import asyncio
import logging
import os
from typing import Dict, List, Any
from mcp.server.fastmcp import FastMCP

try:
    from .agda_repl import AgdaRepl
    from .file_edit import replace_hole, replace_line, Range, outline
except ImportError:  # running as a loose script
    from agda_repl import AgdaRepl
    from file_edit import replace_hole, replace_line, Range, outline

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("agda-mcp")

mcp = FastMCP("Agda MCP")
repl = AgdaRepl()

# State refreshed from every command's responses.
goals_map: Dict[int, Range] = {}
goal_types: Dict[int, str] = {}
last_diagnostics: Dict[str, List[str]] = {"errors": [], "warnings": []}
current_file: str = ""


def update_state(responses: List[Dict[str, Any]]):
    """Refresh goal ranges, goal types, and diagnostics from Agda responses."""
    global goals_map, goal_types, last_diagnostics
    for resp in responses:
        if resp.get("kind") == "InteractionPoints":
            goals_map = {}
            for pt in resp.get("interactionPoints", []):
                if "id" in pt and "range" in pt:
                    goals_map[pt["id"]] = Range.from_json(pt["range"])

        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "AllGoalsWarnings":
                goal_types = {}
                for g in info.get("visibleGoals", []):
                    obj = g.get("constraintObj", {})
                    gid = obj.get("id")
                    if gid is not None:
                        goal_types[gid] = g.get("type", "?")
                        if "range" in obj:
                            goals_map[gid] = Range.from_json(obj["range"])
                last_diagnostics = {
                    "errors": [str(e) for e in info.get("errors", [])],
                    "warnings": [str(w) for w in info.get("warnings", [])],
                }


def _extract_error(obj: Dict[str, Any]) -> str:
    # Agda nests the human-readable text under either "message" or "error".message.
    err = obj.get("error")
    if isinstance(err, dict) and err.get("message"):
        return err["message"]
    return str(obj.get("message") or obj.get("payload") or obj)


def _goals_from(responses: List[Dict[str, Any]]) -> Dict[int, str]:
    """id -> type for every goal in the last AllGoalsWarnings of `responses`."""
    goals: Dict[int, str] = {}
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "AllGoalsWarnings":
                goals = {}
                for g in info.get("visibleGoals", []):
                    gid = g.get("constraintObj", {}).get("id")
                    if gid is not None:
                        goals[gid] = g.get("type", "?")
    return goals


def _error_message(responses: List[Dict[str, Any]]) -> str:
    for resp in responses:
        if resp.get("kind") == "ParseError":
            return f"Malformed command: {resp.get('message')}"
        if resp.get("kind") == "Error":
            return _extract_error(resp)
        info = resp.get("info") if isinstance(resp.get("info"), dict) else None
        if info and info.get("kind") == "Error":
            return _extract_error(info)
    return ""


def handle_edits(file_path: str, responses: List[Dict[str, Any]]) -> List[str]:
    """Apply GiveAction / MakeCase edits to the source file.

    Each edit carries its own goal range, so we apply them bottom-up (later
    positions first) — auto_all can fill several holes at once and editing a
    lower hole must not shift the ranges of holes above it.
    """
    gives = []   # (Range, content, wrap_parens, goal_id)
    cases = []   # (line_num, clauses, goal_id)

    for resp in responses:
        kind = resp.get("kind")
        ip = resp.get("interactionPoint", {})
        ip_id = ip.get("id")

        if kind == "GiveAction":
            rng = Range.from_json(ip["range"]) if "range" in ip else goals_map.get(ip_id)
            if rng is None:
                logger.warning("GiveAction for unknown goal %s", ip_id)
                continue
            result = resp.get("giveResult", {})
            res_kind = result.get("kind") or ("Give_String" if "str" in result else None)
            if res_kind == "Give_Paren":
                gives.append((rng, "", True, ip_id))
            else:
                gives.append((rng, result.get("str", ""), False, ip_id))

        elif kind == "MakeCase":
            rng = Range.from_json(ip["range"]) if "range" in ip else goals_map.get(ip_id)
            if rng is None:
                logger.warning("MakeCase for unknown goal %s", ip_id)
                continue
            cases.append((rng.start_line, resp.get("clauses", []), ip_id))

    edits = []
    # Apply bottom-up so earlier (lower-line/col) edits don't invalidate ranges above.
    for line_num, clauses, gid in sorted(cases, key=lambda c: c[0], reverse=True):
        replace_line(file_path, line_num, clauses)
        edits.append(f"Case split on ?{gid}: {len(clauses)} clauses")
    for rng, content, wrap, gid in sorted(
        gives, key=lambda e: (e[0].start_line, e[0].start_col), reverse=True
    ):
        replace_hole(file_path, rng, content, wrap_parens=wrap)
        edits.append(
            f"Wrapped ?{gid} in parens" if wrap else f"Filled ?{gid} with '{content}'"
        )
    return edits


def _require_file() -> str:
    return "" if current_file else "No file loaded. Use agda_load first."


@mcp.tool()
async def agda_load(file: str) -> str:
    """Load and type-check an Agda file."""
    global current_file
    current_file = file
    responses = await repl.load_file(file)
    update_state(responses)
    err = _error_message(responses)
    if err:
        return f"Error loading file: {err}"
    out = [f"Loaded {file}. {len(goals_map)} goal(s)."]
    if last_diagnostics["warnings"]:
        out.append(f"{len(last_diagnostics['warnings'])} warning(s).")
    return " ".join(out)


@mcp.tool()
async def agda_get_goals() -> str:
    """List all goals/holes with their expected types and any warnings."""
    if msg := _require_file():
        return msg
    responses = await repl.get_goals(current_file)
    update_state(responses)
    if not goal_types and not goals_map:
        return "No goals found."
    lines = []
    for gid in sorted(set(goal_types) | set(goals_map)):
        typ = goal_types.get(gid, "?")
        loc = f"  [{goals_map[gid]}]" if gid in goals_map else ""
        lines.append(f"?{gid} : {typ}{loc}")
    if last_diagnostics["warnings"]:
        lines.append("\nWarnings:")
        lines.extend(f"  {w}" for w in last_diagnostics["warnings"])
    return "\n".join(lines)


@mcp.tool()
async def agda_get_goal_type(goalId: int) -> str:
    """Get the type expected at a specific goal."""
    if msg := _require_file():
        return msg
    responses = await repl.goal_type(current_file, goalId)
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "GoalSpecific":
                type_str = info.get("typeAux", {}).get("expr", "") or info.get("type", "")
                return f"?{goalId} : {type_str}"
    err = _error_message(responses)
    return f"Error: {err}" if err else "Could not determine goal type."


@mcp.tool()
async def agda_get_context(goalId: int) -> str:
    """Get the context (available variables) at a specific goal."""
    if msg := _require_file():
        return msg
    responses = await repl.context(current_file, goalId)
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "GoalSpecific":
                out = ["Context:"]
                for e in info.get("entries", []):
                    out.append(f"  {e.get('reifiedName', '?')} : {e.get('type', '?')}")
                return "\n".join(out)
    err = _error_message(responses)
    return f"Error: {err}" if err else "Could not retrieve context."


@mcp.tool()
async def agda_give(goalId: int, expression: str) -> str:
    """Fill a goal with an expression. Automatically edits the file."""
    if msg := _require_file():
        return msg
    responses = await repl.give(current_file, goalId, expression)
    update_state(responses)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    err = _error_message(responses)
    return f"Error: {err}" if err else "Command executed, but no file edits triggered."


@mcp.tool()
async def agda_refine(goalId: int, expression: str) -> str:
    """Refine a goal with a constructor or function. Automatically edits the file."""
    if msg := _require_file():
        return msg
    responses = await repl.refine(current_file, goalId, expression)
    update_state(responses)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    err = _error_message(responses)
    return f"Error: {err}" if err else "Refinement completed (no edits)."


@mcp.tool()
async def agda_case_split(goalId: int, variable: str) -> str:
    """Split a goal by pattern matching on a variable. Automatically edits the file."""
    if msg := _require_file():
        return msg
    responses = await repl.case_split(current_file, goalId, variable)
    update_state(responses)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    err = _error_message(responses)
    return f"Error: {err}" if err else "Case split completed."


@mcp.tool()
async def agda_auto(goalId: int, hints: str = "") -> str:
    """Search for a term that solves a goal (Agsy). Fills the hole if found.

    Optional `hints` is a space-separated list of names to use in the search.
    """
    if msg := _require_file():
        return msg
    responses = await repl.auto_one(current_file, goalId, hints)
    update_state(responses)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    err = _error_message(responses)
    return f"Error: {err}" if err else f"No solution found for ?{goalId}."


@mcp.tool()
async def agda_auto_all() -> str:
    """Run proof search (Agsy) on every open goal; fills each one it can solve."""
    if msg := _require_file():
        return msg
    responses = await repl.auto_all(current_file)
    update_state(responses)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    err = _error_message(responses)
    return f"Error: {err}" if err else "No goals solved."


@mcp.tool()
async def agda_intro(goalId: int) -> str:
    """Introduce variables/constructors for a goal (e.g. a lambda for a function type)."""
    if msg := _require_file():
        return msg
    responses = await repl.intro(current_file, goalId)
    update_state(responses)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    err = _error_message(responses)
    return f"Error: {err}" if err else f"Nothing to introduce at ?{goalId}."


@mcp.tool()
async def agda_compute(goalId: int, expression: str) -> str:
    """Normalize and display an expression."""
    if msg := _require_file():
        return msg
    responses = await repl.compute(current_file, goalId, expression)
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "NormalForm":
                return info.get("expr", "")
    err = _error_message(responses)
    return f"Error: {err}" if err else "No result."


@mcp.tool()
async def agda_infer_type(goalId: int, expression: str) -> str:
    """Infer the type of an expression."""
    if msg := _require_file():
        return msg
    responses = await repl.infer_type(current_file, goalId, expression)
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "InferredType":
                return info.get("expr", "")
    err = _error_message(responses)
    return f"Error: {err}" if err else "No result."


@mcp.tool()
async def agda_why_in_scope(name: str) -> str:
    """Look up scope information for a name."""
    if msg := _require_file():
        return msg
    responses = await repl.why_in_scope(current_file, name)
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if "text" in info:
                return info["text"]
            if "message" in info:
                return info["message"]
    err = _error_message(responses)
    return f"Error: {err}" if err else "No scope info found."


@mcp.tool()
async def agda_outline(file: str = "") -> str:
    """Token-cheap skeleton of a file: top-level signatures and data/record/module
    headers, without bodies. Defaults to the currently loaded file."""
    path = file or current_file
    if not path:
        return "No file specified and no file loaded."
    try:
        entries = outline(path)
    except OSError as e:
        return f"Error reading {path}: {e}"
    return "\n".join(entries) if entries else "No top-level declarations found."


_scratch_counter = 0


@mcp.tool()
async def agda_run_code(code: str) -> str:
    """Type-check a standalone Agda snippet in an ephemeral module and return the
    result ("OK" or Agda's errors/warnings). A `module ... where` header is added
    automatically — provide only declarations. Runs in the loaded file's directory
    so the project's imports resolve."""
    global _scratch_counter
    _scratch_counter += 1
    workdir = os.path.dirname(current_file) if current_file else os.getcwd()
    # No underscores: Agda splits names on `_` and a bare-digit part is invalid.
    mod = f"McpScratch{os.getpid()}c{_scratch_counter}"
    fname = os.path.join(workdir, mod + ".agda")
    # ponytail: always wrap; a snippet's own `module X where` becomes a valid submodule.
    with open(fname, "w", encoding="utf-8") as f:
        f.write(f"module {mod} where\n\n{code}\n")
    try:
        proc = await asyncio.create_subprocess_exec(
            "agda", fname, cwd=workdir,
            stdout=asyncio.subprocess.PIPE, stderr=asyncio.subprocess.PIPE,
        )
        out, err = await proc.communicate()
        msg = (out.decode() + err.decode()).strip()
        if proc.returncode == 0:
            return f"OK{chr(10) + msg if msg else ''}"
        return msg or f"agda exited with code {proc.returncode}"
    finally:
        for ext in (".agda", ".agdai"):
            try:
                os.remove(os.path.join(workdir, mod + ext))
            except OSError:
                pass


@mcp.tool()
async def agda_try(goalId: int, candidates: List[str], refine: bool = False) -> str:
    """Test candidate expressions in a goal WITHOUT editing the file. For each
    candidate, reports whether it type-checks and, if so, the sub-goals it leaves
    behind (the holes' types) or whether it fully solves the goal.

    Set refine=True to use refinement (Agda inserts holes for missing arguments,
    e.g. `suc` -> `suc ?`) instead of giving the expression verbatim. Useful for
    speculatively probing fills before committing one with agda_give/agda_refine.
    """
    if msg := _require_file():
        return msg
    attempt = repl.refine if refine else repl.give
    baseline = set(_goals_from(await repl.get_goals(current_file)))
    out = []
    mutated = False
    for cand in candidates:
        responses = await attempt(current_file, goalId, cand)
        err = _error_message(responses)
        accepted = any(r.get("kind") == "GiveAction" for r in responses) and not err
        if not accepted:
            # A rejected give/refine leaves the goal intact — no reload needed.
            out.append(f"✗ {cand}  — {(err or 'no result').splitlines()[0]}")
            continue
        # New sub-goals are the ids not present before this attempt.
        after = _goals_from(responses)
        new_types = [after[i] for i in sorted(after) if i not in baseline]
        if new_types:
            out.append(f"✓ {cand}  → leaves {len(new_types)} hole(s): " + ", ".join(new_types))
        else:
            out.append(f"✓ {cand}  → solves goal")
        # The attempt consumed/changed goals in-session; reload (file untouched)
        # to restore the baseline state for the next candidate.
        await repl.load_file(current_file)
        mutated = True
    if mutated:
        update_state(await repl.load_file(current_file))
    return "\n".join(out)


def main():
    mcp.run()


if __name__ == "__main__":
    main()
