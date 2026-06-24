import logging
from typing import Dict, List, Any
from mcp.server.fastmcp import FastMCP

try:
    from .agda_repl import AgdaRepl
    from .file_edit import replace_hole, replace_line, Range
except ImportError:  # running as a loose script
    from agda_repl import AgdaRepl
    from file_edit import replace_hole, replace_line, Range

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


def _error_message(responses: List[Dict[str, Any]]) -> str:
    for resp in responses:
        if resp.get("kind") == "ParseError":
            return f"Malformed command: {resp.get('message')}"
        info = resp.get("info") if isinstance(resp.get("info"), dict) else None
        if resp.get("kind") == "Error":
            return str(resp.get("message", resp))
        if info and info.get("kind") == "Error":
            return str(info.get("message") or info.get("payload") or info)
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


def main():
    mcp.run()


if __name__ == "__main__":
    main()
