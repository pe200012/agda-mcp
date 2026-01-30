import logging
import asyncio
from typing import Dict, List, Optional, Any
from mcp.server.fastmcp import FastMCP

# Import from local modules
# Since we are running as a script/module, we need to handle imports carefully.
# In a proper package, we use relative imports.
try:
    from .agda_repl import AgdaRepl
    from .file_edit import replace_hole, replace_line, Range
    from .agda_types import (
        AgdaLoad,
        AgdaGetGoals,
        AgdaGetGoalType,
        AgdaGetContext,
        AgdaGive,
        AgdaRefine,
        AgdaCaseSplit,
        AgdaCompute,
        AgdaInferType,
        AgdaIntro,
        AgdaWhyInScope,
        AgdaAuto,
        AgdaAutoAll,
    )
except ImportError:
    # Fallback for running directly if needed
    from agda_repl import AgdaRepl
    from file_edit import replace_hole, replace_line, Range
    from agda_types import (
        AgdaLoad,
        AgdaGetGoals,
        AgdaGetGoalType,
        AgdaGetContext,
        AgdaGive,
        AgdaRefine,
        AgdaCaseSplit,
        AgdaCompute,
        AgdaInferType,
        AgdaIntro,
        AgdaWhyInScope,
        AgdaAuto,
        AgdaAutoAll,
    )

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("agda-mcp")

mcp = FastMCP("Agda MCP")
repl = AgdaRepl()

# State
goals_map: Dict[int, Range] = {}
current_file: str = ""


def update_goals(responses: List[Dict[str, Any]]):
    """
    Parses responses to update the goals_map.
    """
    global goals_map
    for resp in responses:
        if resp.get("kind") == "InteractionPoints":
            points = resp.get("interactionPoints", [])
            for pt in points:
                # pt: {"id": 1, "range": [...]}
                if "id" in pt and "range" in pt:
                    goals_map[pt["id"]] = Range.from_json(pt["range"])

    logger.debug(f"Updated goals map: {len(goals_map)} goals")


def handle_edits(file_path: str, responses: List[Dict[str, Any]]) -> List[str]:
    """
    Parses responses for edit actions and applies them.
    Returns a list of descriptions of what was done.
    """
    edits_performed = []

    for resp in responses:
        kind = resp.get("kind")

        if kind == "GiveAction" or "giveResult" in resp:
            # {"kind": "GiveAction", "interactionPoint": {"id": 1, ...}, "giveResult": {"str": "refl", ...}}
            # Structure varies by Agda version.
            # Agda 2.8:
            # "giveResult": { "kind": "Give_String", "str": "..." } or { "kind": "Give_Paren" }
            # Or simplified: "giveResult": {"str": "x"}

            ip_id = resp.get("interactionPoint", {}).get("id")
            result = resp.get("giveResult", {})
            res_kind = result.get("kind")

            # Fallback for simplified structure
            if res_kind is None and "str" in result:
                res_kind = "Give_String"

            if ip_id is not None and ip_id in goals_map:
                goal_range = goals_map[ip_id]

                if res_kind == "Give_String":
                    content = result.get("str", "")
                    replace_hole(file_path, goal_range, content)
                    edits_performed.append(f"Filled goal ?{ip_id} with '{content}'")
                elif res_kind == "Give_Paren":
                    replace_hole(file_path, goal_range, "", wrap_parens=True)
                    edits_performed.append(f"Wrapped goal ?{ip_id} in parentheses")
            else:
                logger.warning(f"GiveAction for unknown goal {ip_id}")

        elif kind == "MakeCase" or "clauses" in resp:
            # {"kind": "MakeCase", "interactionPoint": {"id": 1, ...}, "clauses": ["...", "..."]}
            ip_id = resp.get("interactionPoint", {}).get("id")
            clauses = resp.get("clauses", [])

            if ip_id is not None and ip_id in goals_map:
                goal_range = goals_map[ip_id]
                # MakeCase replaces the *line* containing the goal.
                # goal_range.start_line is 1-based.
                replace_line(file_path, goal_range.start_line, clauses)
                edits_performed.append(
                    f"Case split on goal ?{ip_id}, generated {len(clauses)} clauses"
                )
            else:
                logger.warning(f"MakeCase for unknown goal {ip_id}")

    return edits_performed


@mcp.tool()
async def agda_load(file: str) -> str:
    """Load and type-check an Agda file."""
    global current_file, goals_map
    current_file = file
    goals_map = {}  # Reset goals

    responses = await repl.load_file(file)
    update_goals(responses)

    # Check for errors
    errors = [r for r in responses if r.get("kind") == "Error"]
    if errors:
        msg = errors[0].get("message", "Unknown error")
        return f"Error loading file: {msg}"

    return f"Loaded {file}. Found {len(goals_map)} goals."


@mcp.tool()
async def agda_get_goals() -> str:
    """List all goals/holes in the currently loaded file."""
    if not current_file:
        return "No file loaded. Please use agda_load first."

    responses = await repl.get_goals()
    update_goals(responses)

    # Format output
    if not goals_map:
        return "No goals found."

    out = []
    for gid, rng in goals_map.items():
        # Ideally we want the type too, but interaction points just gives location.
        # We need to query goal type separately or parsing 'AllGoalsWarnings' if available.
        # But 'agda_get_goals' usually returns a summary.
        # We can try to get types? No, that's expensive (N roundtrips).
        # We'll just list IDs and locations.
        out.append(f"?{gid} at {rng}")

    return "\n".join(out)


@mcp.tool()
async def agda_get_goal_type(goalId: int) -> str:
    """Get the type expected at a specific goal."""
    if not current_file:
        return "No file loaded."

    responses = await repl.goal_type(current_file, goalId)
    # Parse 'GoalSpecific' or 'DisplayInfo' -> 'GoalSpecific'

    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "GoalSpecific":
                # Agda 2.8: { "kind": "GoalSpecific", "interactionPoint": ..., "type": "...", ... }
                # Or sometimes plain text in 'typeAux'?
                type_str = info.get("typeAux", {}).get("expr", "") or info.get(
                    "type", ""
                )
                return f"?{goalId} : {type_str}"

    return "Could not determine goal type."


@mcp.tool()
async def agda_get_context(goalId: int) -> str:
    """Get the context (available variables) at a specific goal."""
    if not current_file:
        return "No file loaded."

    responses = await repl.context(current_file, goalId)

    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "GoalSpecific":
                # entries is a list of {originalName, reifiedName, binding, type}
                entries = info.get("entries", [])
                out = ["Context:"]
                for e in entries:
                    name = e.get("reifiedName", "?")
                    typ = e.get("type", "?")
                    out.append(f"  {name} : {typ}")
                return "\n".join(out)

    return "Could not retrieve context."


@mcp.tool()
async def agda_give(goalId: int, expression: str) -> str:
    """Fill a goal with an expression. Automatically edits the file."""
    if not current_file:
        return "No file loaded."

    responses = await repl.give(current_file, goalId, expression)

    edits = handle_edits(current_file, responses)

    if edits:
        return "\n".join(edits)

    # If no edit, maybe it failed?
    errors = [r for r in responses if r.get("kind") == "Error"]
    if errors:
        return f"Error: {errors[0].get('message')}"

    return "Command executed, but no file edits triggered."


@mcp.tool()
async def agda_refine(goalId: int, expression: str) -> str:
    """Refine a goal with a constructor or function."""
    if not current_file:
        return "No file loaded."

    responses = await repl.refine(current_file, goalId, expression)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    return "Refinement completed (no edits or manual update needed)."


@mcp.tool()
async def agda_case_split(goalId: int, variable: str) -> str:
    """Split a goal by pattern matching on a variable."""
    if not current_file:
        return "No file loaded."

    responses = await repl.case_split(current_file, goalId, variable)
    edits = handle_edits(current_file, responses)
    if edits:
        return "\n".join(edits)
    return "Case split completed."


@mcp.tool()
async def agda_compute(goalId: int, expression: str) -> str:
    """Normalize and display an expression in a goal's context."""
    if not current_file:
        return "No file loaded."

    responses = await repl.compute(current_file, goalId, expression)
    # Search for 'NormalForm' kind or similar info
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "NormalForm":
                return info.get("expr", "")
    return "No result."


@mcp.tool()
async def agda_infer_type(goalId: int, expression: str) -> str:
    """Infer the type of an expression in a goal's context."""
    if not current_file:
        return "No file loaded."

    responses = await repl.infer_type(current_file, goalId, expression)
    # Look for 'InferredType'
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            if info.get("kind") == "InferredType":
                return info.get("expr", "")
    return "No result."


@mcp.tool()
async def agda_why_in_scope(name: str) -> str:
    """Look up documentation and scope information for a name."""
    if not current_file:
        return "No file loaded."

    responses = await repl.why_in_scope(current_file, 0, name)

    # Try to extract meaningful info
    for resp in responses:
        if resp.get("kind") == "DisplayInfo":
            info = resp.get("info", {})
            # Agda often puts the scope info in 'text' or 'message' field of Info_Generic
            if "text" in info:
                return info["text"]
            if "message" in info:
                return info["message"]

    return "No scope info found."


def main():
    mcp.run()


if __name__ == "__main__":
    main()
