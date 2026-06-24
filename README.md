# Agda MCP server (Python)

A Python implementation of the [Model Context Protocol (MCP)](https://modelcontextprotocol.io/) server for Agda. This server enables AI assistants to interact with Agda for proof development and code exploration.

## Features

The server wraps `agda --interaction-json` to maintain a persistent REPL session. It supports standard interaction commands including load, give, refine, case split, proof search (`agda_auto` / `agda_auto_all`, via Agsy), and `agda_intro`. `agda_get_goals` lists every goal with its expected type and any warnings in a single call. `agda_try` speculatively tests candidate expressions in a goal without editing the file, `agda_outline` returns a token-cheap declaration skeleton, and `agda_run_code` type-checks a standalone snippet. When using `agda_give`, `agda_refine`, `agda_case_split`, `agda_auto`, `agda_auto_all`, or `agda_intro`, the server automatically applies the resulting edits to the source file. It uses the `IOTCM` JSON protocol variations found in Agda 2.8+.

## Prerequisites

- **Python 3.10+**
- **Agda**: The `agda` executable must be in your PATH (recommended 2.6.4+).
- **uv** (optional)

## Installation and usage

### Zero-install (recommended)

Run the server directly from the GitHub repository using `uv`.

Add this to your MCP settings file (e.g., `~/.config/claude-code/mcp.json`):

```json
{
  "mcpServers": {
    "agda-mcp-py": {
      "command": "uvx",
      "args": [
        "--from",
        "git+https://github.com/pe200012/agda-mcp",
        "agda-mcp-py"
      ]
    }
  }
}
```

### Local development

1. Clone the repository:
   ```bash
   git clone https://github.com/pe200012/agda-mcp
   cd agda-mcp
   ```

2. Install dependencies:
   ```bash
   uv sync
   ```

3. Run the server:
   ```bash
   uv run agda-mcp-py
   ```

## Available tools

### Session management
- **`agda_load(file: str)`**: Load and type-check an Agda file. Must be called first.

### Inspection
- **`agda_get_goals()`**: List all open goals in the loaded file.
- **`agda_get_goal_type(goalId: int)`**: Return the expected type for a goal.
- **`agda_get_context(goalId: int)`**: List variables in scope at a goal.
- **`agda_compute(goalId: int, expression: str)`**: Normalize an expression in the goal context.
- **`agda_infer_type(goalId: int, expression: str)`**: Infer the type of an expression.
- **`agda_why_in_scope(name: str)`**: Check the scope and definition of a name.

### Interaction
- **`agda_give(goalId: int, expression: str)`**: Fill a hole with an expression and update the file.
- **`agda_refine(goalId: int, expression: str)`**: Refine a hole with a constructor and update the file.
- **`agda_case_split(goalId: int, variable: str)`**: Perform a case split and update the file.

## Technical details

The server uses `mcp.server.fastmcp` for the protocol implementation. A custom `AgdaRepl` class handles `subprocess` communication with `agda --interaction-json`, managing the `Indirect` highlighting mode protocol. The `file_edit` module applies changes returned by Agda directly to the source file using the line/column ranges provided by interaction points.

## Development

Run the implementation test suite:
```bash
uv run test_impl.py
```
