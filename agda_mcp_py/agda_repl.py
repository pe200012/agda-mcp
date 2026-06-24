import asyncio
import json
import logging
import queue
import subprocess
import threading
from typing import Any, Dict, List, Optional, Set

logger = logging.getLogger(__name__)

# Agda --interaction-json emits a burst of JSON responses per command with no
# explicit "done" marker. Empirically (Agda 2.8), every command terminates on a
# known response kind: action commands (load/give/refine/make_case/auto/intro)
# end with `InteractionPoints`; pure queries (metas/goal_type/context/...) end
# with `DisplayInfo`. Errors surface as `DisplayInfo` with info.kind == "Error".
# We wait (up to HARD_TIMEOUT) for that terminal, then briefly drain stragglers —
# instead of the old "sleep out a 1s timeout on every call" heuristic.
TERMINAL_POINTS: Set[str] = {"InteractionPoints"}
TERMINAL_INFO: Set[str] = {"DisplayInfo"}

SETTLE = 0.15  # grace drain after terminal seen
HARD_TIMEOUT = 120.0  # max silence while waiting for terminal (type-checking can be slow)


def _q(s: str) -> str:
    """Quote a string argument for an IOTCM command.

    ensure_ascii=False is essential: Agda identifiers are Unicode (λ Γ Δ → ⊢ …)
    and the interaction parser reads UTF-8 literally — it rejects the \\uXXXX
    escapes that json.dumps emits by default. Quotes/backslashes/newlines are
    still escaped so the argument can't break the command.
    """
    return json.dumps(s, ensure_ascii=False)


def _is_error(data: Dict[str, Any]) -> bool:
    if data.get("kind") == "Error" or data.get("kind") == "ParseError":
        return True
    info = data.get("info")
    return isinstance(info, dict) and info.get("kind") == "Error"


class AgdaRepl:
    def __init__(self):
        self.process: Optional[subprocess.Popen] = None
        self.lock = asyncio.Lock()
        # A single daemon thread drains stdout into this queue. Reading the pipe
        # from one place avoids losing/interleaving lines across commands — the
        # bug you hit by abandoning a blocking readline on every wait_for timeout.
        self._lines: "queue.Queue[str]" = queue.Queue()

    def start(self):
        if self.process is not None and self.process.poll() is None:
            return
        try:
            self.process = subprocess.Popen(
                ["agda", "--interaction-json"],
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                bufsize=1,  # line buffered
            )
        except FileNotFoundError:
            raise RuntimeError(
                "Agda executable not found. Ensure `agda` is installed and in your PATH."
            )
        self._lines = queue.Queue()
        proc = self.process
        t = threading.Thread(target=self._pump, args=(proc,), daemon=True)
        t.start()

    def _pump(self, proc: subprocess.Popen):
        for line in proc.stdout:
            self._lines.put(line)

    def stop(self):
        if self.process:
            self.process.terminate()
            self.process.wait()
            self.process = None

    def _get_line(self, timeout: float) -> Optional[str]:
        try:
            return self._lines.get(timeout=timeout)
        except queue.Empty:
            return None

    async def _interact(
        self, cmd_str: str, terminal: Set[str], hard_timeout: float = HARD_TIMEOUT
    ) -> List[Dict[str, Any]]:
        """Send one IOTCM command and collect its JSON responses.

        Stops once a response whose `kind` is in `terminal` (or any error / parse
        failure) is seen, then drains any immediately-following stragglers.
        """
        self.start()
        if self.process.poll() is not None:  # died since last call
            self.process = None
            self.start()

        loop = asyncio.get_event_loop()
        async with self.lock:
            while not self._lines.empty():  # discard any stragglers from a prior command
                self._lines.get_nowait()
            self.process.stdin.write(cmd_str + "\n")
            self.process.stdin.flush()

            responses: List[Dict[str, Any]] = []
            done = False
            while True:
                if self.process.poll() is not None:
                    logger.error("Agda process died (code %s)", self.process.returncode)
                    break
                # Before the terminal we wait up to hard_timeout (slow type-check);
                # after it we only briefly drain. A silence longer than the timeout
                # ends the read — the hang backstop.
                # ponytail: per-line timeout, not an absolute deadline; fine because
                # Agda streams Status/RunningInfo while busy. Add a wall clock cap if
                # a command is ever found to stall silently.
                timeout = SETTLE if done else hard_timeout
                raw = await loop.run_in_executor(None, self._get_line, timeout)
                if raw is None:  # queue idle for `timeout` seconds
                    break
                line = raw.strip()
                if not line:
                    continue
                if line.startswith("JSON>"):
                    line = line[5:].strip()
                try:
                    data = json.loads(line)
                except json.JSONDecodeError:
                    # e.g. "cannot read: IOTCM ..." — a malformed command.
                    logger.error("Non-JSON from Agda: %s", line)
                    responses.append({"kind": "ParseError", "message": line})
                    done = True
                    continue
                responses.append(data)
                if data.get("kind") in terminal or _is_error(data):
                    done = True
            return responses

    # --- Command builders ---------------------------------------------------
    # All string arguments are JSON-encoded (quoted + escaped) so expressions
    # containing quotes/backslashes/newlines can't break the IOTCM command.

    def _iotcm(self, file_path: str, body: str) -> str:
        return f"IOTCM {_q(file_path)} NonInteractive Indirect ({body})"

    async def load_file(self, file_path: str) -> List[Dict[str, Any]]:
        body = f"Cmd_load {_q(file_path)} []"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_POINTS)

    async def get_goals(self, file_path: str) -> List[Dict[str, Any]]:
        # Cmd_metas returns AllGoalsWarnings (every goal + its type) in one shot.
        return await self._interact(
            self._iotcm(file_path, "Cmd_metas Simplified"), TERMINAL_INFO
        )

    async def give(self, file_path: str, goal_id: int, expr: str) -> List[Dict[str, Any]]:
        body = f"Cmd_give WithoutForce {goal_id} noRange {_q(expr)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_POINTS)

    async def refine(self, file_path: str, goal_id: int, expr: str) -> List[Dict[str, Any]]:
        body = f"Cmd_refine {goal_id} noRange {_q(expr)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_POINTS)

    async def case_split(self, file_path: str, goal_id: int, var: str) -> List[Dict[str, Any]]:
        body = f"Cmd_make_case {goal_id} noRange {_q(var)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_POINTS)

    async def auto_one(self, file_path: str, goal_id: int, hints: str = "") -> List[Dict[str, Any]]:
        # Agda >= 2.7: Cmd_autoOne takes a leading Rewrite (AsIs) argument.
        body = f"Cmd_autoOne AsIs {goal_id} noRange {_q(hints)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_POINTS)

    async def auto_all(self, file_path: str) -> List[Dict[str, Any]]:
        return await self._interact(
            self._iotcm(file_path, "Cmd_autoAll AsIs"), TERMINAL_POINTS
        )

    async def intro(self, file_path: str, goal_id: int) -> List[Dict[str, Any]]:
        body = f"Cmd_intro False {goal_id} noRange {_q('')}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_POINTS)

    async def why_in_scope(self, file_path: str, name: str) -> List[Dict[str, Any]]:
        body = f"Cmd_why_in_scope_toplevel {_q(name)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_INFO)

    async def context(self, file_path: str, goal_id: int) -> List[Dict[str, Any]]:
        body = f"Cmd_context Simplified {goal_id} noRange {_q('')}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_INFO)

    async def goal_type(self, file_path: str, goal_id: int) -> List[Dict[str, Any]]:
        body = f"Cmd_goal_type Simplified {goal_id} noRange {_q('')}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_INFO)

    async def compute(self, file_path: str, goal_id: int, expr: str) -> List[Dict[str, Any]]:
        # ponytail: toplevel compute (ignores goal context); switch to
        # `Cmd_compute DefaultCompute {goal_id} noRange ...` if goal-local needed.
        body = f"Cmd_compute_toplevel DefaultCompute {_q(expr)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_INFO)

    async def infer_type(self, file_path: str, goal_id: int, expr: str) -> List[Dict[str, Any]]:
        body = f"Cmd_infer_toplevel Simplified {_q(expr)}"
        return await self._interact(self._iotcm(file_path, body), TERMINAL_INFO)
