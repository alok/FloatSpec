"""Subprocess execution that reports instead of raising (FLOCQSMITH.md §6.5).

``flocq_bridge.run`` raises on any stderr text or nonzero exit, which is the
right contract for fixed families. flocqsmith must attribute failures to
individual cases, so it needs a sibling that returns the raw streams, the exit
code and whether the wall-clock timeout fired. The process-group kill mirrors
``flocq_bridge.run``: a prover child must not outlive its timeout.

A module-wide semaphore caps concurrent prover processes (default 2), because
FloatSpec development machines are shared with Lean builds (§13.2).
"""

from __future__ import annotations

from dataclasses import dataclass
import os
from pathlib import Path
import signal
import subprocess
import threading
import time

ROOT = Path(__file__).resolve().parents[2]
HEAVY = threading.BoundedSemaphore(int(os.environ.get("FLOCQSMITH_MAX_PROVERS", "2")))


@dataclass(frozen=True)
class ProcResult:
    command: tuple[str, ...]
    stdout: str
    stderr: str
    returncode: int | None
    timed_out: bool
    seconds: float

    def to_json(self) -> dict[str, object]:
        return {"command": list(self.command), "returncode": self.returncode,
                "timed_out": self.timed_out, "seconds": round(self.seconds, 3)}


def resolve(command: list[str]) -> list[str]:
    if command[0] == "lake" and os.environ.get("LEAN_TOOLCHAIN_OVERRIDE"):
        return ["elan", "run", os.environ["LEAN_TOOLCHAIN_OVERRIDE"], *command]
    return command


def run_capture(command: list[str], timeout: float, cwd: Path = ROOT) -> ProcResult:
    command = resolve(command)
    started = time.monotonic()
    with HEAVY:
        with subprocess.Popen(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              start_new_session=(os.name == "posix")) as process:
            timed_out = False
            try:
                stdout, stderr = process.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                _kill_group(process)
                stdout, stderr = process.communicate()
            except BaseException:
                _kill_group(process)
                process.communicate()
                raise
            return ProcResult(tuple(command), stdout or "", stderr or "", process.returncode, timed_out,
                              time.monotonic() - started)


def _kill_group(process: subprocess.Popen[str]) -> None:
    try:
        if os.name == "posix":
            os.killpg(process.pid, signal.SIGKILL)
        else:
            process.kill()
    except ProcessLookupError:
        pass
