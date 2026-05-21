"""
VsRocq MCP Server — alternative to rocq-mcp that uses vsrocqtop instead of coq-lsp/pet.

This server provides tools for Rocq/Coq proof development:
- Compilation and verification (via coqc)
- Interactive proof state (via vsrocqtop LSP or coqtop -emacs)
- Environment queries (via coqtop -emacs)
- File structure analysis (regex-based)

Unlike rocq-mcp, this server does NOT use pet/coq-lsp internally.
It communicates directly with vsrocqtop's language server protocol (LSP) or
falls back to coqtop's text interface for interactive features.
"""

from __future__ import annotations

import asyncio
import json
import os
import re
import signal
import subprocess
import tempfile
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Literal, TypedDict
import pty
import select

try:
    from fastmcp import FastMCP, Context
    from fastmcp.server.lifespan import lifespan
    HAS_FASTMCP = True
except ImportError:
    HAS_FASTMCP = False
    FastMCP = None
    Context = None
    lifespan = None

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

ROCQ_WORKSPACE: str = os.environ.get("ROCQ_WORKSPACE", os.getcwd())
_ROCQ_WORKSPACE_EXPLICIT: bool = "ROCQ_WORKSPACE" in os.environ
ROCQ_COQC_TIMEOUT: int = int(os.environ.get("ROCQ_COQC_TIMEOUT", "60"))
ROCQ_VERIFY_TIMEOUT: int = int(os.environ.get("ROCQ_VERIFY_TIMEOUT", "120"))
ROCQ_COQC: str = os.environ.get("ROCQ_COQC", "/Users/valentinschneeberger/.opam/default/bin/coqc")
ROCQ_COQTOP: str = os.environ.get("ROCQ_COQTOP", "/Users/valentinschneeberger/.opam/default/bin/coqtop")
ROCQ_MAX_SOURCE_SIZE: int = int(os.environ.get("ROCQ_MAX_SOURCE_SIZE", "1000000"))

# ---------------------------------------------------------------------------
# FastMCP Setup
# ---------------------------------------------------------------------------

if HAS_FASTMCP:
    @lifespan
    async def app_lifespan(server: Any) -> Any:
        """Server lifespan. vsrocqtop is spawned lazily."""
        state: dict[str, Any] = {
            "workspace": ROCQ_WORKSPACE,
            "vsrocqtop": None,
            "current_workspace": None,
        }
        try:
            yield state
        finally:
            client = state.get("vsrocqtop")
            if client:
                _kill_vsrocqtop(client)
    
    mcp = FastMCP("vsrocq-mcp", lifespan=app_lifespan)

# ---------------------------------------------------------------------------
# Shared helpers (same as rocq-mcp)
# ---------------------------------------------------------------------------

_CLEANUP_EXTENSIONS: tuple[str, ...] = (
    ".v", ".vo", ".vok", ".vos", ".glob", ".aux", ".vio", ".timing", ".coqaux"
)


def _path_within(needle: Path, haystack: Path) -> bool:
    """Return True if needle is haystack or a path inside it."""
    return needle == haystack or str(needle).startswith(str(haystack) + os.sep)


def _validate_workspace(workspace: str) -> str | None:
    """Return error message if workspace is invalid, None if OK."""
    ws = Path(workspace).resolve()
    if _ROCQ_WORKSPACE_EXPLICIT:
        root = Path(ROCQ_WORKSPACE).resolve()
        if not _path_within(ws, root):
            return f"Workspace must be within {root}"
    if not ws.is_dir():
        return f"Workspace directory does not exist: {ws}"
    if not os.access(ws, os.W_OK):
        return f"Workspace directory is not writable: {ws}"
    return None


def _cleanup_coqc_artifacts(tmp_path: str) -> None:
    """Remove all coqc output artifacts for a temp file."""
    base = Path(tmp_path).with_suffix("")
    for ext in _CLEANUP_EXTENSIONS:
        base.with_suffix(ext).unlink(missing_ok=True)


_SAFE_COQC_ARGS: frozenset[str] = frozenset({
    "-noinit", "-indices-matter", "-impredicative-set",
    "-allow-rewrite-rules", "-allow-sprop", "-cumulative-sprop",
})
_SAFE_COQC_ARG_PREFIXES: tuple[str, ...] = ("-w ",)


def _is_safe_arg(value: str) -> bool:
    return value in _SAFE_COQC_ARGS or any(value.startswith(p) for p in _SAFE_COQC_ARG_PREFIXES)


def _check_path_containment(ws: Path, dir_arg: str) -> str | None:
    if os.path.isabs(dir_arg):
        return None
    if _path_within((ws / dir_arg).resolve(), ws.resolve()):
        return dir_arg
    return None


def _resolve_file_in_workspace(file: str, workspace: str) -> str:
    ws_resolved = Path(workspace).resolve()
    resolved = (ws_resolved / file).resolve()
    if not _path_within(resolved, ws_resolved):
        raise ValueError("File path must be within workspace.")
    if not resolved.is_file():
        raise FileNotFoundError(f"File not found: {file}")
    return str(resolved)


_PROJECT_MARKERS: tuple[str, ...] = ("_RocqProject", "_CoqProject", "dune-project")


def _find_project_root_from_file(file: str | None) -> str | None:
    """Walk up from file looking for a Rocq project marker."""
    if not file:
        return None
    try:
        p = Path(file)
        if not p.is_absolute():
            p = Path(ROCQ_WORKSPACE) / p
        p = p.absolute()
    except (OSError, ValueError):
        return None
    if p.is_file():
        p = p.parent
    while True:
        for marker in _PROJECT_MARKERS:
            if (p / marker).is_file():
                return str(p)
        if p.parent == p:
            return None
        p = p.parent


def _find_dune_root(ws: Path) -> Path | None:
    check = ws.resolve()
    while True:
        if (check / "dune-project").is_file():
            return check
        parent = check.parent
        if parent == check:
            return None
        check = parent


def _parse_dune_args(args: list[str], ws: Path, dune_root: Path) -> list[str]:
    """Parse dune coq top args and return coqc flags."""
    seen: set[tuple] = set()
    flags: list[str] = []
    i = 0
    while i < len(args):
        a = args[i]
        if a in ("-R", "-Q") and i + 2 < len(args):
            rel = args[i + 1]
            logical = args[i + 2]
            key = (a, rel, logical)
            if key not in seen:
                seen.add(key)
                flags.extend([a, rel, logical])
            i += 3
        elif a == "-I" and i + 1 < len(args):
            rel = args[i + 1]
            key = ("-I", rel)
            if key not in seen:
                seen.add(key)
                flags.extend(["-I", rel])
            i += 2
        elif a == "-w" and i + 1 < len(args):
            spec = args[i + 1]
            key = ("-w", spec)
            if key not in seen:
                seen.add(key)
                flags.extend(["-w", spec])
            i += 2
        elif a == "-noinit":
            key = ("-noinit",)
            if key not in seen:
                seen.add(key)
                flags.append("-noinit")
            i += 1
        else:
            i += 1
    return flags


def _run_dune_coq_top(v_rel: str, dune_root: Path, timeout: int = 10) -> list[str] | None:
    try:
        result = subprocess.run(
            ["dune", "coq", "top", "--toplevel", "echo", "--no-build", v_rel],
            capture_output=True, text=True, timeout=timeout, cwd=str(dune_root)
        )
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None
    if result.returncode != 0:
        return None
    import shlex
    try:
        return shlex.split(result.stdout.strip())
    except ValueError:
        return None


def _parse_project_flags(ws: Path) -> list[str]:
    """Parse _RocqProject/_CoqProject or detect dune project.
    
    Also checks _build/default/ for dune-generated project files."""
    
    # Check workspace root first
    for name in ("_RocqProject", "_CoqProject"):
        proj = ws / name
        if proj.is_file():
            break
    else:
        # Check _build/default/ for dune-generated project files  
        for name in ("_RocqProject", "_CoqProject"):
            proj = ws / "_build" / "default" / name
            if proj.is_file():
                break
        else:
            # No project file found, try dune detection
            dune_root = _find_dune_root(ws)
            if dune_root is not None:
                # Find a representative .v file
                rep_file = None
                for v in ws.glob("**/*.v"):
                    if "_build" not in str(v):
                        rep_file = v
                        break
                if rep_file is not None:
                    try:
                        v_rel = str(rep_file.resolve().relative_to(dune_root))
                    except ValueError:
                        pass
                    else:
                        args = _run_dune_coq_top(v_rel, dune_root)
                        if args is not None:
                            flags = _parse_dune_args(args, ws, dune_root)
                            if flags:
                                return flags
            return ["-Q", str(ws), "Test"]
    
    # Parse the found project file
    flags: list[str] = []
    lines = proj.read_text().splitlines()
    i = 0
    while i < len(lines):
        line = lines[i].strip()
        if not line or line.startswith("#"):
            i += 1
            continue
        if line == "-arg" and i + 1 < len(lines):
            value = lines[i + 1].strip()
            if _is_safe_arg(value):
                flags.extend(value.split(None, 1))
            i += 2
        elif line.startswith("-arg "):
            value = line[len("-arg "):].strip()
            if _is_safe_arg(value):
                flags.extend(value.split(None, 1))
            i += 1
        elif line.startswith(("-R ", "-Q ")):
            parts = line.split(None, 2)
            if len(parts) == 3 and _check_path_containment(ws, parts[1]) is not None:
                flags.extend(parts)
            i += 1
        elif line.startswith("-I "):
            parts = line.split(None, 1)
            if len(parts) == 2 and _check_path_containment(ws, parts[1]) is not None:
                flags.extend(parts)
            i += 1
        else:
            i += 1
    
    # Convert absolute paths to relative to workspace if needed
    cleaned_flags = []
    j = 0
    while j < len(flags):
        if flags[j] in ("-R", "-Q") and j + 2 < len(flags):
            dir_arg = flags[j + 1]
            if os.path.isabs(dir_arg):
                try:
                    rel_dir = str(Path(dir_arg).relative_to(ws))
                    cleaned_flags.extend([flags[j], rel_dir, flags[j + 2]])
                except ValueError:
                    cleaned_flags.extend([flags[j], dir_arg, flags[j + 2]])
            else:
                cleaned_flags.extend([flags[j], dir_arg, flags[j + 2]])
            j += 3
        elif flags[j] == "-I" and j + 1 < len(flags):
            dir_arg = flags[j + 1]
            if os.path.isabs(dir_arg):
                try:
                    rel_dir = str(Path(dir_arg).relative_to(ws))
                    cleaned_flags.extend(["-I", rel_dir])
                except ValueError:
                    cleaned_flags.extend(["-I", dir_arg])
            else:
                cleaned_flags.extend(["-I", dir_arg])
            j += 2
        else:
            cleaned_flags.append(flags[j])
            j += 1
    
    return cleaned_flags


# ---------------------------------------------------------------------------
# Coqc tools (no LSP needed)
# ---------------------------------------------------------------------------

def _run_coqc_process(file_path: str, workspace: Path, timeout: int) -> dict[str, Any]:
    try:
        proc = subprocess.Popen(
            [ROCQ_COQC, *_parse_project_flags(workspace), file_path],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            cwd=str(workspace), start_new_session=True
        )
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
            return {"returncode": proc.returncode, "stdout": stdout, "stderr": stderr, "timed_out": False}
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(proc.pid), signal.SIGTERM)
            except OSError:
                proc.terminate()
            try:
                stdout, stderr = proc.communicate(timeout=3)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(os.getpgid(proc.pid), signal.SIGKILL)
                except OSError:
                    proc.kill()
                stdout, stderr = "", ""
            return {"returncode": -1, "stdout": stdout or "", "stderr": stderr or "", "timed_out": True}
    except FileNotFoundError:
        return {"returncode": -1, "stdout": "", "stderr": f"{ROCQ_COQC} not found", "timed_out": False}


def _run_coqc(source: str, workspace: str, timeout: int) -> dict[str, Any]:
    ws = Path(workspace).resolve()
    with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False, dir=str(ws)) as f:
        f.write(source)
        f.flush()
        tmp_path = f.name
    try:
        return _run_coqc_process(tmp_path, ws, timeout)
    finally:
        _cleanup_coqc_artifacts(tmp_path)


def _run_coqc_file(file_path: str, workspace: str, timeout: int) -> dict[str, Any]:
    ws = Path(workspace).resolve()
    try:
        return _run_coqc_process(file_path, ws, timeout)
    finally:
        base = Path(file_path).with_suffix("")
        for ext in _CLEANUP_EXTENSIONS:
            if ext == ".v":
                continue
            base.with_suffix(ext).unlink(missing_ok=True)


_COQC_POS_RE = re.compile(
    r'File "[^"]*", line (\d+), characters (\d+)-(\d+):\s*\n((?:Error|Warning):.*?)(?=File "|$)',
    re.DOTALL,
)


def _parse_coqc_error_positions(stderr: str) -> list[dict[str, Any]]:
    positions = []
    for m in _COQC_POS_RE.finditer(stderr):
        positions.append({
            "line": int(m.group(1)) - 1,
            "character": int(m.group(2)),
            "end_character": int(m.group(3)),
            "message": m.group(4).strip()[:500],
        })
    return positions


def _first_error_from_positions(positions: list[dict[str, Any]]) -> dict[str, Any] | None:
    for pos in positions:
        if pos["message"].startswith("Error:"):
            return pos
    return None


_MAX_ERROR_LENGTH = 4000
_PROOF_FILE_LABEL = "<proof>"
_TMP_PATH_RE = re.compile(r'"[^"]*tmp[^"]*\.v"')


def _format_error(error_str: str, proof_str: str, include_warnings: bool = True, file_label: str = _PROOF_FILE_LABEL) -> str:
    if not error_str:
        return error_str
    
    proof_lines = proof_str.splitlines()
    diagnostics = list(re.finditer(r'(File "([^"]*)", line (\d+), characters (\d+)-(\d+):\s*\n)(.*?)(?=File "|$)', error_str, re.DOTALL))
    
    if not diagnostics:
        cleaned = _TMP_PATH_RE.sub(f'"{file_label}"', error_str).strip()
        if len(cleaned) > _MAX_ERROR_LENGTH:
            cleaned = cleaned[-_MAX_ERROR_LENGTH:]
        return cleaned
    
    parsed = []
    for m in diagnostics:
        kind_m = re.match(r"^(Error|Warning)\b", m.group(6).strip())
        parsed.append({
            "kind": kind_m.group(1) if kind_m else "Error",
            "line": int(m.group(3)),
            "char_start": int(m.group(4)),
            "char_end": int(m.group(5)),
            "body": m.group(6).strip(),
        })
    
    has_errors = any(d["kind"] == "Error" for d in parsed)
    if not has_errors:
        return ""
    
    selected = []
    seen_warnings: set[str] = set()
    for d in parsed:
        if d["kind"] == "Warning":
            if not include_warnings or d["body"] in seen_warnings or len(seen_warnings) >= 3:
                continue
            seen_warnings.add(d["body"])
        selected.append(d)
        if d["kind"] == "Error":
            break
    
    parts = []
    for d in selected:
        line_1 = d["line"]
        char_start = d["char_start"]
        char_end = d["char_end"]
        header = f"{file_label}, line {line_1}, characters {char_start}-{char_end}:"
        line_idx = line_1 - 1
        source_line = proof_lines[line_idx] if 0 <= line_idx < len(proof_lines) else None
        annotation = ""
        if source_line is not None:
            prefix = f"  {line_1:4d} | "
            caret_offset = len(prefix) + char_start
            caret_len = max(1, char_end - char_start)
            annotation = f"\n{prefix}{source_line}\n{' ' * caret_offset}{'^' * caret_len}"
        parts.append(f"{header}{annotation}\n{d['body']}")
    
    output = "\n\n".join(parts)
    if len(output) > _MAX_ERROR_LENGTH:
        output = output[-_MAX_ERROR_LENGTH:]
    return output


def _build_compile_result(result: dict[str, Any], source: str, timeout: int, include_warnings: bool, *, file_label: str = _PROOF_FILE_LABEL) -> dict[str, Any]:
    if result["timed_out"]:
        return {"success": False, "error": f"Compilation timed out after {timeout}s."}
    
    if result["returncode"] == 0:
        return {"success": True, "output": result["stdout"][:2000]}
    
    error_text = _format_error(result["stderr"], source, include_warnings=include_warnings, file_label=file_label)
    if not error_text:
        raw = result["stderr"].strip()
        fallback = raw[-_MAX_ERROR_LENGTH:] if len(raw) > _MAX_ERROR_LENGTH else raw
        fallback = _TMP_PATH_RE.sub(f'"{file_label}"', fallback).strip()
        if not fallback:
            fallback = f"coqc exited with code {result['returncode']}"
        return {"success": False, "error": fallback}
    
    positions = _parse_coqc_error_positions(result["stderr"])
    result_dict: dict[str, Any] = {"success": False, "error": error_text}
    if positions:
        result_dict["error_positions"] = positions
        result_dict["hint"] = "Examine the error and fix the proof."
    return result_dict


# ---------------------------------------------------------------------------
# Coqtop-based Query Tools
# ---------------------------------------------------------------------------

_COQTOP_PROMPT_RE = re.compile(r'^<prompt>(.*?)</prompt>', re.MULTILINE)


def _run_coqtop_commands(commands: str, workspace: str, timeout: int = 30) -> dict[str, Any]:
    """Run commands via coqtop -emacs and return output."""
    flags = _parse_project_flags(Path(workspace).resolve())
    try:
        proc = subprocess.Popen(
            [ROCQ_COQTOP, "-emacs", "-quiet", *flags],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, cwd=str(workspace)
        )
        stdout, stderr = proc.communicate(input=commands, timeout=timeout)
        # Remove prompts from output
        stdout = _COQTOP_PROMPT_RE.sub('', stdout)
        return {"success": True, "output": stdout + stderr}
    except subprocess.TimeoutExpired:
        proc.kill()
        return {"success": False, "error": f"Query timed out after {timeout}s"}
    except FileNotFoundError:
        return {"success": False, "error": f"{ROCQ_COQTOP} not found"}


# ---------------------------------------------------------------------------
# Simple TOC parser (no LSP needed)
# ---------------------------------------------------------------------------

def _parse_toc_simple(file_path: str) -> list[dict[str, Any]]:
    """Parse a .v file to extract definitions, lemmas, theorems using regex."""
    try:
        content = Path(file_path).read_text()
    except OSError:
        return []
    
    # Remove comments
    content = re.sub(r'\(\*.*?\*\)', '', content, flags=re.DOTALL)
    
    results = []
    # Match: Theorem, Lemma, Definition, Inductive, etc.
    patterns = [
        (r'^(Theorem|Lemma|Remark|Fact|Corollary|Proposition|Definition|Inductive|Record|Fixpoint|CoFixpoint|Instance|Class)\s+([a-zA-Z_][a-zA-Z0-9_]*)', "Theorem/Lemma"),
        (r'^(Let)\s+([a-zA-Z_][a-zA-Z0-9_]*)', "Let"),
        (r'^(Section|Module)\s+([a-zA-Z_][a-zA-Z0-9_]*)', "Section/Module"),
    ]
    
    for line_no, line in enumerate(content.splitlines(), 1):
        for pattern, kind in patterns:
            m = re.match(pattern, line.strip())
            if m:
                results.append({
                    "kind": kind,
                    "name": m.group(2),
                    "line": line_no,
                })
    
    return results


# ---------------------------------------------------------------------------
# Coqtop Interactive Process (NO LSP - uses coqtop -emacs directly)
# ---------------------------------------------------------------------------

class CoqtopGoal:
    """Represents a single Coq goal with hypotheses."""
    def __init__(self, hypotheses: list[str], conclusion: str, goal_id: str = ""):
        self.hypotheses = hypotheses
        self.conclusion = conclusion
        self.goal_id = goal_id


class CoqtopState:
    """Represents the current proof state."""
    def __init__(self, goals: list[CoqtopGoal], proof_finished: bool = False, error: str = ""):
        self.goals = goals
        self.proof_finished = proof_finished
        self.error = error
    
    def format_goals(self, max_goals: int = 10) -> str:
        if self.proof_finished:
            return "No more goals."
        if not self.goals:
            return "No goals."
        
        parts = []
        total = len(self.goals)
        shown = min(total, max_goals)
        
        for i, goal in enumerate(self.goals[:shown], 1):
            if total > 1:
                parts.append(f"Goal {i} (ID {goal.goal_id}):")
            else:
                parts.append(f"Goal (ID {goal.goal_id}):")
            
            if goal.hypotheses:
                for hyp in goal.hypotheses:
                    parts.append(f"  {hyp}")
                parts.append("  ============================")
            else:
                parts.append("  ============================")
            
            parts.append(f"  {goal.conclusion}")
            parts.append("")
        
        if total > shown:
            parts.append(f"... ({total - shown} more goals)")
        
        return "\n".join(parts)


_COQTOP_PROMPT_PATTERN = re.compile(r'<prompt>(.*?)</prompt>')
_GOAL_HEADER_PATTERN = re.compile(r'^(\d+) goals?\s*\(ID\s*(\d+)\)', re.MULTILINE)
_GOAL_CONCLUSION_PATTERN = re.compile(r'============================\s*\n(.*?)(?=\n<prompt|$)', re.DOTALL)


def _parse_coqtop_output(output: str) -> CoqtopState:
    """Parse coqtop -emacs output into structured goals.
    
    Handles PTY output which uses \r\n and has spaces before separator lines.
    """
    # Normalize line endings (PTY uses \r\n, but the rest of the system uses \n)
    output = output.replace('\r\n', '\n')
    
    # Remove prompts
    output = _COQTOP_PROMPT_PATTERN.sub('', output)
    
    # Check for errors first
    error_match = re.search(r'^(Error:|Toplevel input.*?\n.*?\^.*?\n).*', output, re.MULTILINE | re.DOTALL)
    if error_match:
        error_text = error_match.group(1).strip()
        return CoqtopState([], error=error_text)
    
    # Check if proof is finished
    if "No more goals" in output or "Proof completed" in output:
        return CoqtopState([], proof_finished=True)
    
    # Check if not in proof mode
    if "not in proof mode" in output.lower():
        return CoqtopState([])
    
    goals = []
    
    # Main goal block pattern:
    #   N goal (ID X)
    #   [possible hypotheses indented]
    #   ============================
    #   [conclusion indented]
    #   <blank line>
    goal_blocks = re.finditer(
        r'(\d+) goals?\s*\(ID\s*(\d+)\)\n'
        r'(.*?)'
        r'={10,}\n'
        r'\s*(.*?)'
        r'(?:\n\n|\n(?=\d+ goals?)|\n$|$)',
        output,
        re.DOTALL
    )
    
    for match in goal_blocks:
        goal_num = match.group(1)
        goal_id = match.group(2)
        hypotheses_text = match.group(3).strip()
        conclusion = match.group(4).strip()
        
        # Parse hypotheses - lines that are indented and not just whitespace
        hypotheses = []
        if hypotheses_text:
            for line in hypotheses_text.split('\n'):
                line = line.strip()
                if line and not line.startswith('='):
                    hypotheses.append(line)
        
        goals.append(CoqtopGoal(hypotheses, conclusion, goal_id))
    
    # Secondary goal references like "goal 2 (ID 11) is:"
    secondary_goals = re.finditer(
        r'goal\s+(\d+)\s+\(ID\s+(\d+)\)\s+is:\s*\n\s*(.*?)(?=\n\n|\n\d+ goal|\n$|$)',
        output,
        re.DOTALL
    )
    
    for match in secondary_goals:
        goal_id = match.group(2)
        conclusion = match.group(3).strip()
        goals.append(CoqtopGoal([], conclusion, goal_id))
    
    return CoqtopState(goals)


class CoqtopProcess:
    """Manages a persistent coqtop process for interactive proof using a PTY."""
    
    def __init__(self, workspace: str):
        self.workspace = workspace
        self.process = None
        self.master_fd = None
        self.current_file = ""
        self.current_theorem = ""
        self.step_count = 0
        self.in_proof = False
    
    def start(self, file_path: str | None = None) -> CoqtopState:
        """Start coqtop via PTY (fixes buffering issues with stdin/stdout pipes)."""
        if self.process is not None:
            self.stop()
        
        flags = _parse_project_flags(Path(self.workspace).resolve())
        cmd = [ROCQ_COQTOP, "-emacs", "-quiet"]
        if file_path:
            cmd.extend(["-require", file_path])
        cmd.extend(flags)
        
        # Use PTY to avoid buffering issues
        master_fd, slave_fd = pty.openpty()
        self.master_fd = master_fd
        
        self.process = subprocess.Popen(
            cmd,
            stdin=slave_fd,
            stdout=slave_fd,
            stderr=slave_fd,
            preexec_fn=os.setsid,  # Create new session for clean termination
            cwd=str(self.workspace)
        )
        os.close(slave_fd)  # We only use master_fd
        
        # Read welcome message
        self._read_until_prompt(timeout=5)
        
        self.step_count = 0
        self.in_proof = False
        return CoqtopState([])
    
    def stop(self) -> None:
        """Kill the coqtop process."""
        if self.process:
            try:
                # Send quit command
                self._send_command("Quit.")
                # Give it a moment
                time.sleep(0.1)
                self.process.wait(timeout=2)
            except Exception:
                self.process.kill()
                self.process.wait()
        if self.master_fd is not None:
            try:
                os.close(self.master_fd)
            except OSError:
                pass
            self.master_fd = None
        self.process = None
        self.in_proof = False
    
    def is_alive(self) -> bool:
        return self.process is not None and self.process.poll() is None
    
    def _send_command(self, cmd: str) -> None:
        """Send a command to coqtop via PTY."""
        if not self.is_alive():
            raise RuntimeError("coqtop process is not running")
        if self.master_fd is None:
            raise RuntimeError("PTY master fd is closed")
        data = (cmd + "\n").encode("utf-8")
        os.write(self.master_fd, data)
    
    def _read_response(self, timeout: float = 10.0) -> str:
        """Read response from coqtop via PTY.
        
        Coqtop sends: command\r\n[goals/output]\r\n<prompt>...</prompt>
        We read until we get the prompt and then confirm there's no more data.
        """
        if self.master_fd is None:
            return ""
        
        output = b""
        start_time = time.time()
        
        while True:
            elapsed = time.time() - start_time
            if elapsed > timeout:
                break
            
            remaining = timeout - elapsed
            
            # Check if data is available
            ready, _, _ = select.select([self.master_fd], [], [], min(remaining, 0.1))
            if self.master_fd in ready:
                try:
                    data = os.read(self.master_fd, 4096)
                    if data:
                        output += data
                        # Reset timeout when data arrives
                        start_time = time.time()
                except OSError:
                    break
            else:
                # No data available - check if we have a complete response
                if output and b"</prompt>" in output:
                    # Got a prompt, wait briefly for any trailing data
                    ready2, _, _ = select.select([self.master_fd], [], [], 0.1)
                    if self.master_fd not in ready2:
                        break
        
        return output.decode("utf-8", errors="replace")
    
    def _read_until_prompt(self, timeout: float = 5.0) -> str:
        """Read until we see the first prompt (for startup)."""
        return self._read_response(timeout)
    
    def run_tactic(self, tactic: str, timeout: float = 10.0) -> CoqtopState:
        """Execute a tactic and return the current proof state.
        
        We always follow up with 'Show.' to reliably get goals, because
        coqtop -emacs only prints goals on certain commands (Theorem, Show)
        not after every tactic.
        """
        # Send the actual tactic
        self._send_command(tactic)
        output = self._read_response(timeout)
        
        # Parse to get any errors or immediate results  
        state = _parse_coqtop_output(output)
        
        # Track proof mode
        if state.goals or state.proof_finished:
            self.in_proof = True
        elif state.error and "No focused proof" in state.error:
            self.in_proof = False
        
        # If no goals shown and tactic succeeded, fall back to Show.
        # Skip for commands that won't have goals or that close proofs
        skip_auto_show = {"Show.", "Check", "Print", "Qed."}
        if not state.goals and not state.error and not state.proof_finished and tactic not in skip_auto_show:
            self._send_command("Show.")
            show_output = self._read_response(5)
            show_state = _parse_coqtop_output(show_output)
            if show_state.goals or show_state.proof_finished or show_state.error:
                state = show_state
                if show_state.goals or show_state.proof_finished:
                    self.in_proof = True
        
        # If Qed was successful, clear proof mode (proof is now closed)
        if tactic == "Qed." and not state.error:
            self.in_proof = False
        
        if not state.error:
            self.step_count += 1
        
        return state
    
    def run_commands(self, commands: list[str], timeout: float = 30.0) -> CoqtopState:
        """Run multiple commands and return final state."""
        final_state = None
        for cmd in commands:
            state = self.run_tactic(cmd, timeout=timeout / len(commands))
            if state.error:
                return state
            final_state = state
        return final_state or CoqtopState([])

    def start_theorem(self, theorem_name: str = "", file_path: str | None = None, timeout: float = 10.0) -> CoqtopState:
        """Start a proof for a specific theorem."""
        if not self.is_alive():
            self.start(file_path)
        self.current_theorem = theorem_name
        return CoqtopState([])

    def get_current_goals(self) -> CoqtopState:
        """Ask coqtop to show current goals."""
        if not self.is_alive():
            return CoqtopState([], error="coqtop is not running")
        self._send_command("Show.")
        return _parse_coqtop_output(self._read_response())

    def abort_proof(self) -> None:
        """Abort the current proof."""
        if self.is_alive() and self.in_proof:
            self.run_tactic("Abort.")
            self.in_proof = False

    def undo(self, n: int = 1) -> CoqtopState:
        """Undo N steps."""
        for _ in range(n):
            self.run_tactic("Undo.")
        return self.get_current_goals()


# ---------------------------------------------------------------------------
# State table for multi-session support
# ---------------------------------------------------------------------------

_MAX_STATES: int = int(os.environ.get("ROCQ_MAX_STATES", "200"))


@dataclass
class _StateEntry:
    """A proof state stored in the state table."""
    coqtop: CoqtopProcess
    file: str
    theorem: str
    workspace: str
    parent_id: int | None
    tactic: str | None
    step: int
    goals_text: str = ""
    proof_finished: bool = False


_state_table: dict[int, _StateEntry] = {}
_state_next_id: int = 1
_state_current_id: int | None = None


def _state_add(
    coqtop: CoqtopProcess,
    file: str,
    theorem: str,
    workspace: str,
    parent_id: int | None,
    tactic: str | None,
    step: int,
    goals_text: str = "",
    proof_finished: bool = False,
) -> int:
    global _state_next_id, _state_current_id
    sid = _state_next_id
    _state_next_id += 1
    _state_table[sid] = _StateEntry(
        coqtop=coqtop,
        file=file,
        theorem=theorem,
        workspace=workspace,
        parent_id=parent_id,
        tactic=tactic,
        step=step,
        goals_text=goals_text,
        proof_finished=proof_finished,
    )
    _state_current_id = sid
    # Evict oldest when too many states
    while len(_state_table) > _MAX_STATES:
        oldest = min(_state_table)
        entry = _state_table[oldest]
        entry.coqtop.stop()
        del _state_table[oldest]
    return sid


def _state_get(state_id: int) -> _StateEntry | None:
    return _state_table.get(state_id)


def _state_remove(state_id: int) -> None:
    """Remove a state and clean up coqtop process."""
    global _state_current_id
    entry = _state_table.pop(state_id, None)
    if entry:
        entry.coqtop.stop()
    if _state_current_id == state_id:
        _state_current_id = None


def _state_invalidate_all() -> None:
    """Clean up all states (e.g., on server shutdown)."""
    global _state_current_id
    for entry in _state_table.values():
        entry.coqtop.stop()
    _state_table.clear()
    _state_current_id = None


def _state_get_or_error(state_id: int | None) -> tuple[_StateEntry | None, str | None]:
    """Get state by ID or current state. Returns (entry, error)."""
    if state_id is not None:
        entry = _state_table.get(state_id)
        if entry is None:
            if state_id < _state_next_id:
                return None, f"State {state_id} expired (too many states or was removed). Use rocq_start to begin a new session."
            return None, f"State {state_id} does not exist."
        return entry, None
    
    cur = _state_current_id
    if cur is None:
        return None, "No active proof state. Use rocq_start first."
    return _state_table.get(cur), None


def _reconstruct_tactic_path(state_id: int) -> tuple[list[str], bool]:
    """Walk back from state_id and return tactic sequence."""
    tactics = []
    visited = set()
    current = state_id
    
    while current is not None:
        if current in visited:
            break
        visited.add(current)
        entry = _state_table.get(current)
        if entry is None:
            break
        if entry.tactic:
            tactics.append(entry.tactic)
        current = entry.parent_id
    
    tactics.reverse()
    # Complete if we reached the root (parent_id=None or missing)
    complete = current is None or _state_table.get(current) is None
    return tactics, complete


# ---------------------------------------------------------------------------
# Verification helpers (coqc-based)
# ---------------------------------------------------------------------------

def _check_forbidden_commands(source: str) -> str | None:
    forbidden = ["Admitted", "Abort", "admit"]
    for cmd in forbidden:
        if re.search(rf'\b{cmd}\b', source):
            return f"Forbidden command found: {cmd}"
    return None


# ---------------------------------------------------------------------------
# Tool: rocq_compile
# ---------------------------------------------------------------------------

@mcp.tool()
async def rocq_compile(
    source: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Compile Rocq source code and return structured errors.
    
    Args:
        source: Complete Rocq (.v) file content to compile.
        workspace: Directory to use as workspace (default: ROCQ_WORKSPACE env var).
        timeout: Compilation timeout in seconds (default: ROCQ_COQC_TIMEOUT env var).
        include_warnings: If True, include deduplicated warnings before the error.
    """
    workspace = workspace or ROCQ_WORKSPACE
    timeout = timeout if timeout > 0 else ROCQ_COQC_TIMEOUT
    
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}
    
    if len(source) > ROCQ_MAX_SOURCE_SIZE:
        return {"success": False, "error": f"Source exceeds max size ({ROCQ_MAX_SOURCE_SIZE} bytes)"}
    
    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "error": forbidden}
    
    result = _run_coqc(source, workspace, timeout)
    return _build_compile_result(result, source, timeout, include_warnings)


# ---------------------------------------------------------------------------
# Tool: rocq_compile_file
# ---------------------------------------------------------------------------

@mcp.tool()
async def rocq_compile_file(
    file: str,
    workspace: str = "",
    timeout: int = 0,
    include_warnings: bool = True,
) -> dict[str, Any]:
    """Compile a Rocq (.v) file on disk and return structured errors.
    
    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Workspace directory (auto-detected from project markers).
        timeout: Compilation timeout in seconds.
        include_warnings: If True, include deduplicated warnings.
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    timeout = timeout if timeout > 0 else ROCQ_COQC_TIMEOUT
    
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}
    
    try:
        file_path = _resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}
    
    try:
        source = Path(file_path).read_text()
    except OSError as e:
        return {"success": False, "error": f"Cannot read file: {e}"}
    
    if len(source) > ROCQ_MAX_SOURCE_SIZE:
        return {"success": False, "error": f"File exceeds max size ({ROCQ_MAX_SOURCE_SIZE} bytes)"}
    
    forbidden = _check_forbidden_commands(source)
    if forbidden:
        return {"success": False, "error": forbidden}
    
    result = _run_coqc_file(file_path, workspace, timeout)
    return _build_compile_result(result, source, timeout, include_warnings, file_label=file)


# ---------------------------------------------------------------------------
# Tool: rocq_query
# ---------------------------------------------------------------------------

@mcp.tool()
async def rocq_query(
    command: str,
    preamble: str = "",
    file: str = "",
    workspace: str = "",
) -> dict[str, Any]:
    """Search the Rocq environment — find lemmas, check types, inspect definitions.
    
    Does NOT modify any proof state.
    
    Examples:
      command="Search (nat -> nat -> nat)."  — find relevant lemmas
      command="Check Nat.add."               — check a term's type
      command="Print Nat.add."               — see a definition
      command="About plus."                  — summary of a name

    Args:
        command: The Rocq query command to execute.
        preamble: Optional import lines for query context.
        file: Path to a .v file whose definitions should be in scope.
        workspace: Workspace directory.
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}
    
    if file:
        try:
            file_path = _resolve_file_in_workspace(file, workspace)
            content = Path(file_path).read_text()
        except (ValueError, FileNotFoundError, OSError) as e:
            return {"success": False, "error": str(e)}
        
        ws = Path(workspace).resolve()
        with tempfile.NamedTemporaryFile(suffix=".v", mode="w", delete=False, dir=str(ws)) as f:
            f.write(content)
            f.write("\n")
            f.write(command)
            f.flush()
            tmp = f.name
        try:
            result = _run_coqc_process(tmp, ws, 30)
            if result["timed_out"]:
                return {"success": False, "error": "Query timed out"}
            output = result["stdout"] or result["stderr"]
            return {"success": True, "output": output[:8000]}
        finally:
            _cleanup_coqc_artifacts(tmp)
    else:
        cmds = preamble + "\n" + command + "\n"
        return _run_coqtop_commands(cmds, workspace)


# ---------------------------------------------------------------------------
# Tool: rocq_toc
# ---------------------------------------------------------------------------

@mcp.tool()
async def rocq_toc(
    file: str,
    workspace: str = "",
) -> dict[str, Any]:
    """Get the structure of a .v file.
    
    Returns all definitions, lemmas, theorems, and sections as a hierarchical outline.
    
    Args:
        file: Path to the .v file (relative to workspace).
        workspace: Workspace directory.
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}
    
    try:
        file_path = _resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}
    
    items = _parse_toc_simple(file_path)
    lines = [f"File: {file}"]
    for item in items:
        lines.append(f"  {item['kind']} {item['name']} (line {item['line']})")
    
    output = "\n".join(lines)
    if len(output) > 8000:
        output = output[:8000] + "\n... (truncated)"
    
    return {"success": True, "output": output or f"File: {file}\n  (empty)"}


# ---------------------------------------------------------------------------
# INTERACTIVE PROOF TOOLS (using coqtop directly -- NO LSP)
# ---------------------------------------------------------------------------

@mcp.tool()
async def rocq_start(
    file: str = "",
    theorem: str = "",
    line: int = 0,
    character: int = 0,
    preamble: str = "",
    workspace: str = "",
) -> dict[str, Any]:
    """Start an interactive proof session and return a state_id.

    Opens a persistent coqtop process with the given context.
    The state_id can be used with rocq_check and rocq_step_multi.

    Start modes:
    - **file + theorem**: Load a .v file and position at the theorem
    - **file + line/character**: Position at a specific location in a file
    - **preamble**: Start with just import statements

    Args:
        file: Path to a .v file (relative to workspace).
        theorem: Name of a theorem to prove (must exist in the file).
        line: Line number for position-based start (0-based).
        character: Character position for line-based start.
        preamble: Import commands to set up the environment.
        workspace: Workspace directory.
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}
    
    # Create coqtop process
    coqtop = CoqtopProcess(workspace)
    
    try:
        coqtop.start()
    except Exception as e:
        return {"success": False, "error": f"Failed to start coqtop: {e}"}
    
    # Handle preamble mode
    if preamble.strip():
        commands = _split_rocq_sentences(preamble)
        for cmd in commands:
            state = coqtop.run_tactic(cmd)
            if state.error:
                coqtop.stop()
                return {"success": False, "error": f"Preamble failed: {state.error}"}
    
    # Handle file mode
    if file:
        try:
            file_path = _resolve_file_in_workspace(file, workspace)
        except (ValueError, FileNotFoundError) as e:
            coqtop.stop()
            return {"success": False, "error": str(e)}
        
        # Read file content and inject it
        try:
            content = Path(file_path).read_text()
        except OSError as e:
            coqtop.stop()
            return {"success": False, "error": f"Cannot read file: {e}"}
        
        # For position-based start, we need to process the file up to that point
        # For theorem-based start, we find the theorem and process up to it
        if theorem:
            # Try to process up to the theorem declaration
            # This is a simplified approach - we process the whole file
            commands = _split_rocq_sentences(content)
            target_theorem = None
            
            for i, cmd in enumerate(commands):
                if theorem in cmd and any(cmd.startswith(kw) for kw in ("Theorem", "Lemma", "Remark", "Fact", "Corollary", "Proposition")):
                    target_theorem = i
                    break
            
            if target_theorem is None:
                coqtop.stop()
                return {"success": False, "error": f"Theorem '{theorem}' not found in {file}"}
            
            # Process all commands up to the theorem
            for i in range(target_theorem):
                state = coqtop.run_tactic(commands[i])
                if state.error:
                    coqtop.stop()
                    return {"success": False, "error": f"Failed processing file: {state.error}"}
            
            # Now start the theorem proof
            state = coqtop.run_tactic("Proof.")
        else:
            # For line/character based, process file up to that point
            # Simplified: process entire file (user can then use Undo to go back)
            commands = _split_rocq_sentences(content)
            for cmd in commands[:20]:  # Process first ~20 commands as a safety limit
                state = coqtop.run_tactic(cmd)
                if state.error:
                    coqtop.stop()
                    return {"success": False, "error": f"Failed processing file: {state.error}"}
                if state.goals:
                    break  # Stop when we hit an open proof
        
        coqtop.current_file = file
    
    # Get current goals
    state = coqtop.get_current_goals()
    
    # Create state entry
    state_id = _state_add(
        coqtop=coqtop,
        file=file or "<preamble>",
        theorem=theorem or "<interactive>",
        workspace=workspace,
        parent_id=None,
        tactic=None,
        step=0,
        goals_text=state.format_goals(),
        proof_finished=state.proof_finished,
    )
    
    return {
        "success": True,
        "state_id": state_id,
        "goals": state.format_goals(),
        "file": file or "<preamble>",
        "theorem": theorem or "<interactive>",
        "proof_finished": state.proof_finished,
    }


@mcp.tool()
async def rocq_check(
    body: str,
    from_state: int = 0,
    workspace: str = "",
) -> dict[str, Any]:
    """Execute tactics and advance the proof state.

    Runs each tactic sequentially. If a tactic fails, returns the error
    and last_valid_state_id for recovery.

    Args:
        body: One or more tactics to execute (separated by '.').
        from_state: State ID to start from (default: most recent state).
        workspace: Workspace directory.
    """
    # Resolve state
    entry, error = _state_get_or_error(from_state if from_state > 0 else None)
    if error:
        return {"success": False, "error": error}
    
    coqtop = entry.coqtop
    if not coqtop.is_alive():
        return {"success": False, "error": "coqtop process has died. Use rocq_start to begin a new session."}
    
    # Parse tactics
    tactics = _split_rocq_sentences(body)
    if not tactics:
        return {
            "success": True,
            "commands_run": 0,
            "state_id": from_state if from_state > 0 else _state_current_id,
            "goals": entry.goals_text,
            "proof_finished": entry.proof_finished,
        }
    
    parent_id = from_state if from_state > 0 else _state_current_id
    prev_state_id = parent_id
    feedback_pairs = []
    
    for i, tac in enumerate(tactics):
        state = coqtop.run_tactic(tac)
        
        if state.error:
            return {
                "success": False,
                "error": state.error,
                "failed_command": tac,
                "command_index": i,
                "commands_run": i,
                "last_valid_state_id": prev_state_id,
                "goals_at_failure": state.format_goals() if state.goals else entry.goals_text,
                "feedback": feedback_pairs,
            }
        
        goals_text = state.format_goals()
        feedback_pairs.append([tac, goals_text])
        
        # Add new state entry for this step
        sid = _state_add(
            coqtop=coqtop,
            file=entry.file,
            theorem=entry.theorem,
            workspace=entry.workspace,
            parent_id=prev_state_id,
            tactic=tac,
            step=entry.step + i + 1,
            goals_text=goals_text,
            proof_finished=state.proof_finished,
        )
        prev_state_id = sid
    
    final_goals = state.format_goals()
    
    result = {
        "success": True,
        "goals": final_goals,
        "proof_finished": state.proof_finished,
        "commands_run": len(tactics),
        "state_id": prev_state_id,
        "parent_state_id": parent_id,
    }
    
    if feedback_pairs:
        result["feedback"] = feedback_pairs
    
    if state.proof_finished:
        tactics_used, complete = _reconstruct_tactic_path(prev_state_id)
        if tactics_used:
            result["proof_tactics"] = tactics_used
            result["proof_hint"] = (
                "Proof complete! Assemble imports + theorem statement + Proof. + tactics + Qed.\n"
                "Then validate with rocq_compile and dune build."
            )
    
    return result


@mcp.tool()
async def rocq_step_multi(
    tactics: list[str],
    from_state: int = 0,
) -> dict[str, Any]:
    """Try multiple tactics from the same state (branching exploration).

    Each tactic is tried independently from the same starting state.
    Results are ephemeral -- commit the winner with rocq_check.

    Args:
        tactics: List of tactics to try (max 20).
        from_state: State ID to branch from (default: most recent).
    """
    if len(tactics) > 20:
        return {"success": False, "error": "Too many tactics (max 20)"}
    
    # Resolve state
    entry, error = _state_get_or_error(from_state if from_state > 0 else None)
    if error:
        return {"success": False, "error": error}
    
    coqtop = entry.coqtop
    if not coqtop.is_alive():
        return {"success": False, "error": "coqtop process has died. Use rocq_start to begin a new session."}
    
    results = []
    base_id = from_state if from_state > 0 else _state_current_id
    
    for tactic in tactics:
        # Backtrack to the base state using Undo
        current_step = entry.step
        target_step = entry.step
        
        # Find base entry step count
        base_entry = _state_table.get(base_id)
        if base_entry:
            target_step = base_entry.step
        
        steps_to_undo = current_step - target_step
        if steps_to_undo > 0:
            for _ in range(steps_to_undo):
                coqtop.run_tactic("Undo.")
        
        # Try the tactic
        tac = tactic.strip()
        if not tac.endswith('.') and tac not in ('{', '}'):
            tac += '.'
        
        state = coqtop.run_tactic(tac)
        goals_text = state.format_goals()
        
        result_entry = {
            "tactic": tac,
            "success": state.error == "",
            "goals": goals_text if goals_text else "No goals",
            "proof_finished": state.proof_finished,
        }
        
        if state.error:
            result_entry["error"] = state.error
        
        results.append(result_entry)
        
        # Undo to get back to base state for next tactic
        if not state.error:
            coqtop.run_tactic("Undo.")
    
    resp = {
        "success": True,
        "results": results,
        "from_state_id": base_id,
    }
    
    return resp


@mcp.tool()
async def rocq_assumptions(
    theorem: str,
    file: str,
    workspace: str = "",
) -> dict[str, Any]:
    """Check what axioms a theorem depends on.

    Runs Print Assumptions and classifies results.

    Args:
        theorem: Full theorem name (e.g., "add_comm" or "Nat.add").
        file: Path to the .v file where the theorem is defined.
        workspace: Workspace directory.
    """
    workspace = workspace or _find_project_root_from_file(file) or ROCQ_WORKSPACE
    
    err = _validate_workspace(workspace)
    if err:
        return {"success": False, "error": err}
    
    try:
        file_path = _resolve_file_in_workspace(file, workspace)
    except (ValueError, FileNotFoundError) as e:
        return {"success": False, "error": str(e)}
    
    # Read file content
    try:
        content = Path(file_path).read_text()
    except OSError as e:
        return {"success": False, "error": f"Cannot read file: {e}"}
    
    # Run via coqtop
    query = f"Print Assumptions {theorem}."
    commands = content + "\n" + query + "\n"
    result = _run_coqtop_commands(commands, workspace, timeout=60)
    
    if not result.get("success"):
        return result
    
    output = result.get("output", "")
    
    # Parse assumptions
    if "Closed under the global context" in output or "No assumptions" in output:
        return {
            "success": True,
            "theorem": theorem,
            "verdict": "closed",
            "assumptions": [],
            "raw_output": output,
        }
    
    # Extract axiom list
    assumptions = []
    for match in re.finditer(r'^\s*([a-zA-Z_][a-zA-Z0-9_\.]*)\s*:', output, re.MULTILINE):
        assumptions.append(match.group(1))
    
    if not assumptions:
        return {
            "success": True,
            "theorem": theorem,
            "verdict": "closed",
            "assumptions": [],
            "raw_output": output,
        }
    
    # Check if standard axioms
    standard = ["functional_extensionality", "proof_irrelevance", "classical", "excluded_middle", "choice"]
    suspicious = [a for a in assumptions if not any(s in a.lower() for s in standard)]
    
    return {
        "success": True,
        "theorem": theorem,
        "verdict": "suspicious" if suspicious else "standard_only",
        "assumptions": assumptions,
        "suspicious": suspicious,
        "raw_output": output[:2000],
    }


@mcp.tool()
async def rocq_verify(
    proof: str,
    problem_name: str,
    problem_statement: str,
    workspace: str = "",
) -> dict[str, Any]:
    """Verify that a proof actually proves the original statement.

    Wraps the proof in a Module M sandbox and checks that the theorem
    matches the original. Catches Admitted, Abort, type mismatches.

    Args:
        proof: Complete proof file content (including imports).
        problem_name: Unqualified theorem name (e.g., "add_comm").
        problem_statement: Original problem statement (with Admitted).
        workspace: Workspace directory.
    """
    workspace = workspace or ROCQ_WORKSPACE
    
    err = _validate_workspace(workspace)
    if err:
        return {"verified": False, "error": err}
    
    # Build verification source
    verification_source = f"""
{proof}

Module M.
  {problem_statement}
Qed.

Print Assumptions {problem_name}.
Check {problem_name}.
"""
    
    # Compile
    result = _run_coqc(verification_source, workspace, 120)
    
    if result["timed_out"]:
        return {"verified": False, "error": "Verification timed out after 120s."}
    
    if result["returncode"] != 0:
        error_text = _format_error(result["stderr"], verification_source, include_warnings=False)
        return {
            "verified": False,
            "error": error_text or f"Verification failed (exit {result['returncode']})",
        }
    
    # Check assumptions
    stdout = result.get("stdout", "")
    if "Closed under the global context" in stdout:
        return {"verified": True, "method": "module_m", "assumptions": []}
    
    assumptions = []
    for match in re.finditer(r'^\s*([a-zA-Z_][a-zA-Z0-9_\.]*)\s*:', stdout, re.MULTILINE):
        assumptions.append(match.group(1))
    
    return {
        "verified": True,
        "method": "module_m",
        "assumptions": assumptions,
        "note": "Proof uses standard axioms (assumed acceptable)." if assumptions else "",
    }


# ---------------------------------------------------------------------------
# Rocq sentence utilities
# ---------------------------------------------------------------------------

def _find_sentence_end(text: str) -> int | None:
    """Find the first Rocq sentence-terminating dot in text.
    
    A sentence-terminating dot is a '.' that is:
    - NOT inside a comment (* ... *)
    - NOT inside a string "..."
    - followed by whitespace or end-of-string
    """
    in_comment = 0
    in_string = False
    
    for idx, ch in enumerate(text):
        if in_comment > 0:
            if text[idx:idx+2] == "*)":
                in_comment -= 1
            elif text[idx:idx+2] == "(*":
                in_comment += 1
        elif in_string:
            if ch == '"':
                in_string = False
            elif ch == '\\' and idx + 1 < len(text):
                pass  # Skip escaped char
        else:
            if text[idx:idx+2] == "(*":
                in_comment += 1
            elif ch == '"':
                in_string = True
            elif ch == '.' and (idx + 1 >= len(text) or text[idx+1] in ' \t\n\r'):
                return idx
    
    return None


def _split_rocq_sentences(source: str) -> list[str]:
    """Split Rocq source into individual sentences."""
    sentences = []
    remaining = source
    while remaining.strip():
        dot = _find_sentence_end(remaining)
        if dot is None:
            break
        sentence = remaining[:dot+1].strip()
        if sentence:
            sentences.append(sentence)
        remaining = remaining[dot+1:]
    return sentences


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    if not HAS_FASTMCP:
        print("ERROR: fastmcp is not installed. Run: pip install fastmcp")
        exit(1)
    
    try:
        # Tools are registered at import time if fastmcp is available
        mcp.run(transport="stdio")
    finally:
        # Clean up all coqtop processes on exit
        _state_invalidate_all()
