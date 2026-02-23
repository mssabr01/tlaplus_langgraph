"""Wrappers around TLA+ command-line tools (SANY, PlusCal translator, TLC).

Expects tla2tools.jar to be available via the CLASSPATH env var or at
/opt/tla/tla2tools.jar (set up by the Dockerfile).
"""

import os
import subprocess
import tempfile
from typing import Tuple

TLA_JAR = os.environ.get("TLA_JAR", "/opt/tla/tla2tools.jar")

# Timeout for TLC model checking (seconds)
TLC_TIMEOUT = int(os.environ.get("TLC_TIMEOUT", "300"))


def _write_temp_spec(spec: str, cfg: str | None = None) -> Tuple[str, str | None]:
    """Write spec (and optional cfg) to a temp directory.

    Returns (spec_path, cfg_path_or_none).
    TLA+ tools require files to be on disk with matching names.
    """
    tmpdir = tempfile.mkdtemp(prefix="tla_")
    spec_path = os.path.join(tmpdir, "Spec.tla")
    with open(spec_path, "w") as f:
        f.write(spec)

    cfg_path = None
    if cfg:
        cfg_path = os.path.join(tmpdir, "Spec.cfg")
        with open(cfg_path, "w") as f:
            f.write(cfg)

    return spec_path, cfg_path


def _run_java(main_class: str, args: list[str], timeout: int = 60) -> Tuple[bool, str]:
    """Run a TLA+ Java tool and return (success, output)."""
    cmd = ["java", "-cp", TLA_JAR, main_class] + args
    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        output = result.stdout + result.stderr
        success = result.returncode == 0
        return success, output.strip()
    except subprocess.TimeoutExpired:
        return False, f"Timeout after {timeout}s"
    except FileNotFoundError:
        return False, "Java not found. Is JRE installed?"


def parse_spec(spec: str) -> Tuple[bool, str]:
    """Run SANY parser on a TLA+ specification.

    Args:
        spec: Complete TLA+ module content as a string.

    Returns:
        (success, output) where output is SANY's stdout/stderr.
    """
    spec_path, _ = _write_temp_spec(spec)
    return _run_java("tla2sany.SANY", [spec_path])


def translate_pluscal(spec: str) -> Tuple[bool, str]:
    """Run the PlusCal translator on a TLA+ module containing a PlusCal algorithm.

    Args:
        spec: TLA+ module content with embedded PlusCal algorithm.

    Returns:
        (success, translated_spec) where translated_spec is the full module
        content after PlusCal translation (the .tla file is modified in-place
        by the translator, so we re-read it).
    """
    spec_path, _ = _write_temp_spec(spec)
    success, output = _run_java("pcal.trans", [spec_path])

    if success:
        # PlusCal translator modifies the file in-place
        with open(spec_path) as f:
            translated = f.read()
        return True, translated

    return False, output


def run_tlc(spec: str, cfg: str | None = None) -> Tuple[bool, str]:
    """Run TLC model checker on a TLA+ specification.

    Args:
        spec: Complete TLA+ module content (post-translation if PlusCal).
        cfg: Optional .cfg file content. If not provided, TLC uses defaults.

    Returns:
        (success, output) where output is TLC's full stdout/stderr.
        success is True if model checking completed with no errors.
    """
    spec_path, cfg_path = _write_temp_spec(spec, cfg)

    args = [spec_path]
    if cfg_path:
        args = ["-config", cfg_path] + args

    # Use -workers auto for parallel checking, -cleanup to remove state files
    args = ["-workers", "auto", "-cleanup"] + args

    return _run_java("tlc2.TLC", args, timeout=TLC_TIMEOUT)
