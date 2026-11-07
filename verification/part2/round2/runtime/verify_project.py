#!/usr/bin/env python3
"""Single-module stock frontend/stock kernel runner; never builds dependencies."""
from pathlib import Path
import datetime
import hashlib
import json
import os
import resource
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
ENV = json.loads((BASE / "project-environment.json").read_text())
TOOLROOT = Path(ENV["LEAN_SYSROOT"])
PROJECT = Path("/workspace/scratch/1334dbd5a747/goldbach-formalization")
OBJECTS = PROJECT / ".lake/build/lib/lean"


def digest(path):
    with Path(path).open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def memory():
    result = {}
    for name in ("memory.max", "memory.current"):
        path = Path("/sys/fs/cgroup") / name
        if path.exists():
            result[name] = path.read_text().strip()
    return result


def snapshot_shared():
    provenance = json.loads((BASE / "recovery-provenance.json").read_text())
    result = {}
    for item in provenance["p2_sources_and_objects"]:
        for key, expected_key in (("p0_source", "same_sha256"),
                                  ("p0_object", "object_sha256")):
            path = item[key]
            actual = digest(path)
            if actual != item[expected_key]:
                raise SystemExit("Pinned shared cache changed: " + path)
            result[path] = actual
    for name, expected in provenance["stock_binaries"].items():
        path = TOOLROOT / "bin" / name
        actual = digest(path)
        if actual != expected:
            raise SystemExit("Pinned stock executable changed: " + str(path))
        result[str(path)] = actual
    return result


def snapshot_local(excluded):
    """Record every small local producer object except the target being rebuilt."""
    return {str(path): digest(path) for path in sorted(OBJECTS.rglob("*.olean*"))
            if path.is_file() and path != excluded}


def run(action, module, source=None):
    if not module or any(not part.isidentifier() for part in module.split(".")):
        raise SystemExit("Expected a dotted Lean module name")
    obj = OBJECTS.joinpath(*module.split(".")).with_suffix(".olean")
    if action == "compile":
        if source is None:
            source = PROJECT.joinpath(*module.split(".")).with_suffix(".lean")
        if not source.is_file():
            raise SystemExit("Explicit existing source file required")
        command = [str(TOOLROOT / "bin/lake"), "-d", str(BASE / "frontend-driver"),
                   "-f", "lakefile.lean", "script", "run", "compileOne",
                   str(source), module, str(obj), "strict"]
    elif action == "replay":
        if not obj.is_file():
            raise SystemExit("Missing local output object: " + str(obj))
        command = [str(TOOLROOT / "bin/leanchecker"), "--verbose", module]
    else:
        raise SystemExit("Action must be compile or replay")
    environment = os.environ.copy()
    environment.update(ENV)
    environment["PATH"] = str(TOOLROOT / "bin") + os.pathsep + environment.get("PATH", "")
    stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
    log = BASE / (stamp + "-" + action + "-" + module + ".log")
    metadata = {"action": action, "module": module, "command": command,
                "started_utc": stamp, "cwd": str(BASE), "environment": ENV,
                "metadata_adapter": False,
                "trustLevel": 0 if action == "compile" else None,
                "warningAsError": action == "compile",
                "source": str(source) if source else None,
                "source_sha256_before": digest(source) if source else None,
                "object": str(obj),
                "object_sha256_before": digest(obj) if obj.exists() else None,
                "shared_sha256_before": snapshot_shared(),
                "local_producer_sha256_before": snapshot_local(obj),
                "memory_before": memory()}
    print("START", action, module, flush=True)
    start = time.monotonic()
    with log.open("w") as stream:
        stream.write(json.dumps(metadata) + "\n")
        stream.flush()
        result = subprocess.run(command, cwd=BASE, env=environment,
                                stdout=stream, stderr=subprocess.STDOUT)
    output = log.read_text()
    metadata.update(returncode=result.returncode,
                    elapsed_seconds=round(time.monotonic() - start, 3),
                    child_maxrss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,
                    source_sha256_after=digest(source) if source else None,
                    object_sha256_after=digest(obj) if obj.exists() else None,
                    shared_sha256_after=snapshot_shared(),
                    local_producer_sha256_after=snapshot_local(obj),
                    memory_after=memory(), log=str(log))
    failures = []
    if result.returncode:
        failures.append("tool_exit_nonzero")
    if metadata["source_sha256_before"] != metadata["source_sha256_after"]:
        failures.append("source_changed")
    if metadata["shared_sha256_before"] != metadata["shared_sha256_after"]:
        failures.append("shared_cache_changed")
    if metadata["local_producer_sha256_before"] != metadata["local_producer_sha256_after"]:
        failures.append("local_producer_objects_changed")
    if action == "compile" and "FRONTEND_OK module=" + module + " trustLevel=0" not in output:
        failures.append("missing_frontend_completion")
    if action == "replay":
        if "replaying " + module not in output:
            failures.append("missing_selected_module_replay")
        if metadata["object_sha256_before"] != metadata["object_sha256_after"]:
            failures.append("replay_object_changed")
    metadata["verification_passed"] = not failures
    metadata["failures"] = failures
    receipt = log.with_suffix(".json")
    receipt.write_text(json.dumps(metadata, indent=2) + "\n")
    print(output.split("\n", 1)[1], end="")
    print(json.dumps({key: metadata[key] for key in
                      ("returncode", "elapsed_seconds", "child_maxrss_kib",
                       "object_sha256_after", "verification_passed", "failures")}))
    print("RECEIPT", receipt, flush=True)
    return 0 if not failures else (result.returncode or 1)


if __name__ == "__main__":
    if len(sys.argv) not in (3, 4):
        raise SystemExit("Usage: verify_project.py compile MODULE [SOURCE] | verify_project.py replay MODULE")
    raise SystemExit(run(sys.argv[1], sys.argv[2],
                         Path(sys.argv[3]).resolve() if len(sys.argv) == 4 else None))
