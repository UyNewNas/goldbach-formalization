#!/usr/bin/env python3
"""One bounded, strict frontend attempt; never build prerequisite modules.

This is a diagnostic receipt, not a replacement or relaxation of any proof gate.
An incomplete import environment cannot produce an accepted compile, replay, or
axiom audit. Paths are supplied explicitly so that shared caches remain read only.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def parts(path):
    path = Path(path)
    candidates = [path, Path(str(path) + ".server"), Path(str(path) + ".private"),
                  path.with_suffix(".ir"), path.with_suffix(".ir.sig")]
    return {str(p): digest(p) for p in candidates if p.is_file()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    args = parser.parse_args()
    config = json.loads(args.config.read_text())
    source = Path(config["source"])
    output = Path(config["output_object"])
    if source.name != "Part3PrimeAPDistribution.lean":
        raise RuntimeError("This diagnostic is scoped to Part3PrimeAPDistribution")
    if output.exists():
        raise RuntimeError("Refusing to overwrite an existing target object")
    for path, expected in config["tool_and_driver_sha256"].items():
        if digest(path) != expected:
            raise RuntimeError("Tool or driver changed: " + path)
    if digest(source) != config["source_sha256"]:
        raise RuntimeError("Target source changed")
    output.parent.mkdir(parents=True, exist_ok=True)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    command = [str(Path(config["toolroot"]) / "bin/lake"), "-d", config["driver"],
               "-f", "lakefile.lean", "script", "run", "compileOne", str(source),
               config["module"], str(output), "strict"]
    environment = os.environ.copy()
    environment.update(config["environment"])
    environment["PATH"] = str(Path(config["toolroot"]) / "bin") + os.pathsep + environment.get("PATH", "")
    direct_before = {r["module"]: parts(r["object"]) for r in config["direct_imports"]}
    record = {"status": "DIAGNOSTIC_ONLY", "base_commit": config["base_commit"],
              "module": config["module"], "command": command, "cwd": config["repo"],
              "environment": config["environment"], "timeout_seconds": 45,
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "source": str(source), "source_sha256_before": digest(source),
              "output_object": str(output), "target_parts_before": parts(output),
              "direct_import_parts_before": direct_before,
              "config_sha256": digest(args.config), "runner_sha256": digest(__file__),
              "trustLevel_requested": 0, "warningAsError_requested": True,
              "metadata_adapter": False, "prerequisite_builds_started": 0,
              "full_repository_build_started": False,
              "expected_missing_import_count": config["missing_import_count"]}
    log = args.output_dir / "strict-compile.log"
    print("START single strict import diagnostic", flush=True)
    started = time.monotonic()
    with log.open("w") as stream:
        try:
            result = subprocess.run(command, cwd=config["repo"], env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT, timeout=45)
            record["returncode"] = result.returncode
            record["timed_out"] = False
        except subprocess.TimeoutExpired:
            record["returncode"] = None
            record["timed_out"] = True
    record.update(elapsed_seconds=round(time.monotonic() - started, 3),
                  source_sha256_after=digest(source), target_parts_after=parts(output),
                  direct_import_parts_after={r["module"]: parts(r["object"]) for r in config["direct_imports"]},
                  tool_and_driver_sha256_after={p: digest(p) for p in config["tool_and_driver_sha256"]},
                  log_sha256=digest(log))
    text = log.read_text()
    record["frontend_started"] = "FRONTEND_START module=" + config["module"] + " trustLevel=0 strict=strict" in text
    record["frontend_success_marker"] = "FRONTEND_OK module=" + config["module"] + " trustLevel=0" in text
    record["source_unchanged"] = record["source_sha256_before"] == record["source_sha256_after"]
    record["direct_import_parts_unchanged"] = direct_before == record["direct_import_parts_after"]
    record["tools_and_driver_unchanged"] = config["tool_and_driver_sha256"] == record["tool_and_driver_sha256_after"]
    # This diagnostic cannot authorize any proof gate, even on an unexpected success.
    record["strict_compile_accepted"] = False
    record["kernel_replay"] = {"executed": False, "accepted": False}
    record["transitive_axiom_audit"] = {"executed": False, "accepted": False}
    (args.output_dir / "strict-compile-receipt.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: record[k] for k in ["returncode", "timed_out", "elapsed_seconds", "frontend_started", "frontend_success_marker", "source_unchanged", "direct_import_parts_unchanged", "tools_and_driver_unchanged"]}), flush=True)
    print(text, flush=True)
    return record["returncode"] if record["returncode"] is not None else 124


if __name__ == "__main__":
    raise SystemExit(main())
