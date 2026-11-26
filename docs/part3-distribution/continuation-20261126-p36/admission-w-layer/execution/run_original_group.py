#!/usr/bin/env python3
"""Capture an unchanged original P3.6 group run and its runtime tool binding."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys


def digest(path: Path) -> str:
    with path.open("rb") as handle:
        return hashlib.file_digest(handle, "sha256").hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, required=True)
    parser.add_argument("--source-commit", required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--binding-output", type=Path, required=True)
    parser.add_argument("--log-output", type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve(strict=True)
    manifest = args.manifest.resolve(strict=True)
    toolchain = Path("/workspace/toolchains/lean-4.33.0-rc1-linux")
    packages = Path("/workspace/blue-member-build/.lake/packages")
    expected = {
        str(toolchain / "bin/lean"): "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
        str(toolchain / "bin/leanchecker"): "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
        str(project / "verification/p36/compile_p36_local.py"): "be263af86651402faf9d7c54e243a44f671177717dbfafca0b604bca4fcc5709",
        str(project / "verification/verify_part3_continuation.py"): "9afe49d061639c5d98926185b4e6301e3ff7222e35550839fbfe1a4c785bdcc8",
        str(project / "verification/verify_part3_distribution.py"): "bef3b8ba73736d7a787aaf31fe49cb8017de4f8d7c71ee4220c6c3dbc47607f4",
        str(project / "verification/Part3DistributionAudit.lean"): "45b20653d5510b9639a653913ba39fdc21d402f45342d6dd7d2c51439f01ed93",
    }
    before = {path: digest(Path(path)) for path in expected}
    if before != expected:
        raise RuntimeError("Pinned original runtime tool digest differs")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
    if head != args.source_commit:
        raise RuntimeError("Runtime checkout differs from frozen source commit")
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=project, check=True)
    selected = json.loads(manifest.read_bytes())["sources"]
    owners = [entry["module"] for entry in selected]
    if len(owners) != len(set(owners)) or not owners:
        raise RuntimeError("Owner manifest is empty or repeats an owner")
    for entry in selected:
        relative = entry["module"].replace(".", "/") + ".lean"
        if entry["selected_path"] != relative or digest(project / relative) != entry["selected_sha256"]:
            raise RuntimeError("Frozen owner manifest differs from runtime source")
        blob = subprocess.check_output(["git", "show", head + ":" + relative], cwd=project)
        if hashlib.sha256(blob).hexdigest() != entry["selected_sha256"]:
            raise RuntimeError("Owner source is not bound to the frozen commit")
    manifest_binding = {"path": str(manifest), "sha256": digest(manifest)}
    run_root = project / ".lake/p36-build/runs"
    previous = set(run_root.glob("*/report.json"))
    command = [sys.executable, str(project / "verification/p36/compile_p36_local.py"), *owners,
               "--project", str(project), "--packages-dir", str(packages),
               "--toolchain-dir", str(toolchain), "--build", "--strict-owned", "--verify-owned",
               "--source-manifest", str(manifest), "--timeout", "2400"]
    args.log_output.parent.mkdir(parents=True, exist_ok=True)
    args.binding_output.parent.mkdir(parents=True, exist_ok=True)
    print("P36_GROUP_RUNTIME_BEFORE " + json.dumps({"source_commit": head, "owners": owners,
          "source_manifest": manifest_binding, "runtime_tool_sha256_before": before}), flush=True)
    with args.log_output.open("x") as log:
        proc = subprocess.Popen(command, cwd=project, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True,
                                env={**os.environ, "PYTHONUNBUFFERED": "1"})
        assert proc.stdout is not None
        for line in proc.stdout:
            log.write(line)
            log.flush()
            print(line, end="", flush=True)
        code = proc.wait()
    reports = set(run_root.glob("*/report.json")) - previous
    if len(reports) != 1:
        raise RuntimeError("Expected exactly one new original report")
    report_path = reports.pop()
    report = json.loads(report_path.read_bytes())
    if report["targets"] != owners or report["source_manifest"] != manifest_binding:
        raise RuntimeError("Original report does not match ordered owner manifest")
    if code:
        for stage in report["commands"]:
            if stage["exit_code"]:
                failed = Path(stage["log"])
                print("P36_FAILED_STAGE_LOG " + json.dumps({"path": str(failed),
                      "sha256": digest(failed)}), flush=True)
                print(failed.read_text(), end="", flush=True)
    after = {path: digest(Path(path)) for path in expected}
    binding = {"owners": owners, "source_commit": head, "status": report["status"],
               "exit_code": code, "report": str(report_path), "report_sha256": digest(report_path),
               "source_manifest": manifest_binding, "runtime_tool_sha256_before": before,
               "runtime_tool_sha256_after": after}
    with args.binding_output.open("x") as handle:
        json.dump(binding, handle, indent=2)
        handle.write("\n")
    print("P36_GROUP_RUNTIME_BINDING " + json.dumps({"path": str(args.binding_output.resolve()),
          "sha256": digest(args.binding_output), "binding": binding}), flush=True)
    if before != after or digest(manifest) != manifest_binding["sha256"]:
        raise RuntimeError("Runtime tools or source manifest changed during original run")
    if code == 0 and report["status"] != "VERIFIED_OWNED":
        raise RuntimeError("Original runner did not fully verify the owned group")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
