"""Materialize an immutable P3.4 source commit in a fresh owned cloud checkout.

This launcher is authored locally and uploaded verbatim. It never changes an
existing project or cache. Every outcome retains its actual logs and receipt.
"""
from __future__ import annotations

import argparse
import base64
import hashlib
import io
import json
import os
from pathlib import Path
import subprocess
import sys
import traceback
import zipfile

REPOSITORY = "https://github.com/UyNewNas/goldbach-formalization.git"
DOCS = "docs/part3-distribution/p34-classical-support-20261127"
REQUIRED = [
    ".gitignore", "lean-toolchain", "lake-manifest.json", "lakefile.toml",
    "verification/verify_p34_classical_support.py",
    "verification/P34ClassicalSupportAudit.lean",
    "verification/P34ClassicalSupportBoundary.lean",
    "verification/P34FrickePhaseAudit.lean",
    "verification/test_p34_classical_support_gate.py",
    "verification/verify_p34_cusp_normalization.py",
    "verification/verify_variable_envelope_boxes.py",
    "verification/test_p34_import_scope.py",
    "verification/run_p34_classical_support_cloud.py",
    DOCS + "/SOURCE_INTAKE.json", DOCS + "/PROJECT_SOURCE_CLOSURE.json",
    DOCS + "/verification-attempts/proof-expression-failure-r2.zip",
]


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", required=True)
    parser.add_argument("--tree", required=True)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--receipt-dir", type=Path, required=True)
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--package-root", type=Path, required=True)
    parser.add_argument("--reuse-r2-root", type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    receipts = args.receipt_dir.resolve()
    for path in (root, receipts):
        if not path.is_relative_to(Path("/workspace")) or "p34-classical" not in path.name:
            raise RuntimeError("Expected an owned P3.4 directory within /workspace")
        if path.exists():
            raise RuntimeError("Fresh owned directory already exists: " + str(path))
    receipts.mkdir(parents=True)
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    env["PATH"] = str(args.toolchain_root / "bin") + ":" + env.get("PATH", "")
    output = root / ".lake/p34-classical-support-verification"
    provenance = {"status": "STARTING", "source": args.source, "tree": args.tree,
                  "root": str(root), "launcher_sha256": sha256(Path(__file__).read_bytes()),
                  "repository": REPOSITORY}

    def checked(argv: list[str], name: str, *, cwd: Path | None = None,
                input_text: str | None = None) -> str:
        result = subprocess.run(argv, cwd=cwd, env=env, input=input_text,
                                capture_output=True, text=True)
        (receipts / (name + ".log")).write_text(
            "command=" + json.dumps(argv) + "\n" + result.stdout + result.stderr)
        if result.returncode:
            raise RuntimeError(name + " failed, exit " + str(result.returncode))
        return result.stdout.strip()

    exit_code = 1
    try:
        checked(["git", "init", str(root)], "init")
        checked(["git", "remote", "add", "origin", REPOSITORY], "remote", cwd=root)
        checked(["git", "config", "remote.origin.promisor", "true"], "promisor", cwd=root)
        checked(["git", "config", "remote.origin.partialclonefilter", "blob:none"], "filter", cwd=root)
        checked(["git", "fetch", "--depth=16",
                 "--filter=blob:none", "--no-tags", "origin", args.source], "fetch", cwd=root)
        observed_tree = checked(["git", "rev-parse", args.source + "^{tree}"], "tree", cwd=root)
        if observed_tree != args.tree:
            raise RuntimeError("Immutable source tree mismatch")
        closure = json.loads(checked(["git", "show", args.source + ":" + DOCS +
                                      "/PROJECT_SOURCE_CLOSURE.json"], "closure", cwd=root))
        paths = REQUIRED + [item["path"] for item in closure["project_sources"]]
        if len(paths) != len(set(paths)) or any(
                path.startswith("/") or ".." in Path(path).parts or "\n" in path for path in paths):
            raise RuntimeError("Invalid exact source paths")
        checked(["git", "sparse-checkout", "set", "--no-cone", "--stdin"], "sparse",
                cwd=root, input_text="".join("/" + path + "\n" for path in paths))
        checked(["git", "checkout", "--detach", args.source], "checkout", cwd=root)
        if any(not (root / path).is_file() for path in paths):
            raise RuntimeError("Required committed file is missing")
        if (root / "verification/run_p34_classical_support_cloud.py").read_bytes() != Path(__file__).read_bytes():
            raise RuntimeError("Uploaded launcher differs from committed launcher")
        provenance["sparse_paths"] = paths
        provenance["initial_head"] = checked(["git", "rev-parse", "HEAD"], "initial-head", cwd=root)
        provenance["initial_status"] = checked(
            ["git", "status", "--porcelain", "--untracked-files=all"], "initial-status", cwd=root)
        if provenance["initial_head"] != args.source or provenance["initial_status"]:
            raise RuntimeError("Initial source checkout is not clean and exact")
        command = [sys.executable, "-B", "verification/verify_p34_classical_support.py",
                   "--expected-head", args.source, "--output-dir", str(output),
                   "--toolchain-root", str(args.toolchain_root),
                   "--package-root", str(args.package_root)]
        if args.reuse_r2_root is not None:
            command += ["--reuse-r2-root", str(args.reuse_r2_root)]
        provenance["command"] = command
        print("P34_CLASSICAL_START " + args.source, flush=True)
        with (receipts / "full-stdout.log").open("w") as handle:
            process = subprocess.Popen(command, cwd=root, env=env, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True)
            assert process.stdout is not None
            for line in process.stdout:
                handle.write(line)
                handle.flush()
                print(line, end="", flush=True)
            exit_code = process.wait()
        provenance["gate_exit_code"] = exit_code
        provenance["final_head"] = checked(["git", "rev-parse", "HEAD"], "final-head", cwd=root)
        provenance["final_tree"] = checked(["git", "rev-parse", "HEAD^{tree}"], "final-tree", cwd=root)
        provenance["final_status"] = checked(
            ["git", "status", "--porcelain", "--untracked-files=all"], "final-status", cwd=root)
        if provenance["final_head"] != args.source or provenance["final_tree"] != args.tree or provenance["final_status"]:
            raise RuntimeError("Final source checkout changed")
        provenance["status"] = "PASSED" if exit_code == 0 else "GATE_FAILED"
    except BaseException as error:
        provenance.update(status="FAILED", error=str(error))
        (receipts / "exception.log").write_text(traceback.format_exc())
        print("P34_CLASSICAL_ERROR " + str(error), flush=True)
        exit_code = 1
    finally:
        (receipts / "worktree-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
        members: dict[str, bytes] = {}
        for directory, prefix in ((output, "verification"), (receipts, "provenance")):
            if directory.is_dir():
                for path in sorted(directory.rglob("*")):
                    if path.is_file() and not path.is_symlink():
                        members[prefix + "/" + path.relative_to(directory).as_posix()] = path.read_bytes()
        manifest = {name: {"bytes": len(data), "sha256": sha256(data)}
                    for name, data in members.items()}
        members["ARCHIVE_MEMBERS.json"] = (json.dumps(manifest, indent=2) + "\n").encode()
        payload = io.BytesIO()
        with zipfile.ZipFile(payload, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as archive:
            for name, data in members.items():
                archive.writestr(name, data)
        data = payload.getvalue()
        artifact = receipts.parent / (receipts.name + ".zip")
        if artifact.exists():
            raise RuntimeError("Evidence artifact already exists")
        artifact.write_bytes(data)
        print("P34_CLASSICAL_EVIDENCE " + json.dumps({"path": str(artifact), "bytes": len(data),
              "sha256": sha256(data), "base64": base64.b64encode(data).decode()}), flush=True)
        print("P34_CLASSICAL_EXIT " + str(exit_code), flush=True)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
