#!/usr/bin/env python3
"""Wrap the pinned P3.6 exporter for the exact admission and W-layer owner group."""
from __future__ import annotations

import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys

sys.dont_write_bytecode = True
PREVIOUS = Path(__file__).resolve().parent.parent / "normalized-density/export_verified_increment.py"
PINNED_PREVIOUS_SHA256 = "003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5"
SHA256 = re.compile(r"[0-9a-f]{64}")
OWNERS = tuple("ImbalancedChen." + name for name in (
    "P5OriginalU5NativeRootCover",
    "P3OriginalU5FreshFifthSquareSupplier",
    "P3OriginalU5AllSourceSquares",
    "P3OriginalU5AllSignedSquares",
    "P3OriginalU5RootVInputs",
    "P3OriginalU5CoarseRootV",
    "P3OriginalU5RoughEndpoints",
    "P3OriginalU5FullWLayer",
))
RUNTIME_FILES = (
    "verification/p36/compile_p36_local.py",
    "verification/verify_part3_continuation.py",
    "verification/verify_part3_distribution.py",
    "verification/Part3DistributionAudit.lean",
)
GROUP_RECEIPT = "GROUP_RECEIPT.json"
OWNER_MANIFEST = "OWNER_MANIFEST.json"
RUNTIME_BINDING = "GROUP_RUNTIME_BINDING.json"
ROOT_Q_LEGACY_PIN = {
    "module": "ImbalancedChen.P2OriginalU5RootQ",
    "report_path": "/workspace/p36-original-u5-20261125/.lake/p36-build/runs/20261125T151944.477149Z/report.json",
    "runner_sha256": "895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30",
    "report_sha256": "e79ea8a026224372ac58109bf0ccd4c3ded6d4ef447facf25f1c07ab7ca223ac",
    "report_bytes": 13762383,
    "report_status": "FAILED",
    "scope": "Successful RootQ dependency compile stage only",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(data):
    return sha256(data).hexdigest()


def read_pinned(path, expected, label):
    data = path.read_bytes()
    require(digest(data) == expected, label + " SHA-256 differs")
    return data


def load_previous(path=PREVIOUS):
    data = read_pinned(path, PINNED_PREVIOUS_SHA256, "Previous exporter")
    spec = importlib.util.spec_from_file_location("p36_pinned_previous_exporter", path)
    previous = importlib.util.module_from_spec(spec)
    exec(compile(data, str(path), "exec"), previous.__dict__)
    pin = ROOT_Q_LEGACY_PIN
    report = previous.absolute(pin["report_path"])
    require(report not in previous.LEGACY_REPORT_PINS, "RootQ extension would replace an existing legacy report pin")
    previous.LEGACY_REPORT_PINS[report] = (pin["runner_sha256"], pin["report_sha256"])
    return previous


def parse_owner_manifest(data, pinned_sha256):
    require(digest(data) == pinned_sha256, "Owner manifest SHA-256 differs")
    document = json.loads(data)
    require(isinstance(document, dict) and set(document) == {"sources"}, "Invalid owner manifest")
    sources = document["sources"]
    require(isinstance(sources, list) and tuple(s["module"] for s in sources) == OWNERS,
            "Manifest must contain the exact ordered owner group")
    owners = {}
    for source in sources:
        owner = source["module"]
        source_digest = source["selected_sha256"]
        require(set(source) == {"module", "selected_path", "selected_sha256"}
                and source["selected_path"] == owner.replace(".", "/") + ".lean"
                and isinstance(source_digest, str) and SHA256.fullmatch(source_digest),
                "Owner source path or hash differs: " + owner)
        owners[owner] = source_digest
    return owners


def check_runtime_binding(binding, commit, owners, report_path, report_sha, manifest, tools):
    expected = {
        "owners": list(owners), "source_commit": commit, "status": "VERIFIED_OWNED", "exit_code": 0,
        "report": report_path, "report_sha256": report_sha, "source_manifest": manifest,
        "runtime_tool_sha256_before": tools, "runtime_tool_sha256_after": tools,
    }
    require(isinstance(binding, dict) and binding == expected and type(binding["exit_code"]) is int,
            "Group runtime binding differs from the original report, owner order, manifest, or pinned tools")


def runtime_tools(previous, compiler, original_project, originals):
    path = previous.absolute(compiler["path"])
    require(path.name == "lean" and compiler["sha256"] == previous.COMPILER_SHA256,
            "Original group compiler identity differs")
    pins = originals[2].PINNED_VERIFIERS
    return {
        str(path): previous.COMPILER_SHA256,
        str(path.with_name("leanchecker")): previous.CHECKER_SHA256,
        **{str(original_project / relative): pins[relative] for relative in RUNTIME_FILES},
    }


def root_q_legacy_receipt(base):
    pin = ROOT_Q_LEGACY_PIN
    report = PurePosixPath(pin["report_path"])
    observed = base["prior_compile_reports"].get(str(report))
    prefix = "lineage/" + report.parent.name + "/"
    files = {name for name in base["files"] if name.startswith(prefix)}
    if observed is None:
        require(not files, "RootQ dependency lineage differs from its report pin")
    else:
        member = prefix + "report.json"
        expected = {"runner_sha256": pin["runner_sha256"], "report_sha256": pin["report_sha256"],
                    "status": pin["report_status"], "writer_binding": "pinned legacy report", "reused_module_count": 1}
        require(observed == expected and files == {member, prefix + "compile-" + pin["module"] + ".log"}
                and base["files"][member] == {"path": str(report), "sha256": pin["report_sha256"],
                                              "bytes": pin["report_bytes"]},
                "RootQ dependency lineage differs from its report pin")
    return {**pin, "used": observed is not None}


def group_receipt(base_raw, manifest_raw, binding_raw, commit, owners, binding):
    base = json.loads(base_raw)
    selection = base["files"]["SOURCE_SELECTION.json"]
    manifest = {"path": selection["path"], "sha256": digest(manifest_raw)}
    require(
        base["status"] == "VERIFIED_OWNED_EXPORT" and base["whole_p36_closed"] is False
        and tuple(owners) == OWNERS and base["targets"] == list(owners)
        and base["source_commit"] == commit and base["source_sha256"] == owners
        and base["report_path"] == binding["report"]
        and base["report_sha256"] == base["terminal_report_sha256"] == binding["report_sha256"]
        and selection["sha256"] == manifest["sha256"] and selection["bytes"] == len(manifest_raw)
        and manifest == binding["source_manifest"] and json.loads(binding_raw) == binding
        and base["runtime_binding_file"] is None
        and base["independent_runtime_binding"] == {"status": "unknown", "sha256_before_and_after": None},
        "Base receipt group identity differs",
    )
    return {
        "status": "VERIFIED_OWNED_GROUP_EXPORT",
        "whole_p36_closed": False, "currentVerified": False,
        "scope": "Exact ordered admission and W-layer owner group",
        "previous_exporter_sha256": PINNED_PREVIOUS_SHA256,
        "source_commit": commit, "owners": list(owners), "source_sha256": owners,
        "source_manifest": manifest,
        "original_report_path": binding["report"], "original_report_sha256": binding["report_sha256"],
        "runtime_binding_sha256": digest(binding_raw),
        "original_runtime_identity": "Independently pinned before/after original runner wrapper capture",
        "additional_root_q_legacy_report": root_q_legacy_receipt(base),
        "base_receipt_sha256": digest(base_raw),
        "archive_sha256": base["archive_sha256"], "archive_bytes": base["archive_bytes"],
    }


def export(args, project, previous, originals):
    manifest_raw = read_pinned(args.owner_manifest, args.owner_manifest_sha256, "Owner manifest")
    owners = parse_owner_manifest(manifest_raw, args.owner_manifest_sha256)
    report_path = args.report.resolve(strict=True)
    report = json.loads(read_pinned(report_path, args.report_sha256, "Original report"))
    manifest = {"path": str(args.owner_manifest.resolve(strict=True)), "sha256": args.owner_manifest_sha256}
    require(report["source_manifest"] == manifest, "Original report source manifest differs from the pinned owner manifest")
    binding_raw = read_pinned(args.runtime_binding, args.runtime_binding_sha256, "Group runtime binding")
    binding = json.loads(binding_raw)
    tools = runtime_tools(previous, report["compiler"], previous.absolute(report["project"]), originals)
    check_runtime_binding(binding, args.source_commit, owners, str(report_path), args.report_sha256, manifest, tools)

    # Use the existing multi-owner validation and archive implementation. Its
    # runtime binding is the singleton format, so the group proof stays outside it.
    result = previous.export(argparse.Namespace(
        report=report_path, report_sha256=args.report_sha256,
        runtime_binding=None, runtime_binding_sha256=None,
        source_commit=args.source_commit, output_dir=args.output_dir), project, owners, originals)
    directory = args.output_dir.resolve()
    base_raw = read_pinned(directory / "RECEIPT.json", result["receipt_sha256"], "Base receipt")
    receipt = group_receipt(base_raw, manifest_raw, binding_raw, args.source_commit, owners, binding)
    (directory / OWNER_MANIFEST).write_bytes(manifest_raw)
    (directory / RUNTIME_BINDING).write_bytes(binding_raw)
    receipt_raw = (json.dumps(receipt, indent=2) + "\n").encode()
    receipt_file = directory / GROUP_RECEIPT
    receipt_file.write_bytes(receipt_raw)
    return {**result, **receipt, "group_receipt": str(receipt_file), "group_receipt_sha256": digest(receipt_raw)}


def verify(args, project, previous, originals):
    directory = args.evidence_dir.resolve(strict=True)
    raw = read_pinned(directory / GROUP_RECEIPT, args.group_receipt_sha256, "Group receipt")
    receipt = json.loads(raw)
    manifest_raw = read_pinned(directory / OWNER_MANIFEST, args.owner_manifest_sha256, "Owner manifest")
    owners = parse_owner_manifest(manifest_raw, args.owner_manifest_sha256)
    binding_raw = read_pinned(directory / RUNTIME_BINDING, args.runtime_binding_sha256, "Group runtime binding")
    binding = json.loads(binding_raw)
    base_path = directory / "RECEIPT.json"
    base_raw = read_pinned(base_path, receipt["base_receipt_sha256"], "Base receipt")
    require(receipt == group_receipt(base_raw, manifest_raw, binding_raw, args.source_commit, owners, binding),
            "Group receipt differs from recovered components")
    base = json.loads(base_raw)
    runner_path = previous.absolute(base["files"]["config/" + RUNTIME_FILES[0]]["path"])
    tools = runtime_tools(previous, base["compiler"], runner_path.parents[2], originals)
    check_runtime_binding(binding, args.source_commit, owners, base["report_path"], base["report_sha256"],
                          receipt["source_manifest"], tools)
    result = previous.verify(argparse.Namespace(
        receipt=base_path, receipt_sha256=receipt["base_receipt_sha256"],
        source_commit=args.source_commit, archive=directory / "evidence.tar.xz"), project, owners, originals)
    return {**receipt, "status": "PASS_LOCAL_GROUP_EVIDENCE_VERIFICATION",
            "group_receipt_sha256": args.group_receipt_sha256,
            "base_verification_status": result["status"], "declaration_count": result["declaration_count"],
            "module_counts": result["module_counts"], "observed_transitive_axioms": result["observed_transitive_axioms"],
            "local_lean_run": result["local_lean_run"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_subparsers(dest="action", required=True)
    exporter = actions.add_parser("export")
    for name in ("report", "owner-manifest", "runtime-binding", "output-dir"):
        exporter.add_argument("--" + name, type=Path, required=True)
    exporter.add_argument("--report-sha256", required=True)
    verifier = actions.add_parser("verify")
    verifier.add_argument("--evidence-dir", type=Path, required=True)
    verifier.add_argument("--group-receipt-sha256", required=True)
    for action in (exporter, verifier):
        action.add_argument("--project", type=Path, required=True)
        for name in ("source-commit", "owner-manifest-sha256", "runtime-binding-sha256"):
            action.add_argument("--" + name, required=True)
    args = parser.parse_args()
    try:
        for name, value in vars(args).items():
            if name.endswith("_sha256"):
                require(SHA256.fullmatch(value), "Expected full digest for --" + name.replace("_", "-"))
        require(re.fullmatch(r"[0-9a-f]{40}", args.source_commit), "Expected full Git source commit")
        previous = load_previous()
        project = args.project.resolve(strict=True)
        require(previous.git_bytes(project, "rev-parse", args.source_commit + "^{commit}").decode().strip()
                == args.source_commit, "Frozen source commit differs")
        originals = previous.load_originals(project)
        function = export if args.action == "export" else verify
        print(json.dumps(function(args, project, previous, originals), indent=2))
    except (OSError, RuntimeError, ValueError, TypeError, LookupError, AttributeError,
            subprocess.CalledProcessError) as error:
        parser.exit(1, "Group evidence rejected: " + str(error) + "\n")


if __name__ == "__main__":
    main()
