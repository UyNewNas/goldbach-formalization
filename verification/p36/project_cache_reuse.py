"""Read-only validation of transferred fresh strict/kernel/axiom receipt objects.

Historical donor objects without complete import bindings are not accepted.
This helper never treats a cache hit as a fresh strict/kernel proof receipt.
Only the serial runner copies validated objects into its own output directory.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path


# Fresh root-owned receipt, independently reviewed in this continuation.
# A caller-authored JSON file is not an authority to create verification credit.
ACCEPTED_LEAF_RECEIPTS = {
    "f36259c80756a53ca0335561500b6e2c64549ff474c69a554b57be56fda159fb":
        "ImbalancedChen.P3TaggedPhysicalRhoPushforward",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inspect_verified_leaf_bundle(bundle: Path, graph, compiler: dict, pins: dict) -> dict:
    """Reuse a transferred fresh receipt for a module with no project dependencies."""
    receipt_file = bundle / "RECEIPT.json"
    receipt_bytes = receipt_file.read_bytes()
    receipt_digest = hashlib.sha256(receipt_bytes).hexdigest()
    if receipt_digest not in ACCEPTED_LEAF_RECEIPTS:
        raise ValueError("receipt has not been independently accepted for reuse")
    receipt = json.loads(receipt_bytes)
    module = receipt["module"]
    if module != ACCEPTED_LEAF_RECEIPTS[receipt_digest]:
        raise ValueError("accepted receipt module differs")
    node = graph.nodes[module]
    if node.package != "project" or any(graph.nodes[n].package == "project" for n in node.imports):
        raise ValueError("verified bundle must have no project dependencies")
    if not all(receipt.get(k) is True for k in (
            "strict_compilation", "bundled_kernel_replay", "complete_transitive_axiom_audit")):
        raise ValueError("bundle lacks complete strict/kernel/axiom acceptance")
    if receipt["compiler"]["sha256"] != compiler["sha256"] or receipt["dependency_pins"] != pins:
        raise ValueError("verified bundle compiler or dependency pins differ")
    archive = bundle / "evidence.tar.xz"
    if sha256(archive) != receipt["archive_sha256"]:
        raise ValueError("verified full evidence archive differs")
    relative = module.replace(".", "/")
    source, obj = bundle / "source" / (relative + ".lean"), bundle / "objects" / (relative + ".olean")
    if sha256(node.source) != receipt["source_sha256"] or sha256(source) != receipt["source_sha256"]:
        raise ValueError("verified source differs")
    if sha256(obj) != receipt["olean_sha256"]:
        raise ValueError("verified object differs")
    required = ["source/" + relative + ".lean", "objects/" + relative + ".olean",
                "run/compile-" + module + ".log", "run/replay-" + module + ".log",
                "run/owned-inventory-audit.log", "run/declarations.json", "run/report.json"]
    for name in required:
        if sha256(bundle / name) != receipt["files"][name]:
            raise ValueError("verified receipt evidence differs: " + name)
    report = json.loads((bundle / "run/report.json").read_text())
    entry = report["modules"][module]
    if report.get("status") != "VERIFIED_OWNED" or report.get("targets") != [module] or \
            report.get("dependency_pins") != pins or report["compiler"]["sha256"] != compiler["sha256"] or \
            entry.get("action") != "compiled" or entry.get("strict") is not True or \
            entry.get("exit_code") != 0 or entry.get("source_sha256") != receipt["source_sha256"]:
        raise ValueError("verified report is not the accepted fresh source build")
    for stage in ("compile-" + module, "replay-" + module, "owned-inventory-audit"):
        matches = [s for s in report["commands"] if s["name"] == stage]
        if len(matches) != 1 or matches[0]["exit_code"] != 0:
            raise ValueError("verified report stage differs: " + stage)
    replay = (bundle / ("run/replay-" + module + ".log")).read_text()
    if "replaying " + module not in replay.splitlines():
        raise ValueError("verified receipt lacks exact replay line")
    declarations = json.loads((bundle / "run/declarations.json").read_text())
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    if set(receipt["allowed_transitive_axioms"]) != allowed or \
            len(declarations) != receipt["complete_owned_declaration_count"] or \
            any(r["module"] != module or set(r["axioms"]) - allowed for r in declarations):
        raise ValueError("verified receipt declaration inventory differs")
    return {"module": module, "source": str(source), "source_sha256": receipt["source_sha256"],
            "object": str(obj), "object_sha256": receipt["olean_sha256"],
            "receipt": str(receipt_file), "receipt_sha256": receipt_digest,
            "origin": "fresh_strict_kernel_axiom_receipt_transferred_without_reverification",
            "evidence_sha256": {str(archive): receipt["archive_sha256"],
                                **{str(bundle / name): receipt["files"][name] for name in required}}}
