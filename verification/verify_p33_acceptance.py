"""Verify the P3.3 acceptance evidence without running Lean or using the network."""

import argparse
from collections import defaultdict
import gzip
import hashlib
from io import BytesIO
import json
from pathlib import Path
import re
import sys
import zipfile


RECEIPTS = Path("verification/proof-continuation/2026-10-15")
EVIDENCE = Path("docs/part3-distribution/p3-3-acceptance-20261125")
CONTINUATION = Path("docs/part3-distribution/continuation-20261124")
PINS = ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
TARGETS = [
    "ActualLargeGCDBetaMass",
    "CleanBetaLargeGCDMajorant",
    "PairedAlphaDeletion",
    "TransposedLargeGCDFourier",
    "SharedFirstFactorLargePairedGCDW",
    "SharedFirstFactorLargePairedGCDNonzero",
    "SharedFirstFactorLargeSupportedDeletion",
    "SharedFirstFactorSmallPairedSupportedReduction",
    "SharedFirstFactorSmallCoreFourierTruncation",
    "SharedFirstFactorSmallCorePrimeDifferenceReindex",
    "SharedFirstFactorSmallCoreSmoothFrequency",
    "SharedFirstFactorSmallCoreSquaredFinite",
    "SharedFirstFactorSupportedCoreCauchy",
]
AXIOM_ALLOWLIST = {"propext", "Classical.choice", "Quot.sound"}
ARCHIVE_SHA256 = "956c1a2bb2f15aada2d064b9b42587010ed4f2e34deb27f2aae89812860f13b2"
PROJECT_BLOB_MAP_SHA256 = "763df9c9f43e893b070376240b08fb6b4180a5c41771949351a3f7e55eded28a"
CORE_ZIP_SHA256 = "c9f5fae1810faa640c970bdd4db5f0efc20240f6c45cd409b58163829d189499"
CORE_COMMIT = "b5c70b7df23d1ba4b84634d06b9087c55e6167d2"
CONTINUATION_COMMIT = "ef1479c272bdd6b24800fa10409d793f0a2fe95c"
PART3_BASELINE_COMMIT = "c509267dc630d91df33033abde1c484ec86b96ae"
PART3_BASELINE_SHA256 = "c9367eb0ad5f2a35ec46e004ca9a6172d7a8113f8293862c38fffb94e9d90b34"
SOURCE_COMMIT = "7f5330cace31383f5626da526b476dd4b0f43376"


def read_json(path):
    return json.loads(path.read_bytes())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blob(path):
    data = path.read_bytes()
    return hashlib.sha1(f"blob {len(data)}\0".encode() + data).hexdigest()


def local_path(module):
    return Path(*module.split(".")).with_suffix(".lean")


def source_graph(root, targets):
    graph = {}
    pending = list(targets)
    while pending:
        module = pending.pop()
        source = root / local_path(module)
        if module in graph:
            continue
        if module != "ImbalancedChen" and not module.startswith("ImbalancedChen."):
            continue
        if not source.is_file():
            raise ValueError(f"Missing project source: {source.relative_to(root)}")
        imports = re.findall(
            r"^\s*(?:(?:public|private|meta|all)\s+)*import\s+([\w.]+)",
            source.read_text(),
            re.M,
        )
        graph[module] = {
            "path": str(local_path(module)),
            "sha256": digest(source),
            "git_blob": blob(source),
            "direct_imports": imports,
        }
        pending.extend(imports)
    return graph


def project_closure(graph, target):
    visited = set()
    pending = [target]
    while pending:
        module = pending.pop()
        if module in graph and module not in visited:
            visited.add(module)
            pending.extend(graph[module]["direct_imports"])
    return visited


def parsed_markers(log, tag):
    prefix = tag + " "
    return [json.loads(line[len(prefix):]) for line in log if line.startswith(prefix)]


def verify_receipt(module, graph, root, archive, manifest, target_declarations):
    binding = manifest["modules"][module]
    errors = []
    manifest_checks = {}
    for file in ("compile", "audit"):
        if file not in binding:
            errors.append(f"Manifest has no {file} receipt")
    if errors:
        return {"errors": errors}
    compile_path = archive / binding["compile"]
    audit_path = archive / binding["audit"]
    compile_receipt = read_json(compile_path)
    audit = read_json(audit_path)
    comp = compile_receipt["binding"]
    source_hash = graph[module]["sha256"]
    if (
        audit["targets"].get(module) != source_hash
        or audit["inputs_before"]["sources"].get(module) != source_hash
        or binding["source_sha256"] != source_hash
    ):
        errors.append("Audit target source differs from current project source")
    if comp["source_sha256"] != source_hash:
        errors.append("Compile target source differs from current project source")
    if compile_receipt["binding_after"] != comp:
        errors.append("Compile inputs changed during compilation")
    if audit["inputs_before"] != audit["inputs_after"]:
        errors.append("Audit inputs changed during acceptance")
    pins = comp["pins"]
    if not all(digest(root / path) == value for path, value in pins.items()):
        errors.append("Current repository pins differ from compile pins")
    if audit["inputs_before"]["pins"] != pins:
        errors.append("Audit pins differ from compile pins")
    if compile_receipt["status"] != "PASS" or compile_receipt["exit_code"] != 0:
        errors.append("Strict compilation did not succeed")
    if not compile_receipt["warnings_as_errors"] or "-DwarningAsError=true" not in compile_receipt["command"]:
        errors.append("Compile receipt did not enforce warnings-as-errors")
    if audit["status"] != "PASS_OWNED_REPLAY_AND_COMPLETE_TYPES_AXIOMS":
        errors.append("Audit did not accept complete owned replay/types/axioms")
    objects = compile_receipt["object_parts"]
    if audit["inputs_before"]["owned_object_parts"].get(module) != objects:
        errors.append("Kernel/type audit object differs from compiled object")
    if comp["lean_real_sha256"] != audit["inputs_before"]["lean_real_sha256"]:
        errors.append("Compile and audit Lean binaries differ")
    inventory_file = audit_path.parent / "declarations.json"
    inventory_path = inventory_file
    if not inventory_path.exists():
        inventory_path = inventory_file.with_suffix(".json.gz")
    if inventory_path.suffix == ".gz":
        declarations = json.loads(gzip.decompress(inventory_path.read_bytes()))
    else:
        declarations = read_json(inventory_path)
    if len(audit["targets"]) == 1 and any(row["module"] != module for row in declarations):
        errors.append("Declaration inventory lists an unrelated module")
    own = [row for row in declarations if row["module"] == module]
    names = sorted(row["name"] for row in own)
    axioms = set().union(*(row["axioms"] for row in own))
    if not names or names != sorted(set(names)) or len(names) != audit["declaration_counts"][module]:
        errors.append("Declaration inventory has missing or duplicate identities")
    if len(names) != binding["declarations"]:
        errors.append("Manifest declaration count differs")
    if not axioms <= AXIOM_ALLOWLIST:
        errors.append("Forbidden transitive axioms")
    if any(
        not row["type"].strip()
        or "⋯" in row["type"]
        or row["axiom"]
        or row["partial"]
        or row["unsafe"]
        for row in own
    ):
        errors.append("Forbidden declaration metadata or incomplete type")
    log_path = audit_path.parent / "declarations.log"
    if not log_path.exists():
        log_path = log_path.with_suffix(".log.gz")
        declarations_log_bytes = gzip.decompress(log_path.read_bytes())
    else:
        declarations_log_bytes = log_path.read_bytes()
    declarations_log = declarations_log_bytes.decode().splitlines()
    logs = [row for row in parsed_markers(declarations_log, "P0_QUEUE_DECL") if row["module"] == module]
    if sorted(logs, key=lambda row: row["name"]) != sorted(own, key=lambda row: row["name"]):
        errors.append("Saved declaration types/axioms differ from the actual tool log")
    signed_inventories = [i for i in parsed_markers(declarations_log, "P0_QUEUE_INVENTORY") if i["module"] == module]
    if len(signed_inventories) != 1 or any(
        sorted(signed_inventories[0][key]) != names for key in ("serialized", "environment")
    ):
        errors.append("Saved module metadata inventory differed from all logged declarations")
    import_inventories = parsed_markers(declarations_log, "P0_QUEUE_IMPORTS")
    closure = project_closure(graph, module)
    if len(import_inventories) != len(audit["targets"]) or any(
        inv != import_inventories[0] or not closure <= set(inv) for inv in import_inventories
    ):
        errors.append("Current project closure is missing from the historical Lean import log")
    replay_stages = [s for s in audit["stages"] if s["kind"] == "stock_replay" and s["module"] == module]
    replay_path = audit_path.parent / f"replay-{module}.log"
    replay_receipt_path = replay_path.with_suffix(".json")
    if len(replay_stages) != 1:
        errors.append("Missing unique kernel replay stage")
    else:
        replay = replay_stages[0]["result"]
        if (
            replay["returncode"] != 0
            or replay["status"] != "PASS"
            or (not replay_path.is_file())
            or replay_path.read_text().splitlines() != [f"replaying {module}"]
            or digest(replay_path) != replay["log_sha256"]
            or read_json(replay_receipt_path) != replay
        ):
            errors.append("Kernel replay receipt is missing or failed exact log acceptance")
    axiom_stages = [s for s in audit["stages"] if s["kind"] == "full_inventory_type_axioms"]
    if len(axiom_stages) != 1 or (
        axiom_stages[0]["exit_code"] != 0
        or axiom_stages[0]["log_sha256"] != hashlib.sha256(declarations_log_bytes).hexdigest()
    ):
        errors.append("Axiom/inventory stage did not pass with the attached exact log")
    for evidence in (
        compile_path,
        compile_path.parent / "stdout.log",
        audit_path,
        replay_path,
        replay_receipt_path,
        inventory_path,
        log_path,
        audit_path.parent / "OwnedAudit.lean",
    ):
        key = str(evidence.relative_to(archive))
        digest_value = digest(evidence)
        if manifest["files"].get(key) != digest_value:
            errors.append(f"Archive manifest does not bind {key}")
        manifest_checks[key] = digest_value
    links = {}
    direct_source = comp.get("direct_source_sha256", {})
    direct_object = comp.get("dependencies", {})
    if set(direct_source) != set(graph[module]["direct_imports"]) or set(direct_object) != set(direct_source):
        errors.append("Historical direct import inventory differs from current source")
    for dependency in graph[module]["direct_imports"]:
        dep_source = direct_source.get(dependency)
        dep_object = direct_object.get(dependency)
        if dependency in graph:
            dep_manifest = manifest["modules"].get(dependency, {})
            if dep_source != graph[dependency]["sha256"]:
                errors.append(f"Historical source binding differs for {dependency}")
            links[dependency] = {
                "source_sha256": dep_source,
                "object_sha256": dep_object,
                "same_historical_owned_audited_object": dep_object
                == dep_manifest.get("audited_object_parts", {}).get(".olean"),
            }
        else:
            links[dependency] = {"source_sha256": dep_source, "object_sha256": dep_object, "external": True}
    if module in target_declarations:
        target_declarations[module] = own
    return {
        "errors": errors,
        "declarations": len(names),
        "axioms": sorted(axioms),
        "evidence_sha256": manifest_checks,
        "dependency_bindings": links,
        "object_parts": objects,
        "project_closure_size": len(closure),
        "external_closure_replay_claimed": audit["external_closure_replay_claimed"],
    }


def verify_inherited(root, graph, audited, remote):
    core_zip = root / EVIDENCE / "core-44318928116.zip"
    baseline_report = root / CONTINUATION / "baseline-c509267-report.json"
    if digest(core_zip) != CORE_ZIP_SHA256:
        raise ValueError("Core workflow artifact SHA256 does not match GitHub")
    if digest(baseline_report) != PART3_BASELINE_SHA256:
        raise ValueError("Published Part 3 baseline report SHA256 differs")
    base = read_json(baseline_report)
    if (
        base["head_commit"] != PART3_BASELINE_COMMIT
        or base["status"] != "PASSED"
        or not set(base["axiom_union"]) <= AXIOM_ALLOWLIST
    ):
        raise ValueError("Part 3 baseline receipt is not the accepted pinned report")
    core_tree_path = root / EVIDENCE / "github-b5c70b7d-core-project-blobs.json"
    if digest(core_tree_path) != PROJECT_BLOB_MAP_SHA256:
        raise ValueError("Reference Core commit blob map SHA256 differs")
    core_tree = read_json(core_tree_path)
    for pin in PINS:
        if core_tree[pin] != remote[pin] or core_tree[pin] != blob(root / pin):
            raise ValueError(f"Core/current dependency pin differs: {pin}")
    with zipfile.ZipFile(core_zip) as zip_file:
        logs = "_temp/lean-verification-logs/"
        outcomes = zip_file.read(logs + "outcomes.log").decode()
        for marker in (
            "build=success",
            "leanchecker=success",
            "axiom-audit=success",
        ):
            if marker not in outcomes.splitlines():
                raise ValueError(f"Workflow completion marker missing: {marker}")
        provenance = zip_file.read(logs + "provenance.log").decode()
        if f"project_commit={CORE_COMMIT}" not in provenance.splitlines():
            raise ValueError("Workflow provenance commit differs")
        replay = {
            line.removeprefix("replaying ")
            for line in zip_file.read(logs + "leanchecker.log").decode().splitlines()
            if line.startswith("replaying ")
        }
        axiom_log = zip_file.read(logs + "axiom-audit.log").decode()
        expected_axiom_log = (
            "axiom-audit: audited 6559 declaration(s) under 'ImbalancedChen'; "
            "all within the allowlist [propext, Classical.choice, Quot.sound]."
        )
        if expected_axiom_log not in axiom_log.splitlines():
            raise ValueError("Core workflow root axiom marker missing")
    inherit_baseline = {}
    inherit_core = {}
    still_uncovered = []
    for module, info in graph.items():
        if module in audited:
            continue
        path = info["path"]
        if module in base["modules"] and info["sha256"] == base["source_sha256"][path]:
            parent_links = [
                (parent, audit["dependency_bindings"][module]["object_sha256"])
                for parent, audit in audited.items()
                if module in audit.get("dependency_bindings", {})
            ]
            obj = base["overlay_olean_sha256"][str(local_path(module).with_suffix(".olean"))]
            if all(object_hash == obj for _, object_hash in parent_links):
                inherit_baseline[module] = {
                    "object_sha256": obj,
                    "source_sha256": info["sha256"],
                    "declarations": next(r["count"] for r in base["module_counts"] if r["module"] == module),
                    "parents_bound_to_this_object": [p for p, _ in parent_links],
                }
                continue
        if module in replay and core_tree.get(path) == info["git_blob"]:
            inherit_core[module] = {
                "git_blob": info["git_blob"],
                "source_sha256": info["sha256"],
            }
        else:
            still_uncovered.append(module)
    return {
        "core_commit": CORE_COMMIT,
        "core_commit_tree": "ccfe1b598822d38e5c7c36c4849c3d52e7adc6c7",
        "core_project_tree": "b5a20e139221ddb41ec325190f517faef28787cf",
        "core_run": 44318928116,
        "core_job": 134852370583,
        "core_artifact": 14441606127,
        "core_artifact_sha256": CORE_ZIP_SHA256,
        "core_scope": "Identical project source and pins with literal stock replay and root transitive axiom scan. No serialized per-module type inventory or historical imported-object equality was exported for this subset.",
        "core_replayed_module_count": len(replay),
        "core_axiom_audit_count": 6559,
        "core_matching_prerequisites": inherit_core,
        "current_continuation_commit": CONTINUATION_COMMIT,
        "part3_baseline_source_commit": PART3_BASELINE_COMMIT,
        "part3_baseline_receipt_sha256": PART3_BASELINE_SHA256,
        "part3_baseline_matching_prerequisites": inherit_baseline,
        "still_uncovered_project_modules": still_uncovered,
    }


def verify(root):
    remote_tree_path = root / EVIDENCE / "github-7f5330ca-project-blobs.json"
    if digest(remote_tree_path) != PROJECT_BLOB_MAP_SHA256:
        raise ValueError("Reference project commit blob map SHA256 differs")
    remote = read_json(remote_tree_path)
    targets = ["ImbalancedChen.Part3" + name for name in TARGETS]
    graph = source_graph(root, targets)
    for info in graph.values():
        info["github_git_blob"] = remote.get(info["path"])
        if info["git_blob"] != info["github_git_blob"]:
            raise ValueError(f"Project source differs from the selected GitHub blob: {info['path']}")
    if {info["path"] for info in graph.values()} != set(remote) - set(PINS):
        raise ValueError("Selected GitHub project blob set differs from the complete current closure")
    archive = root / RECEIPTS
    if digest(archive / "manifest.json") != ARCHIVE_SHA256:
        raise ValueError("Published historical acceptance manifest SHA256 differs")
    manifest = read_json(archive / "manifest.json")
    target_declarations = {module: [] for module in targets}
    audited = {}
    for module in graph:
        if module not in manifest["modules"]:
            continue
        audit = verify_receipt(module, graph, root, archive, manifest, target_declarations)
        if audit["errors"]:
            raise ValueError(f"{module}: {'; '.join(audit['errors'])}")
        audited[module] = audit
    for module, declarations in target_declarations.items():
        if not declarations:
            raise ValueError(f"Missing complete historical acceptance for target {module}")
    imported_from_different_or_uncovered_object = defaultdict(list)
    for module, audit in audited.items():
        for dependency, link in audit.get("dependency_bindings", {}).items():
            if not link.get("external") and not link["same_historical_owned_audited_object"]:
                imported_from_different_or_uncovered_object[dependency].append(module)
    inherited = verify_inherited(root, graph, audited, remote)
    if inherited["still_uncovered_project_modules"]:
        raise ValueError("Project prerequisites lack replay evidence: "
                         + ", ".join(inherited["still_uncovered_project_modules"]))
    bridged_objects = inherited["part3_baseline_matching_prerequisites"]
    if set(imported_from_different_or_uncovered_object) != set(bridged_objects):
        raise ValueError("Imported historical project objects lack exact audited bindings")
    target_rows = sorted(
        (row for rows in target_declarations.values() for row in rows),
        key=lambda row: (row["module"], row["name"]),
    )
    rows_by_name = defaultdict(list)
    for row in target_rows:
        rows_by_name[row["name"]].append(row)
    repeated_names = {}
    for name, rows in rows_by_name.items():
        if len(rows) > 1:
            if len({(row["type"], tuple(sorted(row["axioms"]))) for row in rows}) != 1:
                raise ValueError(f"Conflicting historical records for declaration {name}")
            repeated_names[name] = [row["module"] for row in rows]
    declaration_bytes = (json.dumps(target_rows, sort_keys=True, ensure_ascii=False, indent=2) + "\n").encode()
    compressed = BytesIO()
    with gzip.GzipFile(fileobj=compressed, mode="wb", mtime=0) as output_gzip:
        output_gzip.write(declaration_bytes)
    declarations = compressed.getvalue()
    output = {
        "status": "PASS_HISTORICAL_EVIDENCE_REUSE",
        "fresh_lean_execution": False,
        "scope": "P3.3 large paired-gcd, large supported part, and the actual common finite-frequency small core",
        "full_p3_claimed": False,
        "external_import_environment_replayed_by_this_verifier": False,
        "github_source": SOURCE_COMMIT,
        "github_source_commit_tree": "705c376efe7f65db7df4b5bc837e0c63a9b6a675",
        "github_source_project_tree": "35bbf69a70617e7c4c887dedaa59ea443bc54918",
        "github_project_blob_map_sha256": PROJECT_BLOB_MAP_SHA256,
        "historical_archive": str(RECEIPTS),
        "historical_manifest_sha256": ARCHIVE_SHA256,
        "historical_manuscript_pin": manifest["manuscript"],
        "historical_manifest_boundaries": manifest["notes"],
        "summary": {
            "target_modules": len(target_declarations),
            "target_declarations": len(target_rows),
            "target_distinct_declaration_names": len(rows_by_name),
            "project_source_closure": len(graph),
            "strict_historical_modules_including_targets": len(audited),
            "strict_historical_declarations_including_targets": sum(a["declarations"] for a in audited.values()),
            "part3_baseline_matching_prerequisites": len(bridged_objects),
            "core_matching_prerequisites": len(inherited["core_matching_prerequisites"]),
        },
        "targets": targets,
        "target_repeated_declaration_names": repeated_names,
        "target_transitive_axiom_union": sorted({axiom for row in target_rows for axiom in row["axioms"]}),
        "target_declarations_json_sha256": hashlib.sha256(declaration_bytes).hexdigest(),
        "target_declarations_gzip_sha256": hashlib.sha256(declarations).hexdigest(),
        "source_graph": graph,
        "verified_receipts": audited,
        "imported_from_different_or_uncovered_object": imported_from_different_or_uncovered_object,
        "inherited": inherited,
    }
    return output, declarations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, nargs="?", default=Path(__file__).resolve().parents[1])
    parser.add_argument("--report", type=Path, help="write the deterministic JSON report to this path")
    parser.add_argument("--declarations", type=Path, help="write the target declaration inventory as gzip")
    args = parser.parse_args()
    try:
        report, declarations = verify(args.checkout)
        if args.declarations:
            args.declarations.write_bytes(declarations)
        report_text = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.report:
            args.report.write_text(report_text)
        else:
            print(report_text, end="")
    except (OSError, KeyError, TypeError, ValueError, zipfile.BadZipFile) as error:
        print(f"P3.3 acceptance failed: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
