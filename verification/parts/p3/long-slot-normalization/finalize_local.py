#!/usr/bin/env python3
"""Bind completed local gates and retain their exact evidence; runs no Lean.

The evidence archive contains raw execution receipts/logs, before-import hash
inventories, compiler declarations, matching-cache provenance and target object.
It is a base64-encoded xz tar so it can be retained by the repository connector.
"""

from pathlib import Path
import argparse
import base64
import datetime
import hashlib
import importlib.util
import json
import lzma
import re
import shutil
import sys
import tarfile

TARGET = "ImbalancedChen.Part3LongSlotNormalization"
SOURCE_HASH = "ca4e4d237bb4a5d21f72af3223001621902d6763d0b7ef1f423f532fd94f69fc"
UPSTREAM_HASH = "67ccc48e6a4befadfd4b5639e2cdb4bd43e443b8f4eaf3086fe5a6c5fbd0023e"


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def dump(path, data):
    Path(path).write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-dir", required=True, type=Path)
    args = parser.parse_args()
    runtime = args.runtime_dir
    config = json.loads((runtime / "runtime-config.json").read_text())
    repo = Path(config["repo"])
    destination = Path(__file__).resolve().parent
    execution = runtime / "execution"
    attempts = [json.loads(p.read_text()) for p in sorted(execution.glob("*-receipt.json"))]
    selected = {}
    for action in ("compile", "replay", "audit"):
        records = [r for r in attempts if r["action"] == action and r["scoped_gate_passed"]]
        require(bool(records), "No successful scoped gate: " + action)
        selected[action] = records[-1]
    compile_gate, replay_gate, audit_gate = (selected[a] for a in ("compile", "replay", "audit"))
    source = repo / "ImbalancedChen/Part3LongSlotNormalization.lean"
    upstream = repo / "ImbalancedChen/Part3LongSlotDistribution.lean"
    require(sha(source) == SOURCE_HASH, "Normalization source changed")
    require(sha(upstream) == UPSTREAM_HASH, "Accepted upstream source changed")
    object_identity = compile_gate["target_parts_after"]
    require(bool(object_identity), "No strict compilation object")
    for action, record in selected.items():
        require(record["returncode"] == 0 and not record["verification_failure_reasons"], "Gate failed")
        require(record["runtime_config_sha256"] == sha(runtime / "runtime-config.json"), "Runtime configuration changed")
        require(record["production_source_sha256_before"] == SOURCE_HASH == record["production_source_sha256_after"], "Different production sources across gates")
        require(record["all_import_sources_and_object_parts_unchanged"], "Imports changed during a gate")
        require(record["target_parts_after"] == object_identity, "Different production object across gates")
        if action != "compile":
            require(record["target_parts_before"] == object_identity, "Replay/audit did not consume strict compile object")
        require(sha(record["source"]) == record["source_sha256_after"], "A final gate source changed")
        require(sha(record["log"]) == record["log_sha256"], "Raw gate log changed")
        require(sha(record["import_snapshot"]) == record["import_snapshot_sha256"], "Import inventory changed")
    for path, value in object_identity.items():
        require(sha(path) == value, "Production object changed after verification")
    captures = {a: json.loads(Path(r["import_snapshot"]).read_text()) for a, r in selected.items()}
    require(captures["compile"] == captures["replay"], "Compile and replay imports differ")
    common = captures["compile"]
    audit_capture = captures["audit"]
    require([m for m in audit_capture["modules"] if m["module"] != TARGET] == common["modules"], "Audit common import layout differs")
    for path, value in common["sha256"].items():
        require(audit_capture["sha256"].get(path) == value, "Audit common import source/object differs")
    extras = {p: h for p, h in audit_capture["sha256"].items() if p not in common["sha256"]}
    require(extras == {str(source): SOURCE_HASH, **object_identity}, "Unexpected audit-only source/object")
    require(audit_gate["actual_imports_match_predicted_paths"], "Lean-resolved imports differ")
    declarations_path = Path(audit_gate["log"]).with_suffix("").with_name(Path(audit_gate["log"]).stem + "-compiler-declarations.json")
    declarations = json.loads(declarations_path.read_text())
    audit_log = Path(audit_gate["log"]).read_text()
    serialized = [json.loads(line.removeprefix("PART3_LOCAL_SERIALIZED "))
                  for line in audit_log.splitlines() if line.startswith("PART3_LOCAL_SERIALIZED ")]
    require(serialized == [{"extra_codegen_name_count": 0, "has_data": True, "import_all": True,
                            "is_module": False, "module": TARGET, "serialized_constant_count": 2}],
            "Complete legacy serialized inventory not confirmed")
    required = {"ImbalancedChen.part3_eventually_longSlot_logAccuracy",
                "ImbalancedChen.part3_eventually_longSlot_singularNormalization"}
    require(len(declarations) == 2 and {d["name"] for d in declarations} == required, "Theorem inventory mismatch")
    require(all(d["kind"] == "theorem" and set(d["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for d in declarations), "Forbidden declaration or axiom")
    # Preserve existing complete gates byte for byte and scan only owned sources.
    sys.dont_write_bytecode = True
    lexer_path = repo / "verification/verify_variable_envelope_boxes.py"
    spec = importlib.util.spec_from_file_location("part3_unchanged_source_lexer", lexer_path)
    lexer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(lexer)
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx|skipKernel(?:TC)?)\b")
    for path in (source, upstream):
        require(forbidden.search(lexer.lean_code(path.read_text())) is None, "Forbidden source marker")
    trees = json.loads((runtime / "remote-trees.json").read_text())
    original = {r["path"]: r for r in trees["branch"]["tree"] if r["type"] == "blob"}
    changed = []
    for name, record in original.items():
        data = (repo / name).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != record["sha"]:
            changed.append(name)
    require(set(changed) <= {"ImbalancedChen/Part3LongSlotDistribution.lean", "docs/part3-distribution/README.md"}, "Out-of-batch modification")
    protected = ["lean-toolchain", "lake-manifest.json", "lakefile.toml", "docs/CURRENT_MANUSCRIPT_MAP.md",
                 "verification/verify_part3_distribution.py", "verification/Part3DistributionAudit.lean",
                 ".github/workflows/part3-distribution.yml"]
    require(not set(changed) & set(protected), "Frozen config or full gate changed")
    guard = {"source_scan_passed": True, "normalization_source_unchanged": True,
             "changed_preexisting_files": changed, "preexisting_blob_count": len(original),
             "frozen_configs_and_complete_gates": {p: sha(repo/p) for p in protected}}
    dump(destination / "source-and-scope-guard.json", guard)
    dump(destination / "compiler-declarations.json", declarations)
    type_doc = "# 编译器确认的完整类型\n\n来源：成功的 defining-module 审计；不是源码正则提取。\n\n"
    for declaration in declarations:
        type_doc += "## " + declaration["name"] + "\n\n```lean\n" + declaration["readable_type"] + "\n```\n\n"
        type_doc += "传递公理：`" + "`, `".join(declaration["axioms"]) + "`。\n\n"
        type_doc += "<details>\n<summary>完整 pp.all 输出</summary>\n\n```lean\n" + declaration["type"] + "\n```\n\n</details>\n\n"
    (destination / "COMPILER_TYPES.md").write_text(type_doc)
    logs = destination / "logs"
    logs.mkdir(exist_ok=True)
    for action, record in selected.items():
        if action == "audit":
            # The complete raw audit log, including all actual import paths, is archived.
            text = "\n".join(line for line in Path(record["log"]).read_text().splitlines()
                              if not line.startswith("PART3_LOCAL_IMPORT ")) + "\n"
            (logs / "audit-with-import-lines-omitted.log").write_text(text)
        else:
            shutil.copyfile(record["log"], logs / (action + ".log"))
    archive_inputs = {}
    for name in ["runtime-config.json", "source-closure-manifest.json", "project-overlay-manifest.json",
                 "cache-audit.json", "legacy-audit-review.json", "remote-trees.json", "start-snapshot.json"]:
        archive_inputs["runtime/" + name] = runtime / name
    for directory in ("execution", "history"):
        for path in sorted((runtime / directory).rglob("*")):
            if path.is_file():
                archive_inputs[str(path.relative_to(runtime))] = path
    for path in [source, upstream, repo/"verification/parts/p3/LongSlotNormalizationAudit.lean",
                 destination/"run_local.py", Path(__file__), destination/"source-and-scope-guard.json"]:
        archive_inputs["source/" + str(path.relative_to(repo))] = path
    archive_inputs["runtime/frontend-driver.lean.txt"] = Path(config["driver"]) / "lakefile.lean"
    for path in object_identity:
        archive_inputs["objects/ImbalancedChen/" + Path(path).name] = Path(path)
    archive_path = runtime / "local-evidence.tar.xz"
    with lzma.open(archive_path, "wb", filters=[{"id": lzma.FILTER_LZMA2, "preset": 3, "dict_size": 1 << 26}]) as compressed:
        with tarfile.open(fileobj=compressed, mode="w|") as archive:
            for name, path in sorted(archive_inputs.items()):
                info = tarfile.TarInfo(name)
                info.size = path.stat().st_size
                info.mode = 0o644
                info.mtime = 0
                with path.open("rb") as stream:
                    archive.addfile(info, stream)
    encoded_path = destination / "local-evidence.tar.xz.b64"
    encoded_path.write_bytes(base64.encodebytes(archive_path.read_bytes()))
    # Round-trip exact archive bytes and every retained member without extracting files.
    require(base64.decodebytes(encoded_path.read_bytes()) == archive_path.read_bytes(), "Archive encoding mismatch")
    members = []
    with tarfile.open(archive_path, "r:xz") as archive:
        for member in archive.getmembers():
            require(member.isfile() and member.name in archive_inputs, "Unexpected archive member")
            value = hashlib.sha256(archive.extractfile(member).read()).hexdigest()
            require(value == sha(archive_inputs[member.name]), "Archive member hash mismatch")
            members.append({"path": member.name, "sha256": value, "bytes": member.size})
    require(len(members) == len(archive_inputs), "Missing archive member")
    archive_manifest = {"format": "base64 of xz-compressed POSIX tar; regular files only",
                        "base64_file": encoded_path.name, "base64_sha256": sha(encoded_path),
                        "archive_sha256": sha(archive_path), "archive_bytes": archive_path.stat().st_size,
                        "roundtrip_members_verified": True, "members": members}
    dump(destination / "evidence-manifest.json", archive_manifest)
    direct_names = {"ImbalancedChen.Part3LongSlotDistribution", "ImbalancedChen.BoundaryArbitraryLog"}
    direct = [{**m, "sha256": {p: common["sha256"][p] for p in [m["source"]] + m["parts"]}}
              for m in common["modules"] if m["module"] in direct_names]
    result = {"status": "PASSED_SCOPED_LONG_SLOT_NORMALIZATION", "recorded_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "branch": "chatgpt/chen-p3-distribution", "parent_checkpoint": trees["branch_commit"],
              "common_proof_baseline": "1a80c1bcce67886f699d097fc37fd245cd3620bf", "upstream_fixed_commit": trees["p0_commit"],
              "target": TARGET, "source_sha256": SOURCE_HASH, "accepted_upstream_source_sha256": UPSTREAM_HASH,
              "target_object_parts_sha256": object_identity, "direct_imports": direct,
              "compile_method": "Unchanged P0 driver: stock pinned Lake, official Lean.Elab.runFrontend, trustLevel=0, warningAsError=true",
              "kernel_scope": "Original leanchecker --verbose replays the target production module over its fixed imports; no --fresh full-import replay claimed",
              "owned_axiom_scope": "All defining-module constants, matched bidirectionally with serialized constNames, including private/generated kernel declarations",
              "owned_declaration_count": 2, "serialized_inventory": serialized,
              "compiler_confirmed_types": "compiler-declarations.json", "compiler_readable_types": "COMPILER_TYPES.md",
              "cross_gate_identity_checks": {"same_production_source": True, "same_strict_compile_object_used_by_replay_and_audit": True,
                                             "all_common_import_sources_and_objects_equal": True, "actual_lean_import_paths_match": True},
              "production_import_module_count": len(common["modules"]), "production_import_source_and_object_file_count": len(common["sha256"]),
              "actual_audit_import_module_count": audit_gate["actual_lean_import_count"],
              "selected_gates": selected, "all_actual_attempts": attempts,
              "evidence": {"manifest": "evidence-manifest.json", "archive": encoded_path.name,
                           "manifest_sha256": sha(destination/"evidence-manifest.json"), "archive_base64_sha256": sha(encoded_path)},
              "scope_guard": guard, "full_part3_gate_modified": False, "full_repository_build_executed": False,
              "receiving_part": "Part 0", "remaining_work": ["Actual rough/prime long slots", "Long-variable phases", "Brun/Mellin costs",
                "Actual manuscript/policy parameters imply M*D <= N^theta with theta < 1"],
              "new_analysis_scope_closed": "Exactly the two existing unfiltered, zero-phase integer long-slot normalization theorems"}
    dump(destination / "receipt.json", result)
    print(json.dumps({"status": result["status"], "declarations": 2, "archive_bytes": archive_path.stat().st_size,
                      "retained_files": len(members), "receipt": str(destination/"receipt.json")}), flush=True)


if __name__ == "__main__":
    main()
