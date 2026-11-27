#!/usr/bin/env python3
"""Independent, local-only Cell05 AllRowGaps evidence readback.

Reads archive bytes and repository sources. Does not import an archived helper,
run Lean, execute an old workflow/test, write a source, or contact a service.
The only output mutation is READBACK_REVIEW.json beside this script.
"""
from __future__ import annotations

import hashlib
import io
import json
import math
from pathlib import Path, PurePosixPath
import re
import subprocess
import tarfile
from datetime import datetime, timezone


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
BASE = HERE.parent
MODULE = "ImbalancedChen.P2OriginalSaving19Cell05AllRowGaps"
SHAPE = "ImbalancedChen.P2OriginalSaving19Geometry05ScalableShape"
STAGE = "/workspace/p26-cell05-all-row-gaps-20261127-v1"
SHAPE_STAGE = "/workspace/p26-cell05-shape-completion-20261127-v1"
RECOVERY_STAGE = "/workspace/p26-cell05-runtime-recovery-20261127-v2"
TOOL = "tools/p26/cell05-all-row-gaps-20261127"
MODES = ("normal", "kernel", "owned")
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
SCOPE = "Cell05 all 56 original concrete geometry rows: positive gap sum and stored mean-gap equality only"
PURE = {"ImbalancedChen.P2OriginalSaving19RowNumericsPure", "ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure"}
CHECKS: list[dict] = []
REPORT: dict = {
    "schema": "cell05_all_row_gaps_independent_local_readback_v1",
    "reviewed_at_utc": datetime.now(timezone.utc).isoformat(),
    "reviewer": "/root/p26_evidence_readback",
    "method": "Independent Python byte/hash/JSON/source review; no archived code executed",
    "cloud_calls": 0, "Lean_commands": 0, "old_proof_commands_replayed": 0,
    "old_tests_replayed": 0, "repository_source_edits": 0,
    "P2_6_complete": False,
}


def require(ok, label):
    if not ok:
        CHECKS.append({"check": label, "passed": False})
        raise AssertionError(label)


def passed(label, **details):
    CHECKS.append({"check": label, "passed": True, **details})


def pin(body):
    return {"bytes": len(body), "sha256": hashlib.sha256(body).hexdigest()}


def same(a, b):
    return all(a[k] == b[k] for k in ("bytes", "sha256"))


def load(body):
    return json.loads(body)


def tar_members(body, label):
    with tarfile.open(fileobj=io.BytesIO(body), mode="r:*") as stream:
        members = stream.getmembers()
        names = [m.name for m in members]
        require(len(names) == len(set(names)), label + " duplicate members")
        for m in members:
            p = PurePosixPath(m.name)
            require(m.isfile() and not p.is_absolute() and ".." not in p.parts,
                    label + " safe regular member " + m.name)
        return {m.name: stream.extractfile(m).read() for m in members}


def manifest_check(data, label):
    manifest = load(data["EXPORT_MANIFEST.json"])
    rows = manifest["members"]
    names = [r["member"] for r in rows]
    require(len(names) == len(set(names)), label + " manifest duplicates")
    require(set(data) == set(names) | {"EXPORT_MANIFEST.json"}, label + " exact manifest membership")
    for row in rows:
        require(pin(data[row["member"]]) == {k: row[k] for k in ("bytes", "sha256")},
                label + " member identity " + row["member"])
    passed(label + " exact manifest and every member hash", archive_members=len(data), hashed_members=len(rows))
    return manifest


def fp(data, member, stage=STAGE):
    return {"path": stage + "/" + member, **pin(data[member])}


def pointer(value, path):
    require(path.startswith("/"), "absolute JSON pointer")
    for raw in path.split("/")[1:]:
        key = raw.replace("~1", "/").replace("~0", "~")
        value = value[int(key)] if isinstance(value, list) else value[key]
    return value


def imports(body):
    return re.findall(r"^import (ImbalancedChen\.[\w.]+)$", body.decode(), re.M)


def source_body(module):
    relative = module.replace(".", "/") + ".lean"
    p = REPO / relative
    if p.is_file():
        return p.read_bytes(), {"path": relative, "read_from": "working_tree"}
    # Read-only support for an intentionally sparse checkout. No checkout/write.
    result = subprocess.run(["git", "show", "HEAD:" + relative], cwd=REPO, capture_output=True, check=True)
    return result.stdout, {"path": relative, "read_from": "HEAD_git_blob"}


def check_owned(data, context, module, mode_result, expected_count):
    raw = data["verification/owned.log"].decode()
    tags = {k: [] for k in ("IMPORTS", "INVENTORY", "DECL", "COMPLETE")}
    for line in raw.splitlines():
        require(line.startswith("P26_GEOMETRY01_AUDIT_"), "owned log recognized prefix")
        marker, value = line.split(" ", 1)
        kind = marker.removeprefix("P26_GEOMETRY01_AUDIT_")
        require(kind in tags, "owned log recognized record")
        tags[kind].append(load(value))
    require(all(len(tags[k]) == 1 for k in ("IMPORTS", "INVENTORY", "COMPLETE")), "owned singleton records")
    inventory, complete, declarations = tags["INVENTORY"][0], tags["COMPLETE"][0], tags["DECL"]
    names = [d["name"] for d in declarations]
    serialized, environment = inventory["serialized"], inventory["environment"]
    require(all(len(x) == len(set(x)) == expected_count for x in (names, serialized, environment)),
            "owned exact unique declaration counts")
    require(set(names) == set(serialized) == set(environment), "owned serialized/environment/record equality")
    require(inventory["module"] == module and complete == {"module": module, "count": expected_count},
            "owned complete marker module/count")
    axioms = set()
    for d in declarations:
        require(d["module"] == module, "owned declaring module " + d["name"])
        require(all(d[k] is False for k in ("unsafe", "partial", "axiom")), "owned safe nonaxiom " + d["name"])
        require(isinstance(d["type"], str) and d["type"] and "⋯" not in d["type"], "owned untruncated type " + d["name"])
        require(set(d["axioms"]) <= ALLOWED, "owned allowed transitive axioms " + d["name"])
        axioms.update(d["axioms"])
    imported = tags["IMPORTS"][0]
    require(len(imported) == len(set(imported)), "owned imported-module uniqueness")
    project = {m for m in imported if m.startswith("ImbalancedChen.")}
    target = next(t for t in context["targets"] if t["module"] == module)
    require(project == set(target["transitive_dependencies"]) | {module}, "owned exact project import closure")
    owned = load(data["verification/owned-declarations.json"])
    expected = {"module": module, "owned_declaration_count": expected_count,
                "axioms_union": sorted(axioms), "inventory": inventory,
                "declarations": declarations, "complete": complete}
    require(owned == expected, "owned retained JSON equals reconstructed raw log")
    require(mode_result["owned_declaration_count"] == expected_count, "owned result count")
    require(mode_result["owned_declarations"] == fp(data, "verification/owned-declarations.json", context["stage"]),
            "owned result JSON reference")
    return owned, imported


def run_review():
    archive = (BASE / "gaps-evidence.tar.xz").read_bytes()
    expected_archive = {"bytes": 1465240, "sha256": "c3bda60afa81971e55949866cf99779f063f55acdfd326ee556ff431c51546a5"}
    require(pin(archive) == expected_archive, "original exported archive identity")
    retained_body = (BASE / "RETAINED_VERIFY.json").read_bytes()
    require(pin(retained_body)["sha256"] == "b46709837162072a219fee9874cc01912dcd0dbbe64975c873561407838ed5db",
            "30-page reconstructed retained verification report identity")
    REPORT["archive"] = {"path": str((BASE / "gaps-evidence.tar.xz").relative_to(REPO)), **pin(archive)}
    REPORT["retained_verification_report"] = pin(retained_body)
    outer = tar_members(archive, "AllRowGaps")
    export = manifest_check(outer, "AllRowGaps")
    run = load(outer["verification/RUN.json"])
    success = load(outer["verification/SUCCESS.json"])
    index = load(outer["REUSE_INDEX.json"])
    config = load(outer[TOOL + "/CONFIG.json"])
    workflow = load(outer[TOOL + "/WORKFLOW_MANIFEST.json"])
    target_source = "project/" + MODULE.replace(".", "/") + ".lean"
    target_object = "objects/" + MODULE.replace(".", "/") + ".olean"
    audit_source = TOOL + "/owned-audits/" + MODULE.split(".")[-1] + ".lean"
    target_pin, object_pin, audit_pin = (fp(outer, p) for p in (target_source, target_object, audit_source))

    require(run["stage"] == STAGE and run["cwd"] == STAGE + "/project", "RUN stage/cwd")
    require(run["schema"] == "cell05_all_row_gaps_run_v1", "RUN schema")
    require(len(run["targets"]) == 1 and run["targets"][0]["module"] == MODULE, "one exact owner")
    require(run["targets"][0]["source"] == target_pin and run["targets"][0]["audit"] == audit_pin,
            "RUN target source and audit byte binding")
    require(config["stage"] == STAGE and same(config["source"], target_pin) and same(config["audit"], audit_pin),
            "CONFIG target identity")
    require(run["targets"][0]["project_imports"] == imports(outer[target_source]) == [SHAPE, "ImbalancedChen.P2OriginalSaving19RowNumericsPure"],
            "exact direct import scope")
    require(run["workflow_sha256"] == pin(outer[TOOL + "/WORKFLOW_MANIFEST.json"])["sha256"], "RUN workflow manifest hash")
    rows = workflow["files"]
    require(len(rows) == len({r["relative_path"] for r in rows}) == 7, "workflow seven unique pinned files")
    for row in rows:
        member = TOOL + "/" + row["relative_path"]
        require(same(pin(outer[member]), row), "workflow member hash " + member)
    expected_workflow_names = {TOOL + "/WORKFLOW_MANIFEST.json"} | {TOOL + "/" + r["relative_path"] for r in rows}
    require({p["path"].removeprefix(STAGE + "/") for p in run["workflow_files"]} == expected_workflow_names,
            "RUN exact workflow file inventory")
    for p in run["workflow_files"]:
        member = p["path"].removeprefix(STAGE + "/")
        require(p == fp(outer, member), "RUN workflow fingerprint " + member)
        require((REPO / member).read_bytes() == outer[member], "repository workflow bytes " + member)
    require((REPO / (MODULE.replace(".", "/") + ".lean")).read_bytes() == outer[target_source], "repository target source bytes")
    require(not re.search(r"\b(sorry|admit|native_decide|axiom|unsafe|partial)\b", outer[target_source].decode()),
            "target source forbidden proof features absent")
    passed("target source, audit, workflow manifest, RUN and current repository match", workflow_files=8)

    # The nested predecessor is a real preserved archive, not a substituted summary.
    shape_archive_member = "predecessor/exports/shape-evidence.tar.xz"
    require(same(pin(outer[shape_archive_member]), config["shape"]["archive"]), "nested Shape archive CONFIG pin")
    shape = tar_members(outer[shape_archive_member], "Shape predecessor")
    shape_export = manifest_check(shape, "Shape predecessor")
    old = load(shape["verification/RUN.json"])
    old_success = load(shape["verification/SUCCESS.json"])
    old_index = load(shape["COMBINED_INDEX.json"])
    require(run["shape_stage"] == SHAPE_STAGE == old["stage"], "predecessor stage agreement")
    expected_predecessors = [config["shape"][k] for k in ("driver", "configuration", "recovery_binding", "run", "success", "index", "archive")]
    require(run["predecessor_artifacts"] == expected_predecessors, "RUN exact seven predecessor artifacts")
    for p in expected_predecessors:
        member = p["path"].removeprefix(SHAPE_STAGE + "/")
        require(fp(outer, "predecessor/" + member)["bytes"] == p["bytes"] and
                fp(outer, "predecessor/" + member)["sha256"] == p["sha256"], "predecessor artifact hash " + member)
        if member != "exports/shape-evidence.tar.xz":
            require(outer["predecessor/" + member] == shape[member], "nested/outer predecessor exact duplicate " + member)
    require(run["shape_run"] == fp(shape, "verification/RUN.json", SHAPE_STAGE) == old_success["run"], "predecessor RUN references")
    require(run["shape_success"] == fp(shape, "verification/SUCCESS.json", SHAPE_STAGE) == old_index["shape_success"],
            "predecessor SUCCESS references")
    require(old_success["accepted_targets"] == shape_export["accepted_targets"] == 1 and
            old_success["accepted_steps"] == shape_export["accepted_steps"] == 3, "predecessor one owner three steps")
    require(old_index["prefix8_accepted_targets"] == 8 and old_index["prefix8_accepted_steps"] == 24 and
            old_index["shape_accepted_targets"] == 1 and old_index["shape_accepted_steps"] == 3 and
            old_index["distinct_owners"] == 9 and old_index["distinct_step_acceptances"] == 27, "predecessor index exact separate contexts")
    require(old_index["prefix8"] == fp(shape, "PREFIX8_VALIDATED.json", SHAPE_STAGE), "predecessor prefix8 pointer")
    require(old_success["object"] == fp(shape, "objects/" + SHAPE.replace(".", "/") + ".olean", SHAPE_STAGE), "predecessor target object bytes")
    for r in old_success["records"]:
        require(r["accepted"] == fp(shape, "verification/" + r["mode"] + "-accepted.json", SHAPE_STAGE), "predecessor accepted pointer")
        acc = load(shape["verification/" + r["mode"] + "-accepted.json"])
        for key, member in (("run", "verification/RUN.json"), ("command", "verification/" + r["mode"] + "-command.json"),
                            ("result", "verification/" + r["mode"] + "-result.json"), ("launch_witness", "launch-witnesses/" + r["mode"] + ".json")):
            require(acc[key] == fp(shape, member, SHAPE_STAGE), "predecessor receipt identity " + r["mode"] + " " + key)
        require(acc["object"] == old_success["object"], "predecessor accepted object")
    recovery = load(shape["recovery/CERTIFICATE.json"])
    for field, member in (("recovery_certificate", "CERTIFICATE.json"), ("runtime_guard", "CURRENT_RUNTIME_GUARD.json"), ("recovery_history", "HISTORICAL_VALIDATION.json")):
        p = {"path": RECOVERY_STAGE + "/" + member, **pin(shape["recovery/" + member])}
        require(run[field] == old[field] == p, "recovery chain pin " + field)
    require(recovery["runtime_identity"] == run["runtime"] == old["runtime"], "recovered compiler and mathlib identity")
    require(recovery["status"] == "PASS_EXPLICIT_RUNTIME_RECOVERY" and recovery["current_runtime_guard"] == run["runtime_guard"],
            "explicit runtime recovery certificate")
    require(recovery["history"] == run["recovery_history"] and recovery["old_Lean_commands"] == 0, "recovery history and zero proof replay")
    for value in (run, old, recovery, export, shape_export):
        require(value["original_live_guard_validator_passed"] is False, "original live guard not retroactively claimed")
    require(recovery["original_evidence_rewritten"] is False and recovery["historical_loaded_runtime_inventory_claimed"] is False,
            "recovery historical boundary unchanged")
    for p in recovery["protocol_files"]:
        member = "recovery/" + p["path"].removeprefix(RECOVERY_STAGE + "/")
        require(same(pin(shape[member]), p), "recovery protocol file hash " + member)
    require(export["recovery_certificate"] == shape_export["recovery_certificate"] == run["recovery_certificate"] and
            export["runtime_guard"] == shape_export["runtime_guard"] == run["runtime_guard"], "export runtime/recovery pins")
    passed("predecessor fields, duplicate bodies, object, receipt pins and recovery boundary")
    REPORT["predecessor"] = {"archive": pin(outer[shape_archive_member]), "archive_members": len(shape),
                             "owners_in_combined_index": 9, "acceptances_in_combined_index": 27,
                             "historical_guard_retroactively_passed": False}

    # Match all source/object identities to the old accepted contexts, keeping
    # original and installed locations separate.
    deps = run["dependencies"]
    require(len(deps) == 128 and MODULE not in deps and len(old["dependencies"]) == 125, "128 old suppliers / 129 project closure")
    require(set(deps) == set(old["dependencies"]) | {SHAPE} | PURE, "exact predecessor/pure supplier join")
    require(run["targets"][0]["transitive_dependencies"] == sorted(deps), "target dependency list complete")
    for module, row in old["dependencies"].items():
        require(deps[module]["source"] == row["installed_source"] and deps[module]["object"] == row["installed_object"],
                "old supplier exact source/object provenance " + module)
    require(deps[SHAPE]["source"] == old["targets"][0]["source"] and deps[SHAPE]["object"] == old_success["object"],
            "Shape source/object is new target's exact supplier")
    source_records = []
    source_graph = {}
    for module, d in deps.items():
        for kind, folder, suffix in (("source", "project", ".lean"), ("object", "objects", ".olean")):
            require(same(d[kind], d["installed_" + kind]), "installed supplier identity " + module + " " + kind)
            require(d["installed_" + kind]["path"] == STAGE + "/" + folder + "/" + module.replace(".", "/") + suffix,
                    "canonical installed supplier path " + module + " " + kind)
        body, source_record = source_body(module)
        require(same(pin(body), d["source"]), "repository supplier source hash " + module)
        source_record.update(module=module, **pin(body))
        source_records.append(source_record)
        source_graph[module] = imports(body)
    seen = set()
    def visit(module):
        if module in seen:
            return
        require(module in source_graph, "provided transitive source " + module)
        seen.add(module)
        for dep in source_graph[module]:
            visit(dep)
    for module in imports(outer[target_source]):
        visit(module)
    require(seen == set(deps), "repository source graph exactly 128 suppliers")
    passed("all 128 supplier source hashes and all 128 source/object provenance pairs match", repository_sources=128,
           working_tree_sources=sum(r["read_from"] == "working_tree" for r in source_records))
    REPORT["repository_supplier_sources"] = source_records

    # The pure transport preserves the original 4 normal/kernel authorities.
    transport = load(outer["inputs/pure2/TRANSPORT.json"])
    require(same(pin(outer["inputs/pure2/TRANSPORT.json"]), config["pure2_transport"]), "pure transport config hash")
    require(transport["module_count"] == 2 and len(transport["files"]) == 16, "pure transport exact counts")
    pure_member_names = {"inputs/pure2/" + r["relative_path"] for r in transport["files"]} | {"inputs/pure2/TRANSPORT.json"}
    require(pure_member_names == {n for n in outer if n.startswith("inputs/pure2/")}, "pure transport exact archive members")
    manifest = load(outer["inputs/pure2/MANIFEST.json"])
    original_entries = {r["archive_path"]: r for r in manifest["files"]}
    require(len(original_entries) == len(manifest["files"]), "pure original manifest uniqueness")
    origins = {}
    for row in transport["files"]:
        member = "inputs/pure2/" + row["relative_path"]
        require(same(pin(outer[member]), row), "pure transport member pin " + member)
        if row["relative_path"] != "MANIFEST.json":
            require(original_entries[row["relative_path"]] == row["original_manifest_row"] and
                    same(row, row["original_manifest_row"]), "pure original manifest authority " + member)
            origins[row["original_manifest_row"]["original_path"]] = member
    require(same(pin(outer["inputs/pure2/MANIFEST.json"]), transport["original_manifest"]), "pure original manifest pin")
    pure_audit = load(outer["inputs/pure2/AUDIT.json"])
    runtime = load(outer["inputs/pure2/RUNTIME.json"])
    require(pure_audit["failures"] == [] and pure_audit["source_object_hashes_match"] is True and
            pure_audit["receipt_metadata_not_rewritten"] is True and pure_audit["runtime"] == runtime, "pure original audit boundary")
    require(runtime["mathlib_pin"] == run["runtime"]["mathlib_commit"] and runtime["lean_commit"] in run["runtime"]["lean_version"],
            "pure runtime version and commit join")
    bins = {Path(p["path"]).name: p for p in runtime["runtime_files_observed"]}
    require(same(bins["lean"], run["runtime"]["lean_binary"]) and same(bins["leanchecker"], run["runtime"]["leanchecker_binary"]),
            "pure compiler/checker byte identity join")
    pure_original = {r["module"]: r for r in pure_audit["modules"] if r["module"] in PURE}
    require(set(pure_original) == PURE and transport["original_modules"] == [pure_original[r["module"]] for r in transport["original_modules"]],
            "pure original selected module records")
    reuse = load(outer["SUPPLIER_REUSE.json"])
    require(run["pure2_reuse"] == fp(outer, "SUPPLIER_REUSE.json") and len(reuse["records"]) == 4, "pure reuse bound by RUN")
    require(reuse["frozen_files"] == run["pure2_frozen_files"], "pure frozen file inventory equals RUN")
    for p in reuse["frozen_files"]:
        require(p == fp(outer, p["path"].removeprefix(STAGE + "/")), "pure frozen file reference")
    pure_records = []
    for module in sorted(PURE):
        m = pure_original[module]
        require(m["acceptance_boundary"] == "DIRECT_NORMAL_AND_KERNEL_RECEIPTS_VERIFIED" and set(m["receipts"]) == {"normal", "kernel"},
                "pure original normal/kernel acceptance only")
        for kind, folder, suffix in (("source", "sources", ".lean"), ("object", "objects", ".olean")):
            member = "inputs/pure2/" + folder + "/" + module.replace(".", "/") + suffix
            require(deps[module][kind] == reuse["dependencies"][module][kind] == fp(outer, member), "pure new provenance exact " + module + " " + kind)
            require(same(pin(outer[member]), m[kind]), "pure original source/object body " + module + " " + kind)
        require(m["object_siblings"] == [], "pure no additional object siblings")
        for mode in ("normal", "kernel"):
            authority = m["receipts"][mode]
            prior = authority["prior_hash_pin"]
            require(pointer(load(outer[origins[prior["manifest"]]]), prior["pointer"]) == authority["receipt"],
                    "pure original closure pointer " + module + " " + mode)
            member = origins[authority["receipt"]["path"]]
            result = load(outer[member])
            require(same(pin(outer[member]), authority["receipt"]), "pure original receipt byte hash")
            require(result["module"] == module and result["mode"] == mode and result["attempt"] == "namespace-v2" and
                    result["status"] == "succeeded" and type(result["exit_code"]) is int and result["exit_code"] == 0 and
                    result["input_before"] == result["input_after"] and result["Mathlib_pin"] == runtime["mathlib_pin"], "pure original result semantics")
            require(same(result["source"], m["source"]) and same(result["object"], m["object"]), "pure receipt source/object identity")
            expected_argv = ([bins["lean"]["path"], "-j1", "-DmaxRecDepth=1000000", "-DmaxHeartbeats=0", "-o", result["object"]["path"], result["source"]["path"]]
                             if mode == "normal" else [bins["leanchecker"]["path"], "--verbose", module])
            require(result["argv"] == expected_argv, "pure original flags preserved")
            require(result["cwd"] == str(Path(result["source"]["path"]).parents[1]), "pure original cwd")
            require(result["LEAN_PATH"].split(":")[1:] == [p["path"] for p in runtime["original_external_LEAN_PATH_roots"]], "pure original external roots")
            expected_deps = ({"ImbalancedChen.P2OriginalSaving19ArchiveSchema", "ImbalancedChen.P2OriginalSaving19SourceJson", "ImbalancedChen.P2OriginalLogMomentQ96ArithmeticPure"}
                             if module.endswith("RowNumericsPure") else set())
            require({d["module"] for d in result["dependencies"]} == expected_deps and len(result["dependencies"]) == len(expected_deps), "pure exact original dependency set")
            for dep in result["dependencies"]:
                current = deps[dep["module"]]
                require(same(dep["source"], current["source"]) and same(dep["object"], current["object"]), "pure/Shape shared source/object join")
            log_member = origins[result["log"]["path"]]
            require(same(pin(outer[log_member]), result["log"]), "pure original log reference")
            log = outer[log_member].decode()
            require(not re.search(r"(?:^|:\s*|\s)(?:warning|error|fatal error):", log, re.I | re.M), "pure original successful diagnostic-free log")
            if mode == "kernel":
                require(log.strip() == "replaying " + module, "pure kernel log target")
            elif module.endswith("Q96ArithmeticPure"):
                require(log == "", "pure original empty normal log")
            else:
                match = re.fullmatch(r"'ImbalancedChen.P2OriginalSaving19RowNumericsPure.rowDataChecksFor_iff_originalForm' depends on axioms: \[([^\]]*)\]\s*", log)
                require(match is not None and {s.strip() for s in match[1].split(",")} <= ALLOWED, "pure original normal axiom boundary")
            pure_records.append({"module": module, "mode": mode, "original_receipt": authority["receipt"],
                                 "current_receipt": fp(outer, member), "original_log": result["log"], "current_log": fp(outer, log_member)})
    require(pure_records == reuse["records"], "four exact reconstructed reuse records")
    for k in ("old_normal_commands_replayed", "old_kernel_commands_replayed", "new_Lean_commands"):
        require(transport[k] == 0, "pure zero command claim " + k)
    for k in ("historical_explicit_trust_zero_claimed", "historical_loaded_runtime_inventory_claimed", "new_supplier_owned_audits_claimed", "P2_6_complete"):
        require(transport[k] is False, "pure non-retroactive scope " + k)
    require(reuse["accepted_old_normal_kernel_records"] == 4 and reuse["new_supplier_owned_audits"] == 0 and reuse["old_proof_commands"] == 0 and
            reuse["historical_explicit_trust_zero_claimed"] is False and reuse["historical_loaded_inventory_claimed"] is False, "pure reuse exact old scope")
    input_path = BASE.parent / "inputs/pure2-original-evidence.tar.xz"
    pure_export = load((BASE.parent / "inputs/PURE2_EXPORT.json").read_bytes())
    require(same(pin(input_path.read_bytes()), pure_export["archive"]), "retained pure input archive identity")
    pure_input = tar_members(input_path.read_bytes(), "pure original transport")
    require(set(pure_input) == {n.removeprefix("inputs/pure2/") for n in pure_member_names}, "pure input/output exact membership")
    require(all(outer["inputs/pure2/" + n] == b for n, b in pure_input.items()), "pure input/output exact bytes")
    passed("two original pure suppliers: all 17 transported bodies and four original normal/kernel records")

    # Independently reconstruct each new command and every directed reference.
    previous = None
    prior_finish = None
    records = []
    results = {}
    for mode in MODES:
        command_member, result_member, accepted_member, log_member, witness_member = (
            "verification/" + mode + "-command.json", "verification/" + mode + "-result.json",
            "verification/" + mode + "-accepted.json", "verification/" + mode + ".log", "launch-witnesses/" + mode + ".json")
        command, result, accepted, witness = (load(outer[p]) for p in (command_member, result_member, accepted_member, witness_member))
        common = [run["runtime"]["lean_binary"]["path"], "--trust=0", "-DwarningAsError=true", "-j1", "-M12288", "-DmaxRecDepth=1000000", "-DmaxHeartbeats=0"]
        argv = (common + ["-o", object_pin["path"], MODULE.replace(".", "/") + ".lean"] if mode == "normal" else
                [run["runtime"]["leanchecker_binary"]["path"], "--verbose", MODULE] if mode == "kernel" else common + [audit_pin["path"]])
        expected = {"schema": "cell05_all_row_gaps_command_v1", "run": fp(outer, "verification/RUN.json"), "module": MODULE, "mode": mode,
                    "previous_accepted": previous, "argv": argv, "cwd": run["cwd"], "environment": run["environment"],
                    "source": target_pin, "audit_source": audit_pin, "dependencies": deps,
                    "object_before": None if mode == "normal" else object_pin, "started_unix": command["started_unix"]}
        require(command == expected, mode + " exact frozen command")
        require(witness == {"schema": "cell05_all_row_gaps_launch_v1", "module": MODULE, "mode": mode,
                            "run": fp(outer, "verification/RUN.json"), "command": fp(outer, command_member)}, mode + " exact durable witness")
        for k in ("run", "module", "mode", "source", "audit_source", "dependencies"):
            require(result[k] == command[k], mode + " command/result field " + k)
        for k, member in (("command", command_member), ("log", log_member), ("launch_witness", witness_member)):
            require(result[k] == fp(outer, member), mode + " result reference " + k)
        require(result["schema"] == "cell05_all_row_gaps_result_v1" and result["status"] == "succeeded" and
                type(result["exit_code"]) is int and result["exit_code"] == 0 and result["termination_reason"] is None,
                mode + " successful result")
        require(result["object"] == object_pin and object_pin["bytes"] > 0, mode + " same exact target object")
        require(result["started_unix"] == command["started_unix"] and result["finished_unix"] >= result["started_unix"] and
                all(type(result[k]) in (int, float) and math.isfinite(result[k]) and result[k] > 0 for k in ("started_unix", "finished_unix", "elapsed_seconds")),
                mode + " valid real timing")
        require(result["elapsed_seconds"] <= run["wall_limit_seconds"] and type(result["peak_rss_bytes"]) is int and
                0 <= result["peak_rss_bytes"] <= run["rss_limit_bytes"], mode + " resource limits")
        require(prior_finish is None or command["started_unix"] >= prior_finish, mode + " sequential command order")
        prior_finish = result["finished_unix"]
        require(accepted == {"schema": "cell05_all_row_gaps_accepted_v1", "status": "accepted", "run": fp(outer, "verification/RUN.json"),
                             "module": MODULE, "mode": mode, "launch_witness": fp(outer, witness_member), "command": fp(outer, command_member),
                             "result": fp(outer, result_member), "object": object_pin}, mode + " exact accepted seal")
        log = outer[log_member].decode()
        require(not re.search(r"(?:^|:\s*|\s)(?:warning|error|fatal error):", log, re.I | re.M), mode + " successful diagnostic-free log")
        if mode == "kernel":
            require(log.strip() == "replaying " + MODULE, "new kernel exact target replay")
        previous = fp(outer, accepted_member)
        records.append({"module": MODULE, "mode": mode, "accepted": previous})
        results[mode] = result
    passed("normal/kernel/owned command-result-log-accepted-witness reference chains", accepted_targets=1, accepted_steps=3)
    REPORT["new_steps"] = [{"mode": m, "status": results[m]["status"], "elapsed_seconds": results[m]["elapsed_seconds"],
                            "peak_rss_bytes": results[m]["peak_rss_bytes"], "object": results[m]["object"]} for m in MODES]

    # Printing twenty chosen names is distinct from the complete owned inventory.
    normal = outer["verification/normal.log"].decode()
    matches = list(re.finditer(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])\s*", normal))
    print_tokens = re.findall(r"^#print axioms (\w+)$", outer[target_source].decode(), re.M)
    require("".join(m[0] for m in matches) == normal and len(matches) == len(print_tokens) == 20 and len(set(print_tokens)) == 20,
            "normal exact twenty axiom print statements")
    printed_names = [m[1] for m in matches]
    print_axioms = {x.strip() for m in matches for x in (m[2] or "").split(",") if x.strip()}
    require(print_axioms <= ALLOWED and results["normal"]["printed_declarations"] == printed_names and
            results["normal"]["printed_axioms"] == sorted(print_axioms), "normal exact axiom print facts")
    owned, imported = check_owned(outer, run, MODULE, results["owned"], 31)
    owned_names = {d["name"] for d in owned["declarations"]}
    bindings = []
    for token, display in zip(print_tokens, printed_names):
        public = MODULE + "." + token
        private = bool(re.search(r"^private\s+(?:theorem|def|abbrev)\s+" + re.escape(token) + r"\b", outer[target_source].decode(), re.M))
        pattern = r"_private\." + re.escape(MODULE) + r"\.\d+\." + re.escape(public)
        require(display == public or (private and re.fullmatch(pattern, display)), "printed source token ownership")
        matched = [display] if display in owned_names else [n for n in owned_names if private and display == public and re.fullmatch(pattern, n)]
        require(len(matched) == 1, "printed name unique full-owned binding")
        bindings.append({"printed": display, "owned_name": matched[0]})
    require(results["owned"]["printed_owned_bindings"] == bindings and len({b["owned_name"] for b in bindings}) == 20,
            "twenty raw printed aliases bind uniquely to complete owned names")
    generated = sorted(n for n in owned_names if re.search(r"\._proof_\d+$", n))
    require(len(generated) == 11 and set(generated) == owned_names - {b["owned_name"] for b in bindings}, "all eleven unprinted generated proofs inventoried")
    theorem = next(d for d in owned["declarations"] if d["name"] == MODULE + ".all_row_gaps")
    require(theorem["axioms"] and set(theorem["axioms"]) == ALLOWED, "all_row_gaps exact allowed transitive axiom union")
    REPORT["owned"] = {"owned_declaration_count": 31, "explicit_prints": 20, "generated_declarations": 11,
                       "private_declarations_including_generated": sum(n.startswith("_private.") for n in owned_names),
                       "axioms_union": owned["axioms_union"], "unsafe": 0, "partial": 0, "new_axioms": 0,
                       "full_serialized_environment_and_record_sets_equal": True,
                       "project_imports": len([n for n in imported if n.startswith("ImbalancedChen.")]),
                       "all_imports": len(imported), "generated_names": generated,
                       "all_row_gaps_full_type": theorem["type"]}
    passed("complete owned serialized/environment/records inventory and full types", declarations=31, prints=20, generated=11)

    expected_success = {"schema": "cell05_all_row_gaps_success_v1", "status": "succeeded", "run": fp(outer, "verification/RUN.json"),
                        "accepted_targets": 1, "accepted_steps": 3, "records": records, "object": object_pin,
                        "old_supplier_count": 128, "project_closure_count": 129, "old_proof_commands": 0, "scope": SCOPE, "P2_6_complete": False}
    require(success == expected_success, "exact SUCCESS summary reconstructed")
    expected_index = {"schema": "cell05_all_row_gaps_reuse_index_v1", "shape_success": run["shape_success"], "shape_run": run["shape_run"],
                      "shape_reused_steps": 3, "shape_imported_project_modules": 126, "pure2_reuse": run["pure2_reuse"],
                      "pure2_old_normal_kernel_records": 4, "new_success": fp(outer, "verification/SUCCESS.json"), "new_owners": 1, "new_steps": 3,
                      "new_row_conditions": {"cell": 5, "rows": 56, "RowDataChecksFor_clauses": [3, 5]},
                      "new_complete_ten_clause_rows": 0, "new_Archive_bound_rows": 0, "scope": SCOPE, "P2_6_complete": False}
    require(index == expected_index, "exact reuse/scope summary reconstructed")
    expected_export_fields = {"schema": "cell05_all_row_gaps_export_v1", "accepted_targets": 1, "accepted_steps": 3,
                              "pure2_supplier_object_bodies": 2, "predecessor_archive_included": True, "other_supplier_objects_copied": 0,
                              "new_supplier_owned_audits": 0, "original_live_guard_validator_passed": False,
                              "runtime_guard": run["runtime_guard"], "recovery_certificate": run["recovery_certificate"], "scope": SCOPE, "P2_6_complete": False}
    require({k: v for k, v in export.items() if k != "members"} == expected_export_fields, "exact export scope fields")
    retained = load(retained_body)
    require(retained == {"status": "RETAINED_EVIDENCE_VERIFIED", "success": fp(outer, "verification/SUCCESS.json"),
                         "reuse_index": fp(outer, "REUSE_INDEX.json"), "archive": {"path": STAGE + "/exports/gaps-evidence.tar.xz", **pin(archive)},
                         "accepted_targets": 1, "accepted_steps": 3, "old_proof_commands": 0, "P2_6_complete": False}, "exact retained verify/export report")
    require(run["old_proof_commands"] == 0 and run["scope"] == SCOPE and run["P2_6_complete"] is False, "RUN final scope")
    passed("exact accepted scope and all summaries preserve P2.6 open")
    REPORT["accepted_scope"] = {"module": MODULE, "new_owners": 1, "new_steps": 3, "cell": 5, "original_rows": 56,
                                "ordered_vertices_per_row": 9, "rational_coordinates_per_vertex": 8,
                                "RowDataChecksFor_clauses": [3, 5], "new_row_clause_instances": 112,
                                "new_complete_ten_clause_rows": 0, "new_original_moment_floor_rows": 0,
                                "ownership_integration_or_global_endpoint": False, "P2_6_complete": False}
    REPORT["source_object_match"] = {"target_source": target_pin, "target_object": object_pin,
                                     "supplier_source_object_pairs_bound_to_retained_predecessor_or_original_receipts": 128,
                                     "repository_source_closure_count": 129,
                                     "old_supplier_object_bodies_directly_in_outer": 2,
                                     "old_supplier_object_bodies_in_nested_shape_archive": 1,
                                     "other_old_supplier_objects": "125 fingerprint/provenance pairs reused from accepted predecessor RUN; bodies deliberately not duplicated by this export"}
    REPORT["limitations"] = [
        "Readback authenticates retained bytes, identities and scope. It does not rerun Lean or claim a fresh live-runtime validation.",
        "The export deliberately reuses 125 historical supplier object fingerprints through the accepted Shape context; it is not a standalone 129-object distribution.",
        "The original pure suppliers retain their original normal/kernel contract; no historical explicit trust-zero, loaded-runtime inventory, or new supplier-owned audit is claimed.",
    ]
    REPORT["necessary_remaining_evidence_checks"] = []
    REPORT["findings"] = []
    REPORT["status"] = "PASS_INDEPENDENT_LOCAL_READBACK"


if __name__ == "__main__":
    try:
        run_review()
    except Exception as exc:
        REPORT["status"] = "READBACK_FAILED"
        REPORT["exception"] = repr(exc)
        raise
    finally:
        REPORT["checks"] = CHECKS
        REPORT["review_script"] = pin(Path(__file__).read_bytes())
        (HERE / "READBACK_REVIEW.json").write_text(json.dumps(REPORT, ensure_ascii=False, indent=2) + "\n")
        print(json.dumps({k: REPORT[k] for k in ("status", "archive", "P2_6_complete") if k in REPORT}, ensure_ascii=False))
