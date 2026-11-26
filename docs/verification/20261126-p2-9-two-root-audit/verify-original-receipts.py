#!/usr/bin/env python3
"""Check the original two schema-1 audit receipts after lossless reception.

This is an offline consumer of existing evidence. It never invokes Lean or
changes the original artifacts. The original owned parser is reused by AST.
"""
import ast
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ORIGINAL_ROOT = "/workspace/p2-saving16-20261125"
LEAN = "/workspace/toolchains/lean-4.33.0-rc1-linux/bin/lean"
CHECKER = "/workspace/toolchains/lean-4.33.0-rc1-linux/bin/leanchecker"
SNAPSHOT_SHA = "ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27"
TOOL_PINS = {
    "run_winner9_private_audit.py": "571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5",
    "run_winner9_private_checks.py": "164bc271d8806ed45ebdd71c8f394c4706d7cfdaf4a121b633d738e094bad7ac",
    "inspect_winner9_owner_native.py": "9460e319b2f247b4deb6c4c12ad7b59732bfde939f5dc68e541b4a5714aed90d",
    "winner9_private_audit_template.lean": "2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b",
    "winner9_external_snapshot.py": "a57b658beef42ebfe75ccb09d84f7f1ee7252c289f267396063c93ae5e0bbedf",
}
TARGETS = {
    "ImbalancedChen.ActualPrimePolyhedralTestFunctions": {
        "source_git_blob": "660ce6ca1a0da5065d32bb028509faf629d685fa",
        "source_sha256": "7281ad47406ad7eb48c5f50c24fa037880778aeb59d79a32f25855ab0dd17ad6",
        "object_sha256": "a1ea6cd7acd3317a1e72b9af50c054906b8205d0db2bd78234922745800281da",
        "normal_record_sha256": "8a420f88c97482a5949f51821e748a8fc219f4c135dc0dff91c530fd86fd9e95",
        "closure_signature": "144bbc68377dd301ff84bdd6d404b43686fe2653d7a8599703a2b2b89621def4",
        "owned": 6,
    },
    "ImbalancedChen.AffinePrimeWallReserve": {
        "source_git_blob": "68a60733bdb819724149054b9debf4da390c840a",
        "source_sha256": "185e640b506ee01c6df125cb83c06ff39d8f600e37cc4bf355eeecefe2be559b",
        "object_sha256": "e05ed8e1c69ceadb300c35466c3042675228c420d0508e449b9541ba87f280f4",
        "normal_record_sha256": "f6978a7a65cc13f45d39ee81e5b9ce70ffc06873d346573ed87c3129a43d0899",
        "closure_signature": "9c662c0a50da62b2649208afdf57dbab944d48348912fca2eeb7f11c1b11c91e",
        "owned": 12,
    },
}


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    require(len(sys.argv) == 3, "usage: verifier COMPLETE_DIRECTORY OUTPUT_JSON")
    base = Path(sys.argv[1]).resolve()
    output = Path(sys.argv[2])
    require(not output.exists(), "do not overwrite an earlier root result")
    complete_raw = (base / "COMPLETE_MANIFEST.json").read_bytes()
    complete = json.loads(complete_raw)
    require(complete["schema"] == "p29_two_root_complete_originals_and_preexisting_control_join_v1",
            "wrong complete manifest schema")
    require(complete["original_audit_job"] == "7981839ec960464d913d5ee2b3a18175", "wrong source job")
    checked = {}

    def member(name):
        require(name in complete["files"], "unmanifested evidence: " + name)
        if name not in checked:
            path = base / name
            require(path.resolve().is_relative_to(base) and not path.is_symlink(), "unsafe member")
            raw = path.read_bytes()
            pin = complete["files"][name]
            require(len(raw) == pin["bytes"] and sha(raw) == pin["sha256"], "changed received member: " + name)
            checked[name] = raw
        return checked[name]

    manifest = json.loads(member("manifest.json"))
    require(manifest["original_audit_job"] == complete["original_audit_job"], "wrong original manifest job")
    require(set(manifest["roots"]) == set(TARGETS), "wrong roots")
    require(manifest["roots"] == complete["roots"], "root index changed during local join")
    for name, pin in manifest["files"].items():
        require(complete["files"][name] == {"bytes": pin["bytes"], "sha256": pin["sha256"]},
                "original/complete manifest mismatch: " + name)
    require(manifest["external_snapshot"] == {
        "member": "external/EXTERNAL_SNAPSHOT.json", "sha256": SNAPSHOT_SHA, "bytes": 20904189},
        "wrong external snapshot identity")
    # The reviewed complete receiver verifies every member, including this large
    # snapshot. Its actual contents are inspected once by the input-map owner.
    require(complete["files"]["external/EXTERNAL_SNAPSHOT.json"] == {
        "bytes": 20904189, "sha256": SNAPSHOT_SHA}, "snapshot missing from complete archive")
    normal_raw = member("lineage/SELECTED_ORIGINAL_NORMAL_RECORDS.json")
    require(sha(normal_raw) == "88f5f492ccae8e0fa9ddee189559bb10d1c3cd1dea589486286a5eb6d2a8f78d",
            "wrong original normal-record document")
    normals = json.loads(normal_raw)

    tools = {name: member("original-tools/" + name) for name in TOOL_PINS}
    require(all(sha(tools[n]) == h for n, h in TOOL_PINS.items()), "original tool changed")
    tree = ast.parse(tools["run_winner9_private_audit.py"].decode())
    selected = [n for n in tree.body if isinstance(n, ast.FunctionDef)
                and n.name in {"require", "parse_audit", "replay_context"}]
    require({n.name for n in selected} == {"require", "parse_audit", "replay_context"}, "missing original parser")
    namespace = {"Path": Path, "json": json, "Counter": Counter, "AXIOMS": ALLOWED_AXIOMS}
    exec(compile(ast.Module(body=selected, type_ignores=[]), "<original-winner9-read-only-parser>", "exec"), namespace)
    parser_ast_sha = sha(ast.dump(ast.Module(body=selected, type_ignores=[]), include_attributes=False).encode())
    template = tools["winner9_private_audit_template.lean"].decode()

    def original_member(path):
        path = Path(path)
        relative = path.relative_to(ORIGINAL_ROOT).as_posix() if path.is_absolute() else path.as_posix()
        require(".." not in Path(relative).parts, "unsafe original reference")
        return "project/" + relative

    results = {}
    for module, pin in TARGETS.items():
        root_index = manifest["roots"][module]
        normal = normals[module]
        row_bytes = member(root_index["canonical_normal_record_member"])
        require(row_bytes == canonical(normal) and sha(row_bytes) == pin["normal_record_sha256"], "wrong canonical normal")
        require(normal["module"] == module and normal["exit_code"] == 0 and normal["new_strict_compile"] is True,
                "wrong normal status")
        require(normal["source_sha256"] == pin["source_sha256"]
                and normal["object_sha256"] == pin["object_sha256"]
                and normal["closure_signature"] == pin["closure_signature"], "normal identities differ")
        require(member(root_index["normal_log_member"]) == b"", "strict normal log was not empty")
        source = member(root_index["source_member"])
        obj = member(root_index["object_member"])
        require(sha(source) == pin["source_sha256"] and sha(obj) == pin["object_sha256"], "source/object mismatch")
        require(hashlib.sha1(b"blob " + str(len(source)).encode() + b"\0" + source).hexdigest()
                == pin["source_git_blob"], "selected source Git identity mismatch")

        raw_receipt = member(root_index["latest_receipt_member"])
        require(raw_receipt == member(root_index["attempt_receipt_member"]), "latest/attempt receipts differ")
        require(sha(raw_receipt) == root_index["receipt_sha256"], "receipt index mismatch")
        receipt = json.loads(raw_receipt)
        require(receipt["schema"] == 1 and receipt["module"] == module and receipt["accepted"] is True,
                "wrong schema/module/accepted status")
        for key in ["source_sha256", "object_sha256"]:
            require(receipt[key] == pin[key], "wrong per-module receipt " + key)
        require(receipt["compile_closure_signature"] == pin["closure_signature"], "wrong compilation closure")
        frozen = receipt["input_snapshot"]
        require(sha(canonical(frozen)) == receipt["input_sha256"] == root_index["input_sha256"], "input digest mismatch")
        require(frozen["driver_sha256"] == TOOL_PINS["run_winner9_private_audit.py"]
                and frozen["template_sha256"] == TOOL_PINS["winner9_private_audit_template.lean"], "input tool mismatch")
        require(frozen["lean_binary_sha256"] == "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550"
                and frozen["leanchecker_sha256"] == "ed46f21c763051c26f89481096cbaaf5db9665d674d602e3daf3391613ba0e6a",
                "runtime binaries differ")
        require(frozen["external_snapshot"]["snapshot_sha256"] == SNAPSHOT_SHA, "wrong external binding")
        require(receipt["replay_binding"] == namespace["replay_context"](frozen), "wrong original replay context")
        for dependency, row in frozen["project"].items():
            require(dependency in normals, "project outside original 54-record authority")
            require(row["source_sha256"] == normals[dependency]["source_sha256"]
                    and row["object_sha256"] == normals[dependency]["object_sha256"], "project identity drift")

        replay, audit = receipt["replay"], receipt["audit"]
        require(replay["command"] == [CHECKER, "--verbose", module]
                and replay["exit_code"] == 0 and replay["inputs_unchanged"] is True, "named replay failure")
        require(audit["command"] == [LEAN, "-t0", "-j1", "-M11264", "-DwarningAsError=true",
                "-DmaxRecDepth=50000", "-DmaxHeartbeats=40000000", audit["source"]]
                and audit["exit_code"] == 0 and audit["inputs_unchanged"] is True
                and audit["memory_mb"] == 11264, "original full-owned invocation differs")
        for relative, digest in receipt["artifacts"].items():
            require(sha(member(original_member(relative))) == digest, "original artifact mismatch")
        for process in [replay, audit]:
            require(sha(member(original_member(process["log"]))) == process["log_sha256"], "process log mismatch")
        generated = member(original_member(audit["source"]))
        require(generated.decode() == template.replace("ImbalancedChen.P2Winner9FiniteMomentKernel", module)
                and sha(generated) == audit["source_sha256"], "generated audit source differs from original template")
        audit_log = base / original_member(audit["log"])
        parsed = namespace["parse_audit"](audit_log, module, set(frozen["project"]))
        attempt = Path(original_member(audit["source"])).parent
        declarations_name = (attempt / "declarations.json").as_posix()
        types_name = (attempt / "types.txt").as_posix()
        require(parsed == json.loads(member(declarations_name)), "raw log/parser/declarations differ")
        types_raw = member(types_name)
        require(types_raw == ("\n\n".join(d["name"] + "\n" + d["type"]
                for d in parsed["declarations"]) + "\n").encode(), "complete type serialization differs")
        require(parsed["declaration_count"] == audit["declaration_count"] == pin["owned"], "owned count differs")
        require(parsed["axiom_counts"] == audit["axiom_counts"], "axiom summary differs")
        results[module] = {
            **pin, "root_accepted_for_reuse": True,
            "receipt_member": root_index["attempt_receipt_member"], "receipt_sha256": sha(raw_receipt),
            "input_snapshot_sha256": receipt["input_sha256"], "frozen_project_count": len(frozen["project"]),
            "normal_exit_code": 0, "normal_log_bytes": 0, "named_kernel_exit_code": 0, "full_owned_exit_code": 0,
            "declarations_member": declarations_name, "types_member": types_name,
            "types_bytes": len(types_raw), "types_sha256": sha(types_raw),
            "owned_names": [d["name"] for d in parsed["declarations"]],
            "private_owned": sum(d["name"].startswith("_private.") for d in parsed["declarations"]),
            "axiom_counts": parsed["axiom_counts"],
        }
    summary_name = "project/.lake/p2-private/audit/p29-polyhedral-affine-missing-owned-20261126.json"
    summary = json.loads(member(summary_name))
    require(summary == {"accepted": 2, "all_accepted": True, "modules": {
        module: {"accepted": True, "declarations": pin["owned"], "reused": False}
        for module, pin in TARGETS.items()}, "requested": 2}, "original summary differs")
    result = {
        "schema": "p29_two_root_original_schema1_root_semantic_acceptance_v1",
        "status": "PASS_EXACT_ORIGINAL_NORMAL_NAMED_KERNEL_FULL_OWNED_RECEIPTS",
        "original_audit_job": complete["original_audit_job"],
        "complete_manifest_sha256": sha(complete_raw),
        "original_archive": complete["original_archive"],
        "external_snapshot_sha256": SNAPSHOT_SHA,
        "original_parser_ast_sha256": parser_ast_sha,
        "original_tool_sha256": TOOL_PINS,
        "roots": results,
        "small_original_members_rechecked": {n: {"bytes": len(b), "sha256": sha(b)} for n, b in checked.items()},
        "full_archive_transport_validation": "Reviewed immutable local-receiver code and its successful complete receipt; no remote reread or duplicate full-archive decompression by this semantic checker.",
        "format_boundary": "Original pp.all types and original serialized/environment owned inventory, including private/generated declarations. This receipt makes no separate raw-AST universe serialization claim.",
        "old_normal_compilations_repeated": 0,
        "Lean_invocations_by_this_checker": 0,
        "new_manuscript_credit": 0,
        "full_native_standard_facet_graph_qualified_by_this_audit": False,
        "whole_standard_import_kernel_replay_claim": False,
        "full_P2_9_complete": False,
    }
    raw = (json.dumps(result, indent=2, ensure_ascii=False) + "\n").encode()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.open("xb") as stream:
        stream.write(raw)
    print(json.dumps({"path": str(output), "bytes": len(raw), "sha256": sha(raw),
                      "owned_counts": {m: r["owned"] for m, r in results.items()}}, indent=2))


if __name__ == "__main__":
    main()
