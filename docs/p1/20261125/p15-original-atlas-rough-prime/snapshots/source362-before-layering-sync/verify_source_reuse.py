#!/usr/bin/env python3
"""Verify this exact source adoption. This script never invokes Lean or Lake.

The default invocation is read-only and prints a deterministic JSON report.
--write-report writes only STATIC_VERIFICATION.json beside this script.
The declaration ownership check is lexical; it is not an elaboration claim.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TARGETS = [
    "ImbalancedChen.P1OriginalSingletonSupportData",
    "ImbalancedChen.P1OriginalSingletonCutoffData",
    "ImbalancedChen.P5OriginalPrimeAtlasReserveBranches",
    "ImbalancedChen.P1OriginalSingletonAtlasRoughPrime",
]
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b")
DECL = re.compile(
    r"^(?:@\[[^\n]*\][ \t]*)*(?:(private|protected)[ \t]+)?"
    r"(?:(?:noncomputable|nonrec|partial|unsafe)[ \t]+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive)[ \t]+([^\s(:{]+)",
    re.M,
)


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(raw, path):
    blob = hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()
    return {"path": path, "bytes": len(raw), "sha256": sha(raw), "git_blob": blob}


def checked(row):
    raw = (ROOT / row["path"]).read_bytes()
    actual = fingerprint(raw, row["path"])
    for key in ("path", "bytes", "sha256", "git_blob"):
        need(actual[key] == row[key], "fingerprint mismatch: " + row["path"] + " / " + key)
    return raw


def load(name):
    return json.loads((HERE / name).read_text())


def git_bytes(ref):
    return subprocess.run(
        ["git", "cat-file", "blob", ref], cwd=ROOT, check=True, capture_output=True
    ).stdout


def lean_code(text):
    """Mask nested comments and strings without changing line/character positions."""
    out = list(text)
    i = 0
    while i < len(text):
        start = i
        if text.startswith("--", i):
            i = text.find("\n", i)
            if i < 0:
                i = len(text)
        elif text.startswith("/-", i):
            i += 2
            depth = 1
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            need(depth == 0, "unclosed Lean comment")
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unclosed Lean string")
        else:
            i += 1
            continue
        for j in range(start, i):
            if out[j] not in "\r\n":
                out[j] = " "
    return "".join(out)


def imports(raw):
    code = lean_code(raw.decode())
    return [word for line in re.findall(r"^import[ \t]+([^\n\r]+)", code, re.M)
            for word in line.split()]


def declarations(raw):
    """Read ordinary top-level namespaces/sections and named declarations."""
    scopes = []
    answer = []
    for line in lean_code(raw.decode()).splitlines():
        ns = re.fullmatch(r"namespace[ \t]+([^\s]+)[ \t]*", line)
        sec = re.fullmatch(r"(?:noncomputable[ \t]+)?section(?:[ \t]+([^\s]+))?[ \t]*", line)
        end = re.fullmatch(r"end(?:[ \t]+([^\s]+))?[ \t]*", line)
        if ns:
            scopes.append(("namespace", ns.group(1)))
        elif sec:
            scopes.append(("section", sec.group(1)))
        elif end:
            if scopes:
                scopes.pop()
        else:
            found = DECL.match(line)
            if found:
                visibility, kind, name = found.groups()
                namespace = ".".join(s[1] for s in scopes if s[0] == "namespace")
                if name.startswith("_root_."):
                    qualified = name[len("_root_."):]
                else:
                    qualified = namespace + "." + name if namespace else name
                answer.append({"name": name, "namespace": namespace,
                               "qualified_name": qualified, "kind": kind,
                               "visibility": visibility or "public"})
    return answer


def remove_intervals(raw, intervals):
    last = 0
    ordered = sorted(intervals)
    for lo, hi in ordered:
        need(last <= lo < hi <= len(raw), "overlapping or invalid byte intervals")
        last = hi
    for lo, hi in reversed(ordered):
        raw = raw[:lo] + raw[hi:]
    return raw


def reachable(graph, roots):
    done, active = set(), set()
    def visit(module):
        need(module in graph, "missing project module: " + module)
        need(module not in active, "project import cycle: " + module)
        if module in done:
            return
        active.add(module)
        for child in graph[module]:
            visit(child)
        active.remove(module)
        done.add(module)
    for root in roots:
        visit(root)
    return done


def verify():
    adoption = load("ADOPTION_MANIFEST.json")
    extraction = load("EXTRACTION_MANIFEST.json")
    selection = load("SOURCE_VERSION_SELECTION.json")
    closure = load("SOURCE_CLOSURE.json")
    context = adoption["source_context_commit"]
    for other in (extraction, selection, closure):
        need(other["source_context_commit"] == context, "source-context mismatch")
    for key in ("extraction_manifest", "source_version_selection", "source_closure"):
        checked(adoption[key])
    need([o["module"] for o in adoption["owners"]] == TARGETS, "owner set/order changed")
    need(closure["targets"] == TARGETS, "closure roots changed")
    need(adoption["new_arithmetic_proof_bodies"] == 0, "new proof-body claim changed")
    need(not adoption["physical_singletonAtlas_caller_adopted"], "physical caller claimed")

    owner_bytes = {}
    for owner in adoption["owners"]:
        raw = checked(owner["destination"])
        owner_bytes[owner["destination"]["path"]] = raw
        need(imports(raw) == owner["imports"], "owner imports changed: " + owner["module"])
        need(len(declarations(raw)) == owner["declaration_count"], "owner declaration count")
        if owner["adoption"] == "complete_original_bytes":
            origin = owner["original_source"]
            need(raw == checked(origin) == git_bytes(context + ":" + origin["path"]),
                 "whole-provider bytes changed")
    for row in extraction["destinations"]:
        need(checked(row) == owner_bytes[row["path"]], "extraction destination mismatch")

    sources = {}
    extracted = []
    destination_intervals = {}
    for source in extraction["sources"]:
        origin = source["origin"]
        raw = checked(origin)
        need(raw == git_bytes(context + ":" + origin["path"]), "origin absent/changed at source pin")
        need(source["available_at_commit"] == context, "origin availability pin mismatch")
        sources[source["source_key"]] = source
        origin_decls = declarations(raw)
        for row in source["selected_declarations"]:
            lo, hi = row["source_start_byte"], row["source_end_byte"]
            need(0 <= lo <= row["source_declaration_start_byte"] < hi <= len(raw), "source interval")
            block = raw[lo:hi]
            need(len(block) == row["bytes"] and sha(block) == row["sha256"], "block fingerprint")
            need(raw[:lo].count(b"\n") + 1 == row["source_start_line"], "block start line")
            need(raw[:row["source_declaration_start_byte"]].count(b"\n") + 1 ==
                 row["source_declaration_start_line"], "declaration start line")
            expected = {k: row[k] for k in ("name", "namespace", "qualified_name", "kind", "visibility")}
            need(origin_decls.count(expected) == 1, "original declaration identity")
            dest = owner_bytes[row["destination"]]
            dlo, dhi = row["destination_start_byte"], row["destination_end_byte"]
            need(0 <= dlo < dhi <= len(dest) and dest[dlo:dhi] == block, "copied block differs")
            need(declarations(dest).count(expected) == 1, "destination namespace/name/visibility changed")
            destination_intervals.setdefault(row["destination"], []).append((dlo, dhi))
            extracted.append(row)
    need(len(extracted) == extraction["extracted_declaration_count"] == 16, "extraction count")
    need(sum(r["visibility"] == "private" for r in extracted) ==
         extraction["extracted_private_count"] == 2, "private helper count")
    need(sum(r["visibility"] == "public" for r in extracted) ==
         extraction["extracted_public_count"] == 14, "public extraction count")
    for path, intervals in destination_intervals.items():
        residual = lean_code(remove_intervals(owner_bytes[path], intervals).decode())
        allowed = re.compile(r"(?:import\b.*|namespace\b.*|noncomputable section|open\b.*|end(?:\b.*)?)")
        need(all(not line.strip() or allowed.fullmatch(line.strip())
                 for line in residual.splitlines()), "new non-wrapper code outside extracted blocks: " + path)
        need(len(declarations(owner_bytes[path])) == len(intervals), "unrecorded owner declaration")

    postimages = []
    for row in extraction["future_provider_postimages"]:
        source = sources[row["source_key"]]
        preimage = checked(row["preimage"])
        postimage = checked(row["postimage"])
        original = checked(row["source"])
        need(row["source"] == source["origin"], "postimage origin mismatch")
        intervals = []
        for block in source["selected_declarations"]:
            lo, hi = block["preimage_start_byte"], block["preimage_end_byte"]
            need(preimage[lo:hi] == original[block["source_start_byte"]:block["source_end_byte"]],
                 "preimage block differs")
            intervals.append((lo, hi))
        rebuilt = row["added_import"].encode() + remove_intervals(preimage, intervals)
        need(postimage == rebuilt, "future postimage is not the exact complementary deletion")
        remaining = {d["qualified_name"] for d in declarations(postimage)}
        removed = [b["qualified_name"] for b in source["selected_declarations"]]
        need(row["removed_declarations"] == removed, "removed declaration list changed")
        need(not remaining.intersection(removed), "postimage redeclares migrated owner")
        need(not FORBIDDEN.search(lean_code(postimage.decode())), "forbidden token in postimage")
        postimages.append(row["postimage"]["path"])
    rough_post = next(r for r in extraction["future_provider_postimages"] if r["source_key"] == "rough")
    physical = "ImbalancedChen.P1OriginalSingletonRoughPrimeReserveZero.eventually_original_singletonAtlas_roughPrime_paid"
    need([d["qualified_name"] for d in declarations(checked(rough_post["postimage"]))] == [physical],
         "physical caller not retained as the sole remaining declaration")
    need(all(physical not in {d["qualified_name"] for d in declarations(raw)}
             for raw in owner_bytes.values()), "physical caller entered new owners")
    uniform_post = next(r for r in extraction["future_provider_postimages"] if r["source_key"] == "uniform")
    ucode = lean_code(checked(uniform_post["postimage"]).decode())
    need(all(not re.search(r"\b" + re.escape(r["name"]) + r"\b", ucode)
             for r in sources["uniform"]["selected_declarations"] if r["visibility"] == "private"),
         "remaining provider refers to moved private helpers")

    for key in ("rough_source_freeze", "selected_cutoff_registry", "uniform_cutoff_selected", "later_hidden_variant"):
        raw = checked(selection[key])
        need(raw == git_bytes(context + ":" + selection[key]["path"]), "version-selection input pin")
    frozen = json.loads(checked(selection["rough_source_freeze"]))
    selected = selection["uniform_cutoff_selected"]
    frozen_rows = [r for r in frozen["sources"] if r.get("path") == selected["path"]]
    need(len(frozen_rows) == 1, "frozen selection not unique")
    frozen_row = frozen_rows[0]
    need(frozen_row["commit"] == selected["recorded_mathematical_source_commit"] and
         frozen_row["sha256"] == selected["sha256"] and frozen_row["bytes"] == selected["bytes"] and
         frozen_row["git_blob_sha1"] == selected["git_blob"], "frozen selected version differs")
    registry = json.loads(checked(selection["selected_cutoff_registry"]))
    rows = [r for r in registry["six"] if r["module"] == "ImbalancedChen.P5IndependentTestPrimeChartUniformCutoff"]
    need(len(rows) == 1 and rows[0]["selected"]["sha256"] == selected["sha256"] and
         rows[0]["selected"]["bytes"] == selected["bytes"], "repair registry selection differs")
    uniform = checked(selected)
    hidden = checked(selection["later_hidden_variant"])
    for row in sources["uniform"]["selected_declarations"]:
        block = uniform[row["source_start_byte"]:row["source_end_byte"]]
        need(hidden.count(block) == 1, "selected block differs in later hidden variant")
    qualifier = b"ImbalancedChen.P5Z.OriginalJointPresievedCompiler.jointPresievedSigma"
    need(uniform.count(b"jointPresievedSigma") == 1 and
         uniform.replace(b"jointPresievedSigma", qualifier) == hidden,
         "later hidden variant has a different delta")

    # The original protected rows are historical bindings, not mutable baselines.
    # Reconstruct the one separately authorized dependency repair from its pin.
    need(closure["external_dependency_repair"] == adoption["external_dependency_repair"],
         "external dependency repair binding differs")
    external = json.loads(checked(adoption["external_dependency_repair"]))
    authoritative = json.loads(checked(external["authoritative_manifest"]))
    need(external["failed_source_commit"] == authoritative["failed_source_commit"] == context,
         "external repair source anchor differs")
    need(external["failed_job"] == authoritative["failed_job"], "external repair job differs")
    selected_repairs = [r for r in authoritative["files"] if r["module"] in closure["project_sources"]]
    need(external["relevant_repairs"] == selected_repairs and
         [r["path"] for r in selected_repairs] ==
         ["ImbalancedChen/P1OriginalSingletonPointwiseData.lean"], "external repair scope differs")
    repaired_originals = {}
    for row in selected_repairs:
        original = git_bytes(context + ":" + row["path"])
        need(fingerprint(original, row["path"]) == {"path": row["path"], **row["before"]},
             "external repair preimage differs")
        parts, previous = [], 0
        for splice in row["exact_byte_splices"]:
            lo, hi = splice["pre_start_byte"], splice["pre_end_byte"]
            need(previous <= lo < hi <= len(original) and
                 original[lo:hi] == splice["old_utf8"].encode(), "external repair exact splice differs")
            parts.extend([original[previous:lo], splice["new_utf8"].encode()])
            previous = hi
        parts.append(original[previous:])
        after = b"".join(parts)
        need(after == checked({"path": row["path"], **row["after"]}), "external repair postimage differs")
        need(imports(after) == imports(original) and declarations(after) == declarations(original),
             "external expression repair changed imports or declaration identities")
        repaired_originals[row["path"]] = original
    protected = adoption["protected_inputs"]
    for path, row in protected.items():
        need(row["path"] == path, "protected input key mismatch")
        if path in repaired_originals:
            need(fingerprint(repaired_originals[path], path) == row,
                 "original protected baseline was overwritten")
        else:
            checked(row)

    graph = {}
    for module, row in closure["project_sources"].items():
        raw = checked(row)
        need(row["path"] == module.replace(".", "/") + ".lean", "module/path mismatch")
        all_imports = imports(raw)
        project = [m for m in all_imports if m.startswith("ImbalancedChen.")]
        need(row["imports"] == project and row["all_imports"] == all_imports, "closure imports changed: " + module)
        need(not FORBIDDEN.search(lean_code(raw.decode())), "forbidden proof token: " + module)
        graph[module] = project
    active = reachable(graph, TARGETS)
    need(active == set(graph) and len(active) == closure["project_module_count"] == 362,
         "closure is not the exact four-root set")
    need(closure["target_count"] == 4 and closure["existing_dependency_count"] == 358,
         "root/dependency counts changed")
    need(not closure["missing"] and not closure["cycles"], "recorded missing imports/cycles")
    comparison = closure["phase2_comparison"]
    previous = json.loads(checked(comparison["manifest"]))
    previous_set = set(previous["project_sources"])
    additional_existing = active - previous_set - set(TARGETS)
    need(not additional_existing and comparison["additional_existing_canonical_modules"] == [],
         "additional canonical dependency beyond phase2")
    need(comparison["additional_new_owners"] == TARGETS, "additional owner list")
    need(len(active | previous_set) == comparison["phase2_plus_rough_union_module_count"] == 390,
         "phase2 union count")
    phase1 = json.loads((ROOT / "docs/p1/20261125/p15-singleton-proper-power/SOURCE_CLOSURE.json").read_text())
    phase1_set = set(phase1["project_sources"])
    need(len(active | previous_set | phase1_set) ==
         comparison["phase1_phase2_rough_union_module_count"] == 479, "phase1/phase2/rough union count")

    owned = [d for raw in owner_bytes.values() for d in declarations(raw)]
    public = [d for d in owned if d["visibility"] != "private"]
    public_names = {d["qualified_name"] for d in public}
    need(len(owned) == adoption["total_declarations"] == 27 and
         len(public) == len(public_names) == adoption["public_declarations"] == 25 and
         len(owned) - len(public) == adoption["private_declarations"] == 2, "owner totals or internal duplicates")
    candidates = []
    ownership = {name: [] for name in public_names}
    namespace_fragments = {d["namespace"].split(".")[-1] for d in public}
    # Limit lexical ownership parsing to canonical files mentioning these namespaces.
    for path in sorted((ROOT / "ImbalancedChen").rglob("*.lean")):
        raw = path.read_bytes()
        text = raw.decode()
        if any(fragment in text for fragment in namespace_fragments):
            candidates.append(path.relative_to(ROOT).as_posix())
            for row in declarations(raw):
                if row["visibility"] != "private" and row["qualified_name"] in ownership:
                    ownership[row["qualified_name"]].append(path.relative_to(ROOT).as_posix())
    for name, paths in ownership.items():
        need(len(paths) == 1 and paths[0] in owner_bytes, "duplicate or absent canonical owner: " + name)

    need(adoption["quantifier_order"]["before_threshold"] ==
         ["K : Nat", "1 <= K", "kappa : Real", "kappa < 1"], "threshold parameters changed")
    need(adoption["quantifier_order"]["after_threshold"] ==
         ["N >= N0", "B : Nat", "kappa0 : Real", "Q : Finset Nat", "rho : Nat -> Complex", "js in chartBank (2*N) 1"],
         "post-threshold parameters changed")
    for data in (adoption, extraction, selection, closure):
        need(not data["compiled"] and not data["kernel_replayed"] and not data["proof_credit_added"],
             "source evidence converted into proof credit")

    return {
        "schema": "p15_original_atlas_rough_prime_static_verification_v1",
        "status": "PASS_STATIC_SOURCE_ADOPTION_ONLY",
        "verifier": fingerprint(Path(__file__).read_bytes(), Path(__file__).relative_to(ROOT).as_posix()),
        "source_context_commit": context,
        "manifest_fingerprints": [fingerprint((HERE / name).read_bytes(), (HERE / name).relative_to(ROOT).as_posix())
                                  for name in ("ADOPTION_MANIFEST.json", "EXTRACTION_MANIFEST.json", "SOURCE_VERSION_SELECTION.json", "SOURCE_CLOSURE.json", "EXTERNAL_DEPENDENCY_REPAIR.json")],
        "owners": [o["destination"] for o in adoption["owners"]],
        "exact_extracted_declarations": 16,
        "whole_provider_declarations": 11,
        "public_declarations": 25,
        "private_helpers_original_lexical_names_and_bytes": 2,
        "new_arithmetic_proof_bodies": 0,
        "original_source_git_objects_checked": 5,
        "version_selection_git_objects_checked": 4,
        "frozen_repaired_uniform_cutoff_selection_verified": True,
        "hidden_variant_first_six_blocks_byte_identical": True,
        "future_provider_postimages_exact": postimages,
        "physical_singletonAtlas_caller_retained_uncompiled": True,
        "original_protected_baseline_bindings_preserved": len(protected),
        "protected_inputs_unchanged": len(protected) - len(repaired_originals),
        "exact_parent_authorized_external_dependency_repairs": list(repaired_originals),
        "pending_parent_phase2_source_pin_sync": adoption["pending_parent_phase2_source_pin_sync"],
        "project_closure_modules": len(active),
        "existing_dependencies_cache_evidence_only": 358,
        "additional_existing_dependencies_beyond_phase2": [],
        "phase2_plus_rough_union_modules": 390,
        "phase1_phase2_rough_union_modules": 479,
        "project_imports_and_source_fingerprints_checked": True,
        "missing_project_imports": [],
        "import_cycles": [],
        "forbidden_proof_tokens_found": [],
        "ownership_check_scope": "Lexical namespaces/declarations in canonical files; not a Lean elaboration claim.",
        "ownership_candidate_files": candidates,
        "new_public_names_have_one_canonical_lexical_owner": True,
        "compiled": False,
        "kernel_replayed": False,
        "cloud_task_started": False,
        "git_commit_created": False,
        "proof_credit_added": False,
        "P1_5_closed": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-report", action="store_true")
    args = parser.parse_args()
    report = verify()
    output = json.dumps(report, ensure_ascii=False, indent=2) + "\n"
    if args.write_report:
        (HERE / "STATIC_VERIFICATION.json").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
