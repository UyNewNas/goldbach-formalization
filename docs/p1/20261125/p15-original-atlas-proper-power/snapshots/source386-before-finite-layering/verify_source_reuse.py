#!/usr/bin/env python3
"""Verify the five-owner source snapshot; never run Lean or mutate source/cache.

Without arguments, print the check result. --write-receipt also writes only
CURRENT_STATIC_VERIFICATION.json beside this script. Historical receipts,
reviewed hashes, source originals, migration postimages and caches are read only.
"""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
PHASE1 = ROOT / "docs/p1/20261125/p15-singleton-proper-power"
EXPECTED_ROOTS = [
    "ImbalancedChen.PrimeProductsMellinExactMeanInsertion",
    "ImbalancedChen.P5IndependentPrimeSourceWordDictionary",
    "ImbalancedChen.P5OriginalPrimeAllGroupHBDiscrepancy",
    "ImbalancedChen.P1OriginalSingletonSmoothLicence",
    "ImbalancedChen.P1OriginalSingletonAtlasProperPower",
]
FINGERPRINT_KEYS = ("path", "bytes", "sha256", "git_blob")
INSTALLER = "docs/p1/20261125/p15-singleton-proper-power/install_sources.py"
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|unsafe)\b")


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def fingerprint(raw, path):
    return {"path": path, "bytes": len(raw), "sha256": sha(raw),
            "git_blob": hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()}


def file_fingerprint(path):
    return fingerprint((ROOT / path).read_bytes(), path)


def load(name):
    return json.loads((HERE / name).read_bytes())


def check_fingerprint(row, raw=None):
    if raw is None:
        raw = (ROOT / row["path"]).read_bytes()
    actual = fingerprint(raw, row["path"])
    for key in FINGERPRINT_KEYS:
        if key in row:
            need(actual[key] == row[key], f"fingerprint differs: {row['path']} {key}")
    return raw


def git_bytes(ref):
    return subprocess.check_output(["git", "cat-file", "blob", ref], cwd=ROOT)


def check_original(row):
    raw = check_fingerprint(row)
    need(git_bytes(row["git_blob"]) == raw, "origin Git blob differs: " + row["path"])
    commit = row.get("available_at_commit", row.get("source_commit"))
    if commit:
        need(git_bytes(commit + ":" + row["path"]) == raw,
             "origin commit/path differs: " + row["path"])
    return raw


def remove_intervals(raw, intervals):
    ordered = sorted(intervals)
    last = 0
    for lo, hi in ordered:
        need(last <= lo < hi <= len(raw), "overlapping or invalid declaration intervals")
        last = hi
    for lo, hi in reversed(ordered):
        raw = raw[:lo] + raw[hi:]
    return raw


def declaration_bytes(raw, row):
    lo, hi = row["source_start_byte"], row["source_end_byte"]
    need(0 <= lo < hi <= len(raw), "invalid declaration interval: " + row["name"])
    body = raw[lo:hi]
    need(len(body) == row["bytes"] and sha(body) == row["sha256"],
         "declaration bytes differ: " + row["name"])
    return body


def lean_code(text):
    """Erase nested comments and string literals, preserving line boundaries."""
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


def import_list(raw):
    code = lean_code(raw.decode("utf-8"))
    return [word for line in re.findall(r"^import[ \t]+([^\n\r]+)", code, re.M)
            for word in line.split()]


def reachable(graph, roots):
    done, active = set(), set()
    def visit(module):
        need(module in graph, "missing import in manifest: " + module)
        need(module not in active, "project import cycle at " + module)
        if module in done:
            return
        active.add(module)
        for child in graph[module]:
            visit(child)
        active.remove(module)
        done.add(module)
    for module in roots:
        visit(module)
    return done


def dependency_updates(adoption, closure, exceptions):
    """Check exact external source changes without claiming type equivalence."""
    binding = adoption["external_dependency_updates"]
    need(binding == closure["external_dependency_updates"] ==
         exceptions["dependency_source_updates"], "dependency-update binding differs")
    updates = json.loads(check_fingerprint(binding))
    baseline = json.loads(check_fingerprint(updates["prior_binding_snapshot"]))
    protected_hash = sha(json.dumps(adoption["protected_inputs"], sort_keys=True,
                                    separators=(",", ":")).encode())
    need(protected_hash == baseline["protected_input_bindings_sha256"],
         "original29 protected bindings were changed")
    for name in ["SOURCE_REVIEW.json", "SMOOTH_EXTRACTION.json", "FORMAT_ONLY_DELTA.json",
                 "STATIC_VERIFICATION.json", "run_selected.py", "install_sources.py"]:
        check_fingerprint(baseline["files"][name])
    history = adoption["historical_five_owner_before_dependency_updates"]
    need(history["binding_snapshot"] == updates["prior_binding_snapshot"],
         "pre-update snapshot binding differs")
    old_receipt = check_fingerprint(history["static_receipt"])
    check_fingerprint(baseline["files"]["CURRENT_STATIC_VERIFICATION.json"], old_receipt)
    old_exceptions_raw = check_fingerprint(history["protected_exception_record"])
    check_fingerprint(baseline["files"]["PROTECTED_INPUT_EXCEPTIONS.json"], old_exceptions_raw)
    old_exceptions = json.loads(old_exceptions_raw)
    need(exceptions["exceptions"][0] == old_exceptions["exceptions"][0],
         "historical installer exception changed")

    published = "d20acdf13882e17d97833064f5e7c54f3192b03c"
    failed = "1a259e113c0977c8cb2814492ff3bd6ab7cdc475"
    first = updates["first_compile_repairs"]
    need(updates["published_phase1_update_commit"] == first["published_commit"] == published
         and first["failed_source_commit"] == failed, "first-compile source anchors differ")
    repair_raw = check_fingerprint(first["manifest"])
    need(git_bytes(published + ":" + first["manifest"]["path"]) == repair_raw,
         "published first-compile repair manifest differs")
    repair = json.loads(repair_raw)
    need(repair["failed_source_commit"] == failed, "repair preimage commit differs")
    expected_paths = {"ImbalancedChen/P1OriginalSingletonPointwiseData.lean",
                      "ImbalancedChen/P1Full87TrueDPolicyDelta.lean"}
    need({r["path"] for r in repair["files"]} == expected_paths and len(repair["files"]) == 2,
         "first-compile repair selection differs")
    summarized = {r["path"]: r for r in first["files"]}
    need(set(summarized) == expected_paths and len(first["files"]) == 2,
         "repair summary selection differs")
    preimages, changed_modules = {}, set()
    for row in repair["files"]:
        path = row["path"]
        normalized = {"module": row["module"], "path": path,
                      "before": {"path": path, **row["before"]},
                      "after": {"path": path, **row["after"]},
                      "splice_count": len(row["exact_byte_splices"])}
        need(summarized[path] == normalized, "repair summary differs")
        original = git_bytes(failed + ":" + path)
        check_fingerprint(normalized["before"], original)
        parts, previous = [], 0
        for splice in row["exact_byte_splices"]:
            lo, hi = splice["pre_start_byte"], splice["pre_end_byte"]
            need(previous <= lo < hi <= len(original) and
                 original[lo:hi] == splice["old_utf8"].encode(), "first-compile splice differs")
            parts.extend([original[previous:lo], splice["new_utf8"].encode()])
            previous = hi
        parts.append(original[previous:])
        current = check_fingerprint(normalized["after"])
        need(current == b"".join(parts) == git_bytes(published + ":" + path),
             "first-compile complete postimage differs")
        need(import_list(original) == import_list(current), "first-compile imports changed")
        preimages[path] = original
        changed_modules.add(row["module"])

    adopted = updates["existing_dependency_adoption"]
    accepted_raw = check_fingerprint(adopted["manifest"])
    accepted = json.loads(accepted_raw)
    need(accepted["schema"] == "p15_existing_atlas_dependency_source_reuse_v1" and
         accepted["base_commit"] == adopted["base_commit"] == published and
         accepted["accepted_publication_commit"] == adopted["accepted_publication_commit"] ==
         "a392cd8efcf4f0b4adf3d12f2d8db41370309ed3", "existing-postimage source anchors differ")
    need(accepted["module_count"] == adopted["module_count"] ==
         len(accepted["modules"]) == len(adopted["modules"]) == 9,
         "existing-postimage adoption count differs")
    need(not accepted["new_Lean_acceptance_claimed"] and
         not adopted["old_new_elaborated_type_equivalence_proved"] and
         not adopted["object_or_kernel_readiness_checked_here"], "unsupported source reuse claim")
    nine_modules = set()
    nine_preimages = {}
    for supplier, row in zip(accepted["modules"], adopted["modules"]):
        path, module = supplier["canonical_path"], supplier["module"]
        before, after = supplier["before"], supplier["after"]
        need(before["git_commit"] == published and
             after["source_git_commit"] == accepted["accepted_publication_commit"],
             "existing dependency source pin differs")
        original = git_bytes(before["git_commit"] + ":" + path)
        source = git_bytes(after["source_git_commit"] + ":" + after["source_repository_path"])
        need(before["sha256"] == sha(original) and before["bytes"] == len(original) and
             before["git_blob"] == fingerprint(original, path)["git_blob"],
             "existing dependency original bytes differ")
        need(after["sha256"] == sha(source) and after["bytes"] == len(source) and
             after["git_blob"] == fingerprint(source, path)["git_blob"],
             "existing accepted postimage bytes differ")
        need((ROOT / before["snapshot_path"]).read_bytes() == original and
             (ROOT / path).read_bytes() == source and
             (ROOT / after["source_repository_path"]).read_bytes() == source,
             "preserved preimage or current adopted source differs")
        need(import_list(original) == import_list(source) == supplier["direct_imports"],
             "existing-postimage imports differ")
        normalized = {
            "module": module, "path": path, "before": fingerprint(original, path),
            "before_commit": before["git_commit"],
            "preserved_preimage": fingerprint(original, before["snapshot_path"]),
            "after": fingerprint(source, path), "source_commit": after["source_git_commit"],
            "source": fingerprint(source, after["source_repository_path"]),
            "all_imports": supplier["direct_imports"],
            "reviewed_exception_classifications": supplier["repair_review"]["exception_classifications"],
            "old_new_elaborated_type_equivalence_proved": False,
        }
        need(row == normalized and
             supplier["repair_review"]["old_new_elaborated_type_equivalence_proved"] is False,
             "existing-postimage normalized binding or type-equivalence scope differs")
        need(module not in nine_modules, "duplicate adopted existing module")
        nine_modules.add(module)
        nine_preimages[path] = original
    need(not set(nine_preimages).intersection(adoption["protected_inputs"]),
         "nine-source adoption unexpectedly intersects original protected inputs")

    # Reconstruct the entire prior closure to preserve all unaffected row/field pins.
    reconstruction = updates["closure_reconstruction"]
    old_closure = copy.deepcopy(closure)
    for key in reconstruction["current_only_top_level_fields"]:
        need(key == "external_dependency_updates", "unexpected closure-only field")
        old_closure.pop(key)
    old_closure["stage1_comparison"] = reconstruction["before_stage1_comparison"]
    old_rows = reconstruction["before_changed_project_rows"]
    active_changes = (changed_modules | nine_modules).intersection(closure["project_sources"])
    need(set(old_rows) == active_changes and len(old_rows) == 10,
         "prior closure changed-row selection differs")
    originals = {**preimages, **nine_preimages}
    for module, row in old_rows.items():
        check_fingerprint(row, originals[row["path"]])
        old_closure["project_sources"][module] = row
    old_raw = (json.dumps(old_closure, ensure_ascii=False, indent=2) + "\n").encode()
    check_fingerprint(reconstruction["before_binding"], old_raw)
    need(reconstruction["before_binding"] == baseline["files"]["SOURCE_CLOSURE.json"],
         "prior closure fingerprint differs")
    phase1 = json.loads((PHASE1 / "SOURCE_CLOSURE.json").read_bytes())
    union = set(closure["project_sources"]) | set(phase1["project_sources"])
    membership = updates["membership"]
    need(sorted(active_changes) == membership["active_source_changes"] and
         sorted((changed_modules | nine_modules).intersection(union)) == membership["union_source_changes"] and
         membership["active_source_change_count"] == 10 and
         membership["union_source_change_count"] == 11 and
         not nine_modules.intersection(phase1["project_sources"]) and
         membership["nine_adoption_phase1_intersection"] ==
         membership["nine_adoption_original_protected_input_intersection"] == [],
         "source-change membership differs")
    need(updates["unchanged_owner_bindings"] == [r["destination"] for r in adoption["owners"]],
         "five original owner fingerprints changed")
    for row in updates["unchanged_owner_bindings"]:
        check_fingerprint(row)
    need(not updates["compiled"] and not updates["kernel_replayed"] and
         not updates["proof_credit_added"] and updates["new_arithmetic_proof_bodies"] == 0,
         "dependency metadata grants unsupported acceptance")
    return updates, preimages


def verify():
    adoption = load("ADOPTION_MANIFEST.json")
    extraction = load("SMOOTH_EXTRACTION.json")
    review = load("SOURCE_REVIEW.json")
    delta = load("FORMAT_ONLY_DELTA.json")
    exceptions = load("PROTECTED_INPUT_EXCEPTIONS.json")
    closure = load("SOURCE_CLOSURE.json")
    historical = load("STATIC_VERIFICATION.json")
    need([r["module"] for r in adoption["owners"]] == EXPECTED_ROOTS,
         "five-owner adoption selection differs")
    need(closure["targets"] == EXPECTED_ROOTS, "five-root closure selection differs")
    for row in adoption["toolchain_inputs"] + adoption["existing_canonical_reuse"]:
        check_fingerprint(row)
    updates, repaired_originals = dependency_updates(adoption, closure, exceptions)

    # Keep every original protected binding; only the five explicit published changes.
    check_fingerprint(adoption["protected_input_exceptions"])
    need(len(adoption["protected_inputs"]) == 29 and len(exceptions["exceptions"]) == 5,
         "protected-input selection differs")
    exception = exceptions["exceptions"][0]
    need(exception["path"] == INSTALLER, "unexpected protected-input exception")
    need(exception["original_binding"] == adoption["protected_inputs"][INSTALLER],
         "protected installer baseline changed")
    exceptional = {r["path"]: r for r in exceptions["exceptions"]}
    need(len(exceptional) == 5 and sorted(exceptional) ==
         updates["membership"]["protected_changed_paths"] and
         exceptions["original_protected_input_count"] == 29 and
         exceptions["unchanged_input_count"] == updates["membership"]["unchanged_protected_count"] == 24 and
         exceptions["exception_count"] == 5, "protected exception set differs")
    for path, row in adoption["protected_inputs"].items():
        if path not in exceptional:
            check_fingerprint(row)
        elif path != INSTALLER:
            change = exceptional[path]
            need(change["kind"] == "published_phase1_first_compile_update" and
                 change["original_binding"] == row and
                 change["before_source_commit"] == updates["first_compile_repairs"]["failed_source_commit"] and
                 change["published_update_commit"] == updates["published_phase1_update_commit"] and
                 change["repair_manifest"] == updates["first_compile_repairs"]["manifest"] and
                 not change["phase2_modified_this_input"] and
                 not change["normal_kernel_audit_api_changed"], "published protected exception differs")
            check_fingerprint(row, git_bytes(change["before_source_commit"] + ":" + path))
            after = check_fingerprint(change["reviewed_current_binding"])
            need(after == git_bytes(change["published_update_commit"] + ":" + path),
                 "published protected postimage differs")
    after_installer = check_fingerprint(exception["reviewed_current_binding"])
    repair_raw = check_fingerprint(exception["repair_manifest"])
    repair = json.loads(repair_raw)
    need(repair["installer_before_sha256"] == exception["original_binding"]["sha256"]
         and repair["installer_after_sha256"] == sha(after_installer)
         and repair["normal_kernel_audit_api_changed"] is False,
         "installer exception repair binding differs")
    need(exception["normal_kernel_audit_api_changed"] is False
         and exception["phase2_modified_this_input"] is False,
         "exception scope differs")
    commit = exception["published_repair_commit"]
    need(git_bytes(commit + ":" + INSTALLER) == after_installer,
         "published installer differs")
    need(git_bytes(commit + ":" + exception["repair_manifest"]["path"]) == repair_raw,
         "published repair record differs")

    # Reconstruct the reviewed file exactly; the original review pins stay unchanged.
    check_fingerprint(adoption["format_only_delta"])
    check_fingerprint(extraction["format_only_delta"])
    check_fingerprint(review["post_review_format_only_delta"])
    smooth = check_fingerprint(delta["current_after"])
    check_fingerprint(delta["reviewed_before"], smooth + b"\n")
    need(delta["deleted_before_byte_interval"] == [len(smooth), len(smooth) + 1]
         and delta["deleted_hex"] == "0a", "format operation differs")
    need(smooth.endswith(b"\n") and not smooth.endswith(b"\n\n"),
         "format-only final-line condition differs")
    need(extraction["destination"] == delta["path"]
         and extraction["destination_sha256"] == sha(smooth)
         and extraction["destination_bytes"] == len(smooth)
         and extraction["destination_git_blob"] == delta["current_after"]["git_blob"],
         "smooth extraction destination differs")
    need({r["module"] for r in review["reviewed_owners"]} == set(EXPECTED_ROOTS),
         "review owner selection differs")
    for row in review["reviewed_owners"]:
        if row["path"] == delta["path"]:
            check_fingerprint(row, smooth + b"\n")
        else:
            check_fingerprint(row)
    before_review = {k: v for k, v in review.items()
                     if k not in {"post_review_format_only_delta", "current_source_binding_note"}}
    before_review_raw = (json.dumps(before_review, ensure_ascii=False, indent=2) + "\n").encode()
    check_fingerprint(delta["source_review_before_delta"], before_review_raw)

    # Whole-source adoptions and the single explicit AllGroup import substitution.
    for row in adoption["owners"]:
        current = check_fingerprint(row["destination"])
        kind = row["adoption"]
        if kind in {"complete_existing_t05_selected_source_byte_identical",
                    "complete_original_byte_identical"}:
            need(current == check_original(row["source"]), "complete source differs")
            if "selection_registry" in row:
                registry = check_original(row["selection_registry"])
                need(row["destination"]["sha256"].encode() in registry,
                     "selected source absent from recorded t05 registry")
        elif kind == "one_import_replacement_all_other_bytes_identical":
            original = check_original(row["source"])
            replace = row["replacement"]
            old, new = replace["old"].encode(), replace["new"].encode()
            need(original.count(old) == replace["occurrences"] == 1,
                 "AllGroup import replacement count differs")
            need(current == original.replace(old, new), "AllGroup non-import bytes changed")
        elif kind == "nine_exact_historical_declaration_blocks_in_original_namespaces":
            need(current == smooth, "smooth owner differs")
        else:
            need(row["module"] == EXPECTED_ROOTS[-1]
                 and kind == "new_finite_dictionary_and_existing_P3_supplier_instantiation",
                 "unknown adoption kind")

    # The exact original18 + unchanged9 reconstruct both historical postimages.
    # Current PointwiseData is separately bound to its one published expression repair.
    check_fingerprint(extraction["stage1_manifest"])
    pointwise_binding = extraction["stage1_pointwise_owner"]
    pointwise = check_fingerprint(pointwise_binding, repaired_originals[pointwise_binding["path"]])
    pointwise_current = (ROOT / pointwise_binding["path"]).read_bytes()
    p1_extraction = json.loads((ROOT / extraction["stage1_manifest"]["path"]).read_bytes())
    p1_sources = {r["path"]: r for r in p1_extraction["sources"]}
    need(sha(pointwise) == p1_extraction["destination_sha256"], "pointwise owner differs")
    point_import = b"import ImbalancedChen.P1OriginalSingletonPointwiseData\n"
    smooth_import = b"import ImbalancedChen.P1OriginalSingletonSmoothLicence\n"
    names, point_names, post_count = set(), set(), 0
    unchanged_current_pointwise = 0
    max_destination_end = 0
    for source in extraction["sources"]:
        original = check_original(source)
        old = p1_sources[source["path"]]
        need(check_original(old) == original, "phase1/phase2 origin differs")
        stage1 = check_fingerprint(source["stage1_preimage"])
        check_fingerprint(old["provider_postimage"], stage1)
        point_intervals, smooth_intervals, stage1_intervals = [], [], []
        bodies = []
        for d in old["declarations"]:
            body = declaration_bytes(original, d)
            need(pointwise.count(body) == 1 and smooth.count(body) == 0,
                 "pointwise declaration ownership differs: " + d["name"])
            need(pointwise_current.count(body) <= 1, "duplicate current pointwise block")
            unchanged_current_pointwise += int(pointwise_current.count(body) == 1)
            point_names.add(d["name"])
            bodies.append(body)
            point_intervals.append((d["source_start_byte"], d["source_end_byte"]))
        need(stage1 == point_import + remove_intervals(original, point_intervals),
             "stage1 provider postimage differs")
        for d in source["declarations"]:
            body = declaration_bytes(original, d)
            lo, hi = d["destination_start_byte"], d["destination_end_byte"]
            need(0 <= lo < hi <= len(smooth) and smooth[lo:hi] == body
                 and smooth.count(body) == 1 and pointwise.count(body) == 0,
                 "smooth declaration ownership/interval differs: " + d["name"])
            a, b = d["stage1_preimage_start_byte"], d["stage1_preimage_end_byte"]
            need(stage1[a:b] == body and stage1.count(body) == 1,
                 "smooth stage1 interval differs: " + d["name"])
            need(d["name"] not in names, "duplicate extracted declaration")
            names.add(d["name"])
            bodies.append(body)
            smooth_intervals.append((d["source_start_byte"], d["source_end_byte"]))
            stage1_intervals.append((a, b))
            max_destination_end = max(max_destination_end, hi)
        post = check_fingerprint(source["provider_postimage"])
        need(post == smooth_import + remove_intervals(stage1, stage1_intervals),
             "phase2 provider postimage differs")
        need(post == smooth_import + point_import +
             remove_intervals(original, point_intervals + smooth_intervals),
             "combined27 provider postimage differs")
        need(all(post.count(body) == 0 for body in bodies),
             "postimage retains a migrated declaration")
        need(not FORBIDDEN.search(lean_code(post.decode())), "forbidden token in postimage")
        post_count += 1
    need(len(names) == extraction["declaration_count"] == 9
         and len(point_names) == extraction["stage1_pointwise_declaration_count"] == 18
         and len(names | point_names) == 27 and post_count == 4,
         "declaration/postimage counts differ")
    need(unchanged_current_pointwise == 17, "current pointwise expression-repair scope differs")
    need(max_destination_end == delta["maximum_protected_declaration_end_byte"] <= len(smooth),
         "deleted byte intersects protected declarations")
    for row in adoption["provider_postimages"]:
        check_fingerprint(row)

    # Verify all imports and fingerprints of the active386 and complete union475.
    check_fingerprint(adoption["current_source_closure"])
    comparison = closure["stage1_comparison"]
    phase1_raw = (ROOT / comparison["manifest"]).read_bytes()
    need(sha(phase1_raw) == comparison["manifest_sha256"], "phase1 closure binding differs")
    phase1 = json.loads(phase1_raw)
    graph = {}
    forbidden_modules = []
    for manifest, full in [(phase1, False), (closure, True)]:
        for module, row in manifest["project_sources"].items():
            need(row["path"] == module.replace(".", "/") + ".lean", "module path differs")
            raw = check_fingerprint(row)
            imports = import_list(raw)
            project = [m for m in imports if m.startswith("ImbalancedChen.")]
            need(project == row["imports"], "project imports differ: " + module)
            if full:
                need(project == row["project_imports"] and imports == row["all_imports"],
                     "full import inventory differs: " + module)
                need(row["role"] == ("new_owner" if module in EXPECTED_ROOTS else
                                     "existing_canonical_cache_check_only"), "module role differs")
            if module in graph:
                need(graph[module] == project and row["sha256"] ==
                     phase1["project_sources"][module]["sha256"], "overlap differs")
            graph[module] = project
            if FORBIDDEN.search(lean_code(raw.decode())):
                forbidden_modules.append(module)
    need(not forbidden_modules, "forbidden proof token in project closure: " +
         ", ".join(sorted(set(forbidden_modules))))
    active = reachable(graph, EXPECTED_ROOTS)
    union = reachable(graph, phase1["targets"] + EXPECTED_ROOTS)
    need(active == set(closure["project_sources"]) and union == set(graph),
         "closure contains unrelated or missing project sources")
    need(len(active) == closure["project_module_count"] == 386
         and len(phase1["project_sources"]) == 316
         and len(union) == comparison["combined_project_module_count"] == 475,
         "closure count differs")
    new = active - phase1["project_sources"].keys()
    need(len(new - set(EXPECTED_ROOTS)) == 154
         and closure["existing_canonical_cache_check_count"] == 381
         and closure["target_count"] == closure["new_owner_count"] == 5,
         "new-owner/dependency count differs")
    need(not closure["missing"] and not closure["cycles"], "closure contains known failure")

    # The original four-provider receipt is never rewritten or relabelled as current.
    for item in [adoption["historical_four_provider_snapshot"],
                 closure["historical_four_provider_snapshot"]]:
        check_fingerprint(item["static_receipt"])
    need(historical["new_owner_count"] == 4 and historical["project_module_count"] == 358,
         "historical receipt scope differs")
    for record in [adoption, closure, extraction, historical]:
        need(record["compiled"] is False and record["kernel_replayed"] is False
             and record["proof_credit_added"] is False, "unsupported acceptance claim")
    input_names = ["ADOPTION_MANIFEST.json", "SMOOTH_EXTRACTION.json", "SOURCE_CLOSURE.json",
                   "SOURCE_REVIEW.json", "FORMAT_ONLY_DELTA.json", "PROTECTED_INPUT_EXCEPTIONS.json",
                   "STATIC_VERIFICATION.json", "README.md", "verify_source_reuse.py",
                   "BEFORE_DEPENDENCY_UPDATE_BINDINGS.json", "DEPENDENCY_SOURCE_UPDATES.json",
                   "STATIC_VERIFICATION_BEFORE_DEPENDENCY_UPDATES.json",
                   "PROTECTED_INPUT_EXCEPTIONS_BEFORE_DEPENDENCY_UPDATES.json",
                   "run_selected.py", "install_sources.py"]
    return {
        "schema": "p15_original_atlas_proper_power_current_static_verification_v1",
        "status": "PASS_CURRENT_FIVE_OWNER_SOURCE_BYTES_AND_IMPORT_GRAPH_ONLY",
        "source_context_commit": adoption["source_context_commit"],
        "selected_owners": EXPECTED_ROOTS,
        "selected_source_fingerprints": [r["destination"] for r in adoption["owners"]],
        "inputs": [file_fingerprint((HERE / n).relative_to(ROOT).as_posix()) for n in input_names],
        "current_smooth_bytes": len(smooth),
        "format_only_delta_reconstructs_reviewed_bytes": True,
        "original_review_record_preserved_except_explicit_delta_binding": True,
        "exact_smooth_declarations": len(names),
        "original_pointwise_declaration_blocks_verified": len(point_names),
        "current_pointwise_blocks_unchanged": unchanged_current_pointwise,
        "current_pointwise_expression_repaired_blocks": 1,
        "published_first_compile_source_repairs_exactly_reconstructed": 2,
        "published_first_compile_splice_count": 3,
        "adopted_existing_dependency_postimages": 9,
        "dependency_source_changes_in_active_closure": 10,
        "dependency_source_changes_in_phase1_phase2_union": 11,
        "previous_complete_source_closure_exactly_reconstructed": True,
        "external_dependency_manifests": [updates["first_compile_repairs"]["manifest"],
                                          updates["existing_dependency_adoption"]["manifest"]],
        "reviewed_existing_dependency_exception_owners": [
            r["module"] for r in updates["existing_dependency_adoption"]["modules"]
            if r["reviewed_exception_classifications"]],
        "old_new_elaborated_type_equivalence_proved": False,
        "combined_declarations_removed_from_postimages": 27,
        "combined_provider_postimages": post_count,
        "complete_t05_source_and_dictionary_bytes_equal_origins": True,
        "allgroup_exact_single_import_substitution": True,
        "original_protected_input_count": 29,
        "unchanged_protected_inputs": 24,
        "separately_reviewed_published_protected_exceptions": sorted(exceptional),
        "execution_driver_and_installer_bytes_unchanged": True,
        "phase1_source_modules": 316,
        "current_active_source_modules": len(active),
        "phase1_phase2_union_source_modules": len(union),
        "new_owner_count": 5,
        "existing_active_dependencies_cache_check_only": 381,
        "newly_reached_existing_canonical_modules": 154,
        "all_source_hashes_and_imports_checked": True,
        "forbidden_proof_tokens_checked_on_union_and_postimages": True,
        "forbidden_proof_tokens_found": [],
        "missing_project_sources": [], "project_import_cycles": [],
        "historical_four_provider_receipt_unchanged": True,
        "verification_method": "Python raw-byte/Git-blob/import-graph checks only",
        "object_inventory_or_readiness_checked": False,
        "source_or_cache_mutations_by_verifier": 0,
        "Lean_or_Lake_invocations": 0, "cloud_tasks_started": 0,
        "compiled": False, "kernel_replayed": False, "full_owned_accepted": False,
        "proof_credit_added": False, "P1_5_closed": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-receipt", action="store_true")
    args = parser.parse_args()
    result = verify()
    text = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.write_receipt:
        output = HERE / "CURRENT_STATIC_VERIFICATION.json"
        output.write_text(text)
        print(json.dumps({"status": result["status"], "receipt": output.relative_to(ROOT).as_posix(),
                          "sha256": sha(output.read_bytes()), "owners": 5,
                          "active_sources": 386, "union_sources": 475}, ensure_ascii=False))
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
