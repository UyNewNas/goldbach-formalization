"""Static source/hash inventory only. No Lean, archive, guard or arithmetic evaluation."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
assert OUT == ROOT / "docs/source-only/20261102-resume-30r/fifth_reserve64"

def pin(path, role, names=()):
    p = (ROOT / path).resolve()
    raw = p.read_bytes()
    body = raw.decode("utf-8-sig")
    item = {"path": path, "absolute_path": p.as_posix(), "bytes": len(raw),
            "raw_sha256": hashlib.sha256(raw).hexdigest(), "role": role}
    if p.suffix == ".lean" or p.name.endswith(".lean.txt"):
        ns = re.search(r"^namespace\s+(\S+)", body, re.M)
        module = p.name.removesuffix(".txt").removesuffix(".lean")
        if module.startswith("ImbalancedChen."):
            module = module.removeprefix("ImbalancedChen.")
        item["module"] = "ImbalancedChen." + module
        item["namespace"] = ns.group(1) if ns else None
        item["imports"] = re.findall(r"^import\s+(\S+)", body, re.M)
        decls = []
        for n, line in enumerate(body.splitlines(), 1):
            m = re.match(r"\s*(?:private\s+)?(theorem|def|abbrev|instance)\s+([\w.]+)", line)
            if m and (not names or m.group(2) in names):
                decls.append({"kind": m.group(1), "name": m.group(2), "line": n})
        assert set(names) <= {d["name"] for d in decls}, (path, names)
        item["declarations"] = decls
    return item

specs = [
 ("docs/source-only/20261028-resume-30d/upper_jensen/P5AllChildrenReserveReassembly.lean", "Exact complete64-to-parent reserve reassembly", ["sum64_reserve_eq_single_raw_reserve", "rawRetained", "rawOmitted", "rawBox_real_volume"]),
 ("docs/source-only/20261028-resume-30f/upper_fifth/P5HistoricalMask56FullSourceChildren.lean", "Actual indexed reserve definition; strict licensed-owner selected set", ["indexedActualReserve64", "selected_strict_owners_eq"]),
 ("docs/source-only/20261028-resume-30c/upper_mesh/P1OriginalFifthActualCrossingSections.lean", "Actual selected/firstStop fiber and Fubini motion cost", ["actual_ownerSymmDiff_volume_le"]),
 ("docs/source-only/20261028-resume-30c/upper_mesh/P1OriginalFifthActualB13IntegralError.lean", "Raw grid400 volume; existing literal integral error supplier", ["rawBox_volume", "actual_selected_owner_B13"]),
 ("docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthIndexedOwnerArchive.lean", "Actual source index and licensed-owner constructor; no deduplication", ["ArchiveIndex", "archiveRow", "archiveIndex_card", "licensedOwners", "licensedOwner_selected_zero", "licensedOwner_selected_buffer", "licensedOwner_firstStop_zero", "licensedOwner_firstStop_buffer"]),
 ("docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthIndexedBankError.lean", "Actual zero/buffer indexed domains and zero omission cost", ["indexedDomain", "indexedOmitted", "indexedTrimCost", "indexedDomain_subset_parent"]),
 ("docs/source-only/20261028-resume-30f/upper_mesh/P1HistoricalFifthTypedBaseGeometry.lean", "Original full143-block positive five-coordinate key bounds", ["rows_lower_key_bounds", "archiveRow_baseGeometry", "archiveRow_grid", "licensedIndices_eq_univ", "all_archive_indices_licensed"]),
 ("docs/source-only/20261028-resume-30f/upper_jensen/P5HistoricalCanonicalFilterReserve.lean", "Actual omission history/filter split and per-parent strip rate", ["omittedVolumeCost_exact_canonical_split", "canonicalFilterCost_le_actual_strip_rate"]),
 ("docs/source-only/20261028-resume-30f/upper_jensen/P5HistoricalRejectedCoreReserve.lean", "Original full source mass sum used by H envelope", ["sourceMassSum"]),
 ("docs/source-only/20261028-resume-30e/upper_jensen/P5HistoricalIndexedTrimGeometry.lean", "Actual zero omitted canonical/gate cost split", ["indexedTrimCost_eq_canonical_add_gate"]),
 ("docs/source-only/20261102-resume-30h/upper_jensen/P5HistoricalUniformExtraGatePayment.lean", "Original positive gate margin; no extra gate cost on same schedule", ["licensedOwners_eq_adoptedOwners", "gateRejectedCost_zero", "gateRejectedBankCost_zero", "licensedTrimCost_eq_history_add_filter"]),
 ("docs/source-only/20261102-resume-30h/upper_jensen/P5HistoricalGatePaidReserveSchedule.lean", "Existing envelope, continuity/buffer selection, actual old-literal bound", ["gatePaidEnvelope", "gatePaidEnvelope_continuousAt_zero", "gatePaidEnvelope_zero", "exists_gate_paid_buffer", "full_indexed_error_le_gate_paid_envelope_history"]),
 ("docs/source-only/20261028-resume-30/upper_mesh/P1OriginalFifthJointMeshSchedule.lean", "Original row/bank envelopes and pre-q rational-buffer order", ["rowEnvelope", "bankEnvelope"]),
 ("docs/source-only/20261028-resume-30b/upper_mesh/P1OriginalFifthLiteralKernelModulus.lean", "Actual nonnegative row mass/modulus", ["rowModulus_nonneg", "one_le_rowMassBound"]),
 ("docs/source-only/20261102-resume-30q/fifth_parent/P1HistoricalFifthActualHistoryAdmission.lean", "Actual all-row history emptiness and zero cost at same witnesses", ["archive_canonicalHistory_empty", "archive_canonicalHistoryCost_zero", "archive_canonicalHistoryBankCost_zero"]),
 ("docs/source-only/20261102-resume-30q/fifth_parent/P1HistoricalFifthTypedHistoryAdmission.lean", "Inherited143 actual typed history guard bodies; UNEVALUATED", ["archiveRow_original_order", "archiveRow_original_third_gap"]),
 ("docs/source-only/20261102-resume-30q/fifth_parent/P1HistoricalFifthFullOriginalFloorEnvelope.lean", "Existing Q consumer only; full actual reserve deducted", ["full_original_stored_floor_envelope"]),
 (".lake/proof-continuation/source-reviews/drafts/20261028-Upper-PhaseB-GammaEta/ImbalancedChen.P1OriginalFifthMovingMeshFubiniBridge.lean.txt", "Independent actual ownerUnion/SymmDiff definitions", ["ownerUnion", "ownerSymmDiff"]),
 (".lake/proof-continuation/source-reviews/drafts/20261025a-P1/fifth-unitbox-disjoint-gain/P1FifthUnitBoxGainDecomposition.lean", "Original actual rawOwnerDomain=rawBox intersect fullCell", ["rawOwnerDomain"]),
 (".lake/proof-continuation/source-reviews/drafts/20261024zz-GitSourceCheckpoint/snapshot/ImbalancedChen/P4AAll22OriginalKLedger.lean", "Original separate density and compiler reserve constants", ["densityReserve", "compilerReserve", "densityReserve_pos", "original_density_reserve_split"]),
]
reused = [pin(p, role, names) for p, role, names in specs]
new = []
for leaf in ("P5HistoricalActualReserve64Budget.lean", "P5HistoricalActualReserve64Schedule.lean"):
    p = (OUT / leaf).relative_to(ROOT).as_posix()
    item = pin(p, "New strict source; uncompiled; guards unevaluated")
    item.update({"intended_install_module": item["module"],
                 "installation_target": "ImbalancedChen/" + leaf,
                 "compiled": False, "kernel_verified": False, "source_only": True})
    text = (OUT / leaf).read_text(encoding="utf-8")
    assert not re.search(r"^\s*(axiom|sorry|admit)\b|\bnative_decide\b", text, re.M)
    new.append(item)
assert [len(x["declarations"]) for x in new] == [8, 3]
by_module = {x["module"]: x for x in reused + new}
for item in new:
    item["direct_import_bindings"] = [
        {"module": m, "path": by_module[m]["path"], "raw_sha256": by_module[m]["raw_sha256"]}
        for m in item["imports"]]

evidence = [
 pin("docs/source-only/20261102-resume-30r/BRIEF.md", "Task constraints read"),
 pin("docs/source-only/20261102-resume-30q/fifth_parent/REPORT.md", "Q actual reserve remaining boundary"),
 pin("docs/source-only/20261102-resume-30q/fifth_parent/REGISTRY.json", "Exact inherited143 typed/72 stored object pins; reused, not reconstructed"),
 pin("docs/source-only/20261102-resume-30q/reviews/q23_review_data_trace.md", "Final independent Q scope review read"),
 pin("../goldbach-research/fifth-prefix-subdivision-refinement.tex", "Original full64 partition, whole-parent replacement and exact strict floor margin"),
 pin("../goldbach-research/fifth-prefix-adaptive-refinement.tex", "Original pre-N finite-buffer order and limiting nonnegative saving"),
 pin("../goldbach-research/certify_fifth_prefix_subdivision.py", "Original split_bound/full source read only; not executed"),
 pin("../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex", "Original distinct reserves and normalization"),
]
registry = {
 "schema": "source-only-resume-30r-registry-v1", "task_number": 5,
 "task_id": "fifth_reserve64", "owner": "/root/r05_fifth_reserve64",
 "assigned_model": "gpt-6.1-sol", "assigned_reasoning_effort": "xhigh",
 "write_scope": "docs/source-only/20261102-resume-30r/fifth_reserve64",
 "status": "ACTUAL_FULL_RESERVE64_PAYMENT_SOURCE_SUPPLIED_UNCOMPILED",
 "local_source_step_complete": True, "task_complete": False,
 "broad_target_status": "OPEN", "compiled": False, "kernel_verified": False,
 "formal_credit": 0, "ready_to_install": False,
 "new_sources": new, "reused_sources": reused, "manuscript_and_review_evidence": evidence,
 "new_finite_bodies": [{"path": new[1]["path"], "scope": "exists_original_safe_fifth_margin_payment.hmargin", "kind": "closed rational positivity by norm_num", "status": "UNEVALUATED"}],
 "inherited_guards": "All original typed/history/gate/key/authentication guards remain UNEVALUATED; source hashes are not semantic authentication",
 "results": [
  "Exact actual buffered retained=indexedDomain(z=e), fixedParent=actual raw box",
  "Actual buffered omitted subset of zero omitted union actual same-owner symmetric difference",
  "Per original index actualReserve64 <= existing rowEnvelope + actual indexedTrimCost",
  "On original gate/history schedule actual indexedTrimCost=canonicalFilterCost",
  "All292633 actual original indices reserve sum <= existing gatePaidEnvelope",
  "One rational e before one aligned q gives actual reserve64 sum < any eta with same original owners/history",
  "Original densityReserve/8 and exact original subdivision-to10051/10^6 strict margin can both be met by the same schedule"
 ],
 "removed_caller_premises": ["total actual reserve64 smallness", "per-parent omitted volume smallness", "buffered retained=zero-domain identification"],
 "unchanged_ranges": {"grid":400, "children_per_parent":64, "omega":"0<omega<=1/800", "e":"0<e<3/51200 and e<=archiveGateMargin/4", "chi":"e/20", "mesh":"h<=e/20 and h<=omega/2"},
 "normalization": "Original4 included in existing kernels/floors; no factor64, quarter, sorting factorial or owner cardinality added",
 "remaining_obligations": [
  "Elaboration, import staging and kernel acceptance of all new/inherited sources",
  "Truth and resource feasibility of inherited archive guards and new rational margin body",
  "Original independent binary/typed authentication guards remain unexecuted",
  "Old Jensen/Taylor oldBranchDefectQ supplier assigned to R04",
  "Complete stored floor endpoint and same physical rho/full87/All22/two complete reserves/PP/K remain separate"
 ],
 "difficulty": {"class2": "Actual omitted-domain and full64 reserve conversion supplied", "class1": "Uncompiled API/staging/guard acceptance", "manuscript_contradiction_established":False},
 "validation": {"source_inventory":"PASS", "new_declaration_count":11, "direct_import_pins":"PASS", "raw_hashes":"PASS", "json":"PASS", "lean_lake_compiler_ci":"NOT_RUN", "finite_guard_execution":"NOT_RUN", "numeric_or_integral_replay":"NOT_RUN", "git_operations":False, "old_files_modified":False, "subagents_spawned":False},
 "independent_review": "Pending root-assigned R25; no independent PASS claimed",
 "report": pin((OUT / "REPORT.md").relative_to(ROOT).as_posix(), "Scope and proof explanation"),
 "support_script": pin((OUT / "build_registry.py").relative_to(ROOT).as_posix(), "Static metadata only"),
}
target = OUT / "REGISTRY.json"
target.write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
assert json.loads(target.read_text(encoding="utf-8"))["validation"]["new_declaration_count"] == 11
print(json.dumps({"new_sources": [{"path": x["path"], "bytes":x["bytes"], "raw_sha256":x["raw_sha256"], "declarations":len(x["declarations"])} for x in new], "reused_sources":len(reused), "registry":target.as_posix()}, ensure_ascii=False))
