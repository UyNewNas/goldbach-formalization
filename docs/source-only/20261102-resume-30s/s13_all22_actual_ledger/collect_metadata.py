"""Read-only source/byte metadata. No Lean, evaluation, replay or arithmetic certificate."""
from pathlib import Path
import hashlib
import json
import re

here = Path(__file__).resolve().parent
repo = here.parents[3]
project = repo.parent

def record(path, role):
    p = Path(path)
    if not p.is_absolute():
        p = repo / p
    raw = p.read_bytes()
    text = raw.decode("utf-8-sig")
    out = {"path": p.as_posix(), "role": role, "bytes": len(raw),
           "raw_sha256": hashlib.sha256(raw).hexdigest(), "line_count": len(text.splitlines())}
    if p.suffix == ".lean":
        out["direct_imports"] = [{"module": m.group(1), "line": i}
            for i, line in enumerate(text.splitlines(), 1)
            if (m := re.match(r"^import\s+(\S+)", line))]
        out["namespace_lines"] = [{"namespace": m.group(1), "line": i}
            for i, line in enumerate(text.splitlines(), 1)
            if (m := re.match(r"^namespace\s+(\S+)", line))]
        out["declarations"] = [{"kind": m.group(1), "name": m.group(2), "line": i}
            for i, line in enumerate(text.splitlines(), 1)
            if (m := re.match(r"^(?:private\s+)?(?:noncomputable\s+)?(def|abbrev|theorem|lemma|structure)\s+(\S+)", line))]
    return out

reused_paths = {
    "ImbalancedChen.P4AAll22ActualCompactPositiveBinding": "ImbalancedChen/P4AAll22ActualCompactPositiveBinding.lean",
    "ImbalancedChen.P4AActualFirstIntegralSelectedK": "ImbalancedChen/P4AActualFirstIntegralSelectedK.lean",
    "ImbalancedChen.P4AAll22AdditionalActualSuppliers": "ImbalancedChen/P4AAll22AdditionalActualSuppliers.lean",
    "ImbalancedChen.P4AAll22OriginalKLedger": "ImbalancedChen/P4AAll22OriginalKLedger.lean",
    "ImbalancedChen.P4AOrdinaryRootAll22Dictionary": "ImbalancedChen/P4AOrdinaryRootAll22Dictionary.lean",
    "ImbalancedChen.P4AOrdinaryRootFirstIntegral": "ImbalancedChen/P4AOrdinaryRootFirstIntegral.lean",
    "ImbalancedChen.P2OriginalFirstIntegralEndpoint": "ImbalancedChen/P2OriginalFirstIntegralEndpoint.lean",
    "ImbalancedChen.P2FirstIntegralPolynomialEnclosure": "ImbalancedChen/P2FirstIntegralPolynomialEnclosure.lean",
    "ImbalancedChen.CurrentUpperEighteenBudget": "ImbalancedChen/CurrentUpperEighteenBudget.lean",
    "ImbalancedChen.Part4ActualThirdFiniteDensityReserve": "ImbalancedChen/Part4ActualThirdFiniteDensityReserve.lean",
    "ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover": "ImbalancedChen/P1OriginalFifthGrid400RefinedFullBoxCover.lean",
    "ImbalancedChen.P2OriginalCompactWholeFunctionalEndpoint": "docs/source-only/20261102-resume-30o/compact_total_endpoint/P2OriginalCompactWholeFunctionalEndpoint.lean",
    "ImbalancedChen.P2OriginalCompactQ80CompleteSoundness": "docs/source-only/20261102-certificates-l/compact_q80_encloser/P2OriginalCompactQ80CompleteSoundness.lean",
    "ImbalancedChen.P2OriginalCompactQ80Encloser": "docs/source-only/20261102-certificates-l/compact_q80_encloser/P2OriginalCompactQ80Encloser.lean",
    "ImbalancedChen.P2OriginalCompactConcreteLoop": "docs/source-only/20261102-certificates-l/compact_run_certificate/P2OriginalCompactConcreteLoop.lean",
    "ImbalancedChen.P2OriginalCompactCachedEndpointCandidate": "docs/source-only/20261102-certificates-l/compact_run_certificate/P2OriginalCompactCachedEndpointCandidate.lean",
    "ImbalancedChen.P2OriginalCompactCachedRun": "docs/source-only/20261102-certificates-l/compact_run_certificate/P2OriginalCompactCachedRun.lean",
    "ImbalancedChen.P2OriginalCompactQ80FixedBindings": "docs/source-only/20261102-resume-30n/compact_fixed_bindings/P2OriginalCompactQ80FixedBindings.lean",
    "ImbalancedChen.P2OriginalCompactArchivedTotalCandidate": "docs/source-only/20261102-resume-30o/compact_total_endpoint/P2OriginalCompactArchivedTotalCandidate.lean",
    "ImbalancedChen.P4AActualCompleteCatalogFiveCapPayment": "docs/source-only/20261102-resume-30r/actual_density_reserve/P4AActualCompleteCatalogFiveCapPayment.lean",
    "ImbalancedChen.P4AActualSmallTailDensityCatalogue": "docs/source-only/20261102-resume-30r/actual_density_reserve/P4AActualSmallTailDensityCatalogue.lean",
    "ImbalancedChen.P4AActualOwnCubeCapPayment": "docs/source-only/20261102-resume-30r/actual_density_reserve/P4AActualOwnCubeCapPayment.lean",
    "ImbalancedChen.P4AActualBufferedFallbackCapPayment": "docs/source-only/20261102-resume-30r/actual_density_reserve/P4AActualBufferedFallbackCapPayment.lean",
    "ImbalancedChen.P4ACatalogFiveSmallThirdPayment": "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveSmallThirdPayment.lean",
    "ImbalancedChen.P4ACatalogFiveGlobalLossReduction": "docs/source-only/20261102-resume-30r/catalog5_global_losses/P4ACatalogFiveGlobalLossReduction.lean",
    "ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve": "docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean",
    "ImbalancedChen.P4AOriginalFourteenThirteenCurrentSource": "docs/source-only/20261102-resume-30r/all22_actual_sources/P4AOriginalFourteenThirteenCurrentSource.lean",
    "ImbalancedChen.P4AOriginalSecondPhysicalIntegral": "docs/source-only/20261102-resume-30j/all22_suppliers/P4AOriginalSecondPhysicalIntegral.lean",
    "ImbalancedChen.P4AOriginalBufferedArchiveContinuation": "docs/source-only/20261102-resume-30r/full_buffered_policy/P4AOriginalBufferedArchiveContinuation.lean",
    "ImbalancedChen.P5OriginalFourthFifthSourceInputs": "docs/source-only/20261102-resume-30o/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean",
    "ImbalancedChen.P4AOriginalCausalHistory": "docs/source-only/20261102-resume-30o/all22_common_history/P4AOriginalCausalHistory.lean",
    "ImbalancedChen.P4AOriginalCommonArchiveSchedule": "docs/source-only/20261102-resume-30o/all22_common_history/P4AOriginalCommonArchiveSchedule.lean",
    "ImbalancedChen.P1HistoricalFifthCommonPolicyInputs": "docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthCommonPolicyInputs.lean",
    "ImbalancedChen.P2OriginalFourteenCommonScheduleEndpoint": "docs/source-only/20261102-resume-30q/saving16_scope/P2OriginalFourteenCommonScheduleEndpoint.lean",
    "ImbalancedChen.P2OriginalFourteenWholeFamilyLower": "docs/source-only/20261102-resume-30o/saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean",
    "ImbalancedChen.P2OriginalSaving16CommonOldPolicy": "docs/source-only/20261102-resume-30k/saving16_glue/P2OriginalSaving16CommonOldPolicy.lean",
    "ImbalancedChen.P2OriginalSaving16OwnedIntegral": "docs/source-only/20261102-resume-30o/saving16_pulling_ownership/P2OriginalSaving16OwnedIntegral.lean",
    "ImbalancedChen.P2Winner9ActualEightSimplexMoment": "docs/source-only/20261102-resume-30p/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean",
}
new_sources = []
for p in sorted(here.glob("*.lean")):
    r = record(p, "new strict actual-source binding; UNCOMPILED")
    module = "ImbalancedChen." + p.stem
    r.update({"intended_module": module, "intended_install_path": "ImbalancedChen/" + p.name,
              "compiled": False, "kernel_verified": False})
    reused_paths[module] = str(p)
    new_sources.append(r)

for r in new_sources:
    for imp in r["direct_imports"]:
        evidence = record(reused_paths[imp["module"]], "exact direct import resolution")
        imp.update({"source_path": evidence["path"], "raw_sha256": evidence["raw_sha256"]})

source_map = repo / "docs/source-only/20261102-resume-30r/all22_actual_sources/ALL22_SOURCE_MAP.json"
original = json.loads(source_map.read_text(encoding="utf-8-sig"))
entries = []
for item in original["entries"]:
    out = {k: item[k] for k in ["slot_one_based", "id", "source", "field", "value", "accounting_role", "source_artifact"]}
    slot = item["slot_one_based"]
    out["all22_same_final_policy_supplied"] = False
    out["s13_status"] = ("ACTUAL_ORDINARY_SOURCE_ENDPOINT_ON_ORIGINAL_SHARED_ARCHIVE; FINAL_POLICY_TRANSFER_OPEN" if slot == 5 else
                         "ACTUAL_CURRENT6_MINUS_NEW14_Q96_ON_SAME_ARCHIVE_AS_SLOT5; FINAL_POLICY_TRANSFER_OPEN" if slot == 16 else
                         "NOT_DISCHARGED_BY_S13; REUSE_OR_COORDINATED_ACTUAL_SOURCE_REQUIRED")
    out["s13_export"] = ("ImbalancedChen.P4AOriginalCatalogFiveFourteenJointSchedule.exists_actual_catalog_five_and_fourteen_schedule" if slot in [5,16] else None)
    entries.append(out)
terminal_map = {"scope": "Exact original 22 provenance plus narrow S13 terminal map; not a complete actual All22 ledger",
                "numerical_evaluation": False, "full_target_source_complete": False,
                "inherited_map": record(source_map, "frozen R06 provenance; values copied as strings"),
                "catalog": original["catalog"], "entries": entries}
(here / "ALL22_TERMINAL_MAP.json").write_text(json.dumps(terminal_map, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")

context = [
    (project / "chen-imbalanced-semiprimes/paper/source/manuscript-body.tex", "original statement; lines367-375,453-509,1327-1361"),
    (project / "1_+_1.748_lean_proofs/main.md", "authoritative yellow P4A.4 lines118,129"),
    (project / "output/r-batch-20261102/publication/payload/docs/source-only/20261102-resume-30r/SOURCE_MANIFEST.json", "frozen R source manifest"),
    (source_map, "original 22 source map"),
    (repo / "docs/source-only/20261102-resume-30r/reviews/r25_review_archive_history.md", "independent original archive/history review"),
    (repo / "docs/source-only/20261102-resume-30r/reviews/r26_review_reserves_density.md", "independent R07/R10 complete-payment review"),
    (repo / "docs/source-only/20261102-resume-30r/all22_actual_sources/REPORT.md", "frozen R06 scope"),
    (repo / "docs/source-only/20261102-resume-30r/all22_actual_sources/REGISTRY.json", "frozen R06 exact source provenance"),
    (repo / "docs/source-only/20261102-resume-30r/actual_density_reserve/REPORT.md", "frozen R10 complete payment and separate reserves"),
    (repo / "docs/source-only/20261102-resume-30r/catalog5_global_losses/REPORT.md", "frozen R07 entire ordinary catalog5 payment"),
]
registry = {
    "schema_version": 1, "batch": "20261102-resume-30s", "task": "S13",
    "owner": "/root/s13_all22_actual_ledger", "write_scope": here.as_posix(),
    "yellow_node": "P4A.4, including all actual 4 positive terms, 22 savings and same-policy reserves",
    "status": "SOURCE_ONLY_FOUR_POSITIVE_BINDING_AND_ACTUAL_COMMON_ARCHIVE_SLOTS5_16",
    "whole_assigned_yellow_source_complete": False, "full_target_status": "OPEN",
    "compiled": False, "kernel_verified": False, "formal_credit": 0,
    "finite_guards_status": "UNEVALUATED_INHERITED; NO_NEW_FINITE_RUN",
    "direct_imports_resolved": True, "transitive_import_closure_certified": False,
    "pins": {"lean": "leanprover/lean4:v4.33.0-rc1", "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
             "native_upstream": "subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958",
             "public_parent": "e2a05f73d5f169fff847d72dcfcc66ec54ad4f87"},
    "constants_unchanged": {"c": "49044063/25000000", "K": "8452171/1250000", "Theta": "299/500", "rho": "19/96", "mu": "25/128"},
    "new_lean_sources": new_sources,
    "reused_sources": [dict(record(path, "exact existing source evidence"), intended_module=module)
                       for module,path in reused_paths.items() if not module.startswith("ImbalancedChen.P4AOriginalCatalogFive") and module != "ImbalancedChen.P4AOriginalFourPositiveEndpoints"],
    "context_sources": [record(p,role) for p,role in context],
    "removed_premises": ["sharp first/compact bounds in actual four-positive binding; supplied existing declarations",
        "R10 old-data positivity and all literal mesh/width assumptions on concrete R06 schedule",
        "independent incompatible q choices for original actual catalog5 and original14 current-parent endpoint"],
    "remaining_mathematical_obligations": ["complete original slot1 endpoint/licences; slots2/3 arithmetic/current-policy endpoint transfer (S08 now supplies the original full fifth integral floor)",
        "full actual sixth/eighth chronology, current-parent increments, endpoint conversions and multiplicities on one final policy",
        "original13 actual arithmetic/prime-integral conversion; S12 analytic source is not that conversion",
        "full87/compiled-policy identification and final signed-gain transfer",
        "remaining total density reserve and independent full compiler reserve; third u_d/4 already spent once"],
    "finite_evidence_hold": "L cached two-million-split original compact candidate and inherited rational endpoint bodies require same-source kernel evidence",
    "scope_review": {"reviewer": "/root/s27_review_density", "kind": "NARROW_STATIC_SOURCE_PASS_REPORTED", "whole_yellow_close": False},
    "reports": [record(here / "REPORT.md", "complete terminal and scope report"),
                record(here / "ALL22_TERMINAL_MAP.json", "literal original22 status map")],
    "remote_audit_declarations": [
        "ImbalancedChen.P4AOriginalFourPositiveEndpoints.actual_positive_entry_le_original",
        "ImbalancedChen.P4AOriginalFourPositiveEndpoints.original_root_add_third_le_original_positive_sum",
        "ImbalancedChen.P4AOriginalCatalogFiveArchiveSchedule.original_slot_five_deficit_le_cap_error",
        "ImbalancedChen.P4AOriginalCatalogFiveArchiveSchedule.exists_actual_original_catalog_five_schedule",
        "ImbalancedChen.P4AOriginalCatalogFiveFourteenJointSchedule.exists_actual_catalog_five_and_fourteen_schedule"],
    "remote_validation": "Root-only isolated exact-source integration; reuse identical reliable artifacts; check declarations and print axioms; inherited cached compact finite proof must be checked, never replaced by scalar ledger arithmetic."
}
(here / "REGISTRY.json").write_text(json.dumps(registry, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
print(json.dumps({"new_lean_sources": len(new_sources), "reused_sources": len(registry["reused_sources"]),
                  "whole_yellow_source_complete": False,
                  "registry_sha256": hashlib.sha256((here/"REGISTRY.json").read_bytes()).hexdigest()}))
