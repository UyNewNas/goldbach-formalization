"""Static source metadata only; does not evaluate Lean or certificate arithmetic."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[4]
OUT = Path(__file__).resolve().parent
S = ROOT / "docs/source-only/20261102-resume-30s"
R = ROOT / "docs/source-only/20261102-resume-30r"


def record(path, role=None, module=None):
    path = Path(path)
    raw = path.read_bytes()
    item = {
        "path": str(path.relative_to(ROOT)).replace("\\", "/") if path.is_relative_to(ROOT) else str(path),
        "absolute_path": str(path).replace("\\", "/"),
        "raw_sha256": hashlib.sha256(raw).hexdigest(),
        "bytes": len(raw),
    }
    if role:
        item["role"] = role
    if module:
        item["module"] = module
        item["install_as"] = module.replace(".", "/") + ".lean"
    if path.suffix == ".lean":
        source = raw.decode("utf-8-sig")
        item["imports"] = re.findall(r"^import\s+(\S+)", source, re.M)
        item["declarations"] = [
            {"kind": match.group(1), "name": match.group(2), "line": source.count("\n", 0, match.start()) + 1}
            for match in re.finditer(r"^(?:private\s+)?(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+(\S+)", source, re.M)
        ]
    return item


own_roles = {
    "P5OriginalParentSameReserveTransport": "New actual same-parent/same-owner one-reserve integral transport",
    "P5OriginalStoredFifthEndpoint": "New actual72 stored-new block attachments and exact original endpoint",
    "P5OriginalFullFifthFloorIntegral": "New complete actual original stored maximum and full integral terminal",
    "P5RecordedOldFifthBlockTotals": "Prior scalar source materialized with two Inhabited deriving additions only",
}
new_sources = [record(OUT / (name + ".lean"), role, "ImbalancedChen." + name)
               for name, role in own_roles.items()]

direct_paths = {
    "ImbalancedChen.P5HistoricalActualReserve64Budget": R / "fifth_reserve64/P5HistoricalActualReserve64Budget.lean",
    "ImbalancedChen.P5HistoricalActualReserve64Schedule": R / "fifth_reserve64/P5HistoricalActualReserve64Schedule.lean",
    "ImbalancedChen.P1HistoricalFifthFullOriginalFloorEnvelope": ROOT / "docs/source-only/20261102-resume-30q/fifth_parent/P1HistoricalFifthFullOriginalFloorEnvelope.lean",
    "ImbalancedChen.P5FullStoredParentSameOwnerBinding": ROOT / "docs/source-only/20261028-resume-30g/upper_fifth/P5FullStoredParentSameOwnerBinding.lean",
    "ImbalancedChen.P5OriginalParentJensenIntegral": S / "s04_parent_jensen_integral/P5OriginalParentJensenIntegral.lean",
    "ImbalancedChen.P5OriginalTaylorActualMidpointIntegral": S / "s06_five_dim_midpoint/P5OriginalTaylorActualMidpointIntegral.lean",
    "ImbalancedChen.P5OriginalStoredOldArchiveBinding": S / "s07_stored_old_archive_binding/P5OriginalStoredOldArchiveBinding.lean",
}
for name in own_roles:
    direct_paths["ImbalancedChen." + name] = OUT / (name + ".lean")

direct_imports = []
for src in new_sources:
    for name in src["imports"]:
        if name.startswith("Mathlib"):
            direct_imports.append({"imported_by": src["module"], "module": name,
                                   "upstream": "leanprover-community/mathlib4",
                                   "commit": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1"})
        else:
            item = record(direct_paths[name], "Direct exact-source import", name)
            item["imported_by"] = src["module"]
            direct_imports.append(item)

used = [
    ("docs/source-only/20261028-resume-30d/upper_mesh/P1OriginalFifthAdoptedOwnerBank.lean", "parentIntegral; fixedParent; fixedParent_subset_positiveCube"),
    ("docs/source-only/20261028-resume-30e/upper_mesh/P1HistoricalFifthIndexedBankError.lean", "indexedDomain; indexedIntegral; indexedDomain_subset_parent"),
    ("docs/source-only/20261028-resume-30c/upper_mesh/P1OriginalFifthActualB13IntegralError.lean", "positiveKernel_integrableOn_of_subset; positiveKernel_integral_motion_le; rawBox_volume"),
    ("docs/source-only/20261028-resume-30b/upper_mesh/P1OriginalFifthLiteralKernelModulus.lean", "positive_kernel_le_rowMassBound; rowModulus"),
    ("docs/source-only/20261102-resume-30h/upper_fifth/P5FullArchiveOwnerIntegralAssembly.lean", "archiveFifthIntegral_eq_indexed_owner_sum; actual unique source owners"),
    ("docs/source-only/20261028-resume-30f/coefficient_physical/P5OriginalFifthArchiveActualMean.lean", "independent archiveFifthIntegral definition"),
    ("docs/source-only/20261028-resume-30g/upper_fifth/P5SubdivisionStoredParentArchive.lean", "existing actual72 block concatenation; rows_size"),
    ("docs/source-only/20261028-resume-30g/upper_fifth/P5SubdivisionStoredParentTypes.lean", "independent StoredParent sourceIndex/oldQ80/newQ80"),
    ("docs/source-only/20261028-resume-30g/upper_mesh/P1HistoricalFifthOriginalBlockContributions.lean", "previous positional Fin/List conversion pattern; no repeated analytic source"),
    ("docs/source-only/20261028-resume-30f/upper_fifth/P5OriginalGenericWireFloorReceiver.lean", "rowFloorQ; actual child wire analytic source"),
    ("docs/source-only/20261028-resume-30f/upper_fifth/P5HistoricalMask56FullSourceChildren.lean", "indexedWireFloor64/indexedActualReserve64 definitions valid for all source positions"),
    ("docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalTaylorActualSignedKernel.lean", "originalTaylorSignedKernel_eq_literal including s=2; actual signed definition"),
    ("docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalTaylorAffineBranchBinding.lean", "original_new_eq_affine; original_old_eq_selected_affine"),
    ("docs/source-only/20261102-resume-30r/fifth_old_defect/P5OriginalParentJensenRawFields.lean", "originalParentJensenFloorZ/Q; original Q80 scalar definition"),
    ("docs/source-only/20261102-resume-30o/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean", "actual originalRows4 and originalAdmission4 with proved geometry"),
]
reused = []
for relative, role in used:
    path = ROOT / relative
    reused.append(record(path, role, "ImbalancedChen." + path.stem))

upstream = []
for slot in ["s03_parent_jensen_geometry", "s04_parent_jensen_integral", "s05_taylor_weighted_hessian",
             "s06_five_dim_midpoint", "s07_stored_old_archive_binding"]:
    for path in sorted((S / slot).glob("*.lean")):
        if slot == "s07_stored_old_archive_binding" and path.name not in {
            "P5OriginalTaylorRationalData.lean", "P5OriginalStoredOldArchiveBinding.lean"
        }:
            continue
        upstream.append(record(path, "Actual upstream original mathematics", "ImbalancedChen." + path.stem))

stored = [record(ROOT / f"docs/source-only/20261028-resume-30g/upper_fifth/P5SubdivisionStoredBlock{b:03d}.lean",
                 "Existing literal actual stored checkpoint; no rewrite or numerical replay",
                 f"ImbalancedChen.Data.P5SubdivisionStoredBlock{b:03d}") for b in range(72)]

provenance = []
for relative in [
    "docs/source-only/20261028-resume-30g/upper_fifth/REGISTRY.json",
    "docs/source-only/20261102-resume-30q/fifth_parent/REGISTRY.json",
    "docs/source-only/20261102-resume-30r/fifth_old_defect/REGISTRY.json",
    "docs/source-only/20261102-resume-30r/fifth_reserve64/REGISTRY.json",
    "docs/source-only/20261102-resume-30r/reviews/r25_review_archive_history.md",
    "docs/source-only/20261102-resume-30s/BRIEF.md",
]:
    provenance.append(record(ROOT / relative, "Frozen inherited provenance/scope evidence"))
for slot in ["s03_parent_jensen_geometry", "s04_parent_jensen_integral", "s05_taylor_weighted_hessian",
             "s06_five_dim_midpoint", "s07_stored_old_archive_binding"]:
    if (S / slot / "REGISTRY.json").is_file():
        provenance.append(record(S / slot / "REGISTRY.json", "Upstream supplier registry at S08 snapshot"))

original = [
    record(ROOT.parent / "chen-imbalanced-semiprimes/paper/source/manuscript-body.tex", "367–375 actual ancestors/replacement;451–509 separate reserves"),
    record(ROOT.parent / "goldbach-research/fifth-prefix-subdivision-refinement.tex", "113–134 whole-parent maximum;149–164 original exact endpoint and safe rounding"),
    record(ROOT.parent / "goldbach-research/fifth-prefix-taylor-pilot.tex", "actual signed G; original diagonal Hessian; five-dimensional1/24 midpoint"),
]
for name in ["certify_fifth_prefix_jensen.py", "certify_fifth_prefix_adaptive.py",
             "certify_fifth_prefix_taylor_pilot.py", "certify_fifth_prefix_taylor_full.py",
             "certify_fifth_prefix_subdivision.py"]:
    original.append(record(ROOT.parent / "goldbach-research" / name, "Original program read as source only; never executed"))

scalar_original = ROOT / "docs/source-only/20261028-paper-first/cohort03/upper/sources/81adeddb234aa886fbe26ba36f0b1183de9ba632734c0ce7a7b9cf5dab336640/20261028-Upper-Sol6-Phase3-RecordedBlockTotals.lean.txt"
materialization = {
    "original": record(scalar_original),
    "candidate": record(OUT / "P5RecordedOldFifthBlockTotals.lean"),
    "only_transformation": "Two occurrences of deriving DecidableEq, Repr replaced by deriving DecidableEq, Repr, Inhabited; all other bytes unchanged.",
    "byte_transform_matches": scalar_original.read_bytes().replace(
        b"deriving DecidableEq, Repr", b"deriving DecidableEq, Repr, Inhabited") ==
        (OUT / "P5RecordedOldFifthBlockTotals.lean").read_bytes(),
    "reason": "Existing authorBlocks[i]! / independentBlocks[i]! require Inhabited for their respective structures.",
    "source_or_scalar_recalculation": False,
}

registry = {
    "batch": "20261102-resume-30s", "slot": "s08_full_fifth_floor", "owner": "/root/s08_full_fifth_floor",
    "yellow_node_exact": "逐parent真实floor积分包络 → 实际总积分",
    "source_status": "SOURCE_COMPLETE_CANDIDATE_UNCOMPILED", "whole_assigned_yellow_scope_source_complete": True,
    "kernel_verified": False, "formal_credit": 0, "green_claim": False,
    "new_sources": new_sources, "direct_imports": direct_imports, "reused_sources": reused,
    "actual_upstream_sources": upstream, "actual_stored_data_blocks": stored,
    "inherited_provenance": provenance, "original_sources": original, "materialization": materialization,
    "terminal_module": "ImbalancedChen.P5OriginalFullFifthFloorIntegral",
    "terminal_declarations": [
        "original_stored_old_floor_le_parentIntegral", "each_original_stored_floor_sub_reserve",
        "full_original_stored_floor_sub_reserve", "original_fifth_endpoint_sub_reserve", "exists_original_fifth_safe_integral"
    ],
    "actual_instance": {
        "source_indices": "P1HistoricalFifthIndexedOwnerArchive.ArchiveIndex (292633 original positions)",
        "old_new_source": "G72 original StoredParent checkpoint blocks; separate from original143 typed rows",
        "fourth_source": "P5OriginalFourthFifthSourceInputs.originalRows4/originalAdmission4",
        "owner_family": "licensedOwners i e q chi omega; same source index/mask/strict owner/history",
        "total_integral": "P5OriginalFifthArchiveActualMean.archiveFifthIntegral originalRows4 originalAdmission4 e q chi omega",
        "exact_endpoint": "3037921066812732539869/302231454903657293676544",
        "safe_endpoint": "10051/1000000",
        "common_reserve": "Sum of original indexedActualReserve64, paid ONCE by R05",
    },
    "allowed_original_parameters": {
        "universal": "e:Q,0<=e;q:Nat;chi,omega:R;0<omega<19/96",
        "existence": "for every0<omega<=1/800,one rational0<e<3/51200,e<=archiveGateMargin/4,one q>0,chi=e/20,h<=e/20,h<=omega/2",
        "constants_preserved": "c=49044063/25000000;K=8452171/1250000;no changes",
    },
    "removed_mathematical_premises": [
        "Actual stored old floor licence", "Caller Jensen vertex/ratio facts and whole-parent integral bound",
        "Caller Taylor branches/ranges/log/Hessian/midpoint facts for actual strict stored branch",
        "Target-equivalent floor or total-integral fields", "oldBranchDefectQ subtraction",
        "Caller stored-new total equality", "Caller reserve-smallness in existential safe terminal",
    ],
    "remaining_scoped_mathematical_premises": [],
    "unexecuted_finite_sources": [
        "S08 72 actual stored-new block sum bodies and one72-summary fold conversion",
        "Inherited scalar summary decision bodies, original G storedNew/complete64 binding",
        "S03 actual parent geometry,R04 actual scalar bodies,S07 original storedOld max and primitive facts",
        "Inherited archive shape/history/gate/typed authenticity bodies and R05 rational margin body",
    ],
    "separate_remaining_scopes": [
        "Broader P1.4 independent rawNPZ/binary external authenticity",
        "Actual full87 current-parent and common chronology", "Complete All22 and final same-rho realization",
        "Both total reserves and hdensity", "Full PP and final theorem",
    ],
    "difficulty_audit": {
        "class1": "Exact-source import staging, Lean API/elaboration/tactic resources/kernel and axioms pending",
        "class2": "Necessary same-reserve transport,signed-to-positive integral,max/sum attachment supplied",
        "class3_substantive_manuscript_gap_evidence": False,
    },
    "independent_review": "S25 read transport and complete terminal; mathematical source review positive. Final pins/remote evidence separate.",
    "remote_plan": {
        "owner": "root with S02 integration; no local execution",
        "lean": "leanprover/lean4:v4.33.0-rc1", "mathlib": "e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
        "target": "ImbalancedChen.P5OriginalFullFifthFloorIntegral",
        "check_and_print_axioms": [
            "ImbalancedChen.P5OriginalFullFifthFloorIntegral.full_original_stored_floor_sub_reserve",
            "ImbalancedChen.P5OriginalFullFifthFloorIntegral.original_fifth_endpoint_sub_reserve",
            "ImbalancedChen.P5OriginalFullFifthFloorIntegral.exists_original_fifth_safe_integral",
        ],
        "acceptance": "Complete scoped source + exact-source dependency/kernel/finite-body/axiom evidence; reuse identical reliable artifacts first",
    },
    "validation": {
        "source_text_byte_json_only": True, "lean_lake_compiler": "NOT_RUN", "proof_guards": "NOT_RUN",
        "numerical_producer_replay": "NOT_RUN", "git_ci_mutations": False, "children_spawned": False,
    },
    "report": record(OUT / "REPORT.md"), "support_script": record(Path(__file__).resolve()),
}
(OUT / "REGISTRY.json").write_text(json.dumps(registry, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
print(json.dumps({"new_sources": len(new_sources), "stored_blocks": len(stored),
                  "upstream_source_pins": len(upstream), "materialization_bytes_match": materialization["byte_transform_matches"],
                  "registry_sha256": hashlib.sha256((OUT / "REGISTRY.json").read_bytes()).hexdigest()}, ensure_ascii=False))
