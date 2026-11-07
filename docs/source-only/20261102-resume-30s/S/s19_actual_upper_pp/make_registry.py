"""Read source bytes and serialize S19 metadata; execute no mathematical code."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(r"E:\timot\Documents\FilesForGPT\Myath\goldbach-proof-continuation")
HERE = Path(__file__).resolve().parent
PAPER = ROOT.parent / "chen-imbalanced-semiprimes/paper/source/manuscript-body.tex"

NEW = [
    HERE / "P4BActualUpperTrimPayment.lean",
    HERE / "P4BCommonRefinedUpperTailAndTrim.lean",
]
REUSED = [
    "ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean",
    "ImbalancedChen/ActualUpperCountingInputs.lean",
    "ImbalancedChen/Part3PolynomialResidueDivisorBound.lean",
    "ImbalancedChen/BoundaryArbitraryLog.lean",
    "ImbalancedChen/P5OriginalSharpPrimeSynthesis.lean",
    "docs/source-only/20261102-resume-30r/actual_same_rho_pp/P4BActualUpperRoughPrimeReserveZero.lean",
    "docs/source-only/20261102-resume-30r/actual_same_rho_pp/P4BActualUpperModesRoughPrimePaid.lean",
    "docs/source-only/20261102-resume-30r/gamma_outer_theta/P2GammaJointLabels.lean",
    "docs/source-only/20261102-resume-30r/gamma_outer_theta/P2GammaJointUpperPayment.lean",
    "docs/source-only/20261102-resume-30r/gamma_outer_theta/P2GammaPairThetaZero.lean",
    "docs/source-only/20261102-resume-30r/gamma_grid_level/P2GammaChosenLogGridBudget.lean",
    "docs/source-only/20261102-resume-30r/gamma_grid_level/P2GammaRetainedLowRankLevel.lean",
    "docs/source-only/20261102-resume-30r/gamma_grid_level/P2GammaChosenGridLocalConductor.lean",
    "docs/source-only/20261102-resume-30j/upper_pp/P4BArbitraryWidthUpperPairProfile.lean",
    "docs/source-only/20261102-resume-30j/upper_pp/P4BArbitraryWidthUpperPairHBNormalization.lean",
    "docs/source-only/20261102-resume-30k/upper_row_mode/P4BUpperPairOrderedRowGeometry.lean",
    "docs/source-only/20261102-resume-30k/upper_row_mode/P4BUpperPairOrderedRowModes.lean",
    "docs/source-only/20261102-resume-30k/upper_fourier_tail/P4BArbitraryWidthUpperBlockGeometry.lean",
    "docs/source-only/20261102-resume-30k/upper_fourier_tail/P4BArbitraryWidthUpperPostModulusTail.lean",
    "docs/source-only/20261102-resume-30k/upper_fourier_tail/P4BOriginalUpperFourierTailPaid.lean",
    "docs/source-only/20261102-resume-30m/gamma_short_fibre_bv/P2OriginalGammaDivisorNorm.lean",
    "docs/source-only/20261028-resume-30e/transfer_power/P5ActualCommonRefinedRange.lean",
    "docs/source-only/20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedConstructor.lean",
    "docs/source-only/20261028-resume-30c/transfer_power/P5ProperPowerPhysicalPolynomialPayment.lean",
    "docs/source-only/20261028-resume-30b/transfer_power/P5ProperPowerActualReciprocalTail.lean",
    "docs/source-only/20261028-resume-30b/transfer_lambda/Part3AllKFamilyProperPowerSaving.lean",
    "docs/source-only/20261028-resume-30/transfer_power/P5ProperPowerSignedModulusPayment.lean",
    "docs/source-only/20261028-resume-30f/transfer_lambda/P5OriginalSingletonLowerTrimPaid.lean",
    "docs/source-only/20261028-resume-30f/pp_fourier/P5OriginalPrimeAllGroupHBDiscrepancy.lean",
    "docs/source-only/20261028-resume-30f/pp_fourier/P5IndependentPrimeSourceWordDictionary.lean",
    "docs/source-only/20261028-resume-30f/pp_fourier/P5OriginalPrimeAtlasReserveBranches.lean",
    "docs/source-only/20261028-resume-30c/pp_derivatives/P5ActualEtaPsiOccurrenceBudget.lean",
    ".lake/proof-continuation/source-reviews/drafts/20261028-PrimeProducts-HBIdentity-IntegerAtlasPhase8/P5LicensedOriginalIntegerProfile.lean",
    ".lake/proof-continuation/source-reviews/drafts/20261028-Transfer-Sol6-PhaseB-OuterException/P5ProperPowerSignedMeanHBTransport.lean",
    "docs/source-only/20261028-paper-first/cohort04/transfer/sources/cb0a61efad03499d058999c3ce28a72d487a5ccd64dc1ba05bb6ec7fbb4b81c5/Part3ActualOriginalProperPowerChartBridge.lean",
    "docs/source-only/20261028-paper-first/cohort04/transfer/sources/66b026ca1a0d8a3683938cf4f93eb38d6e9a26533abd836f5df9320e1424371b/Part3OriginalProperPowerChartCount.lean",
]
EVIDENCE = [
    "docs/source-only/20261102-resume-30s/BRIEF.md",
    "docs/source-only/20261102-resume-30r/actual_same_rho_pp/REPORT.md",
    "docs/source-only/20261102-resume-30r/actual_same_rho_pp/REGISTRY.json",
    "docs/source-only/20261102-resume-30r/gamma_outer_theta/REPORT.md",
    "docs/source-only/20261102-resume-30r/gamma_outer_theta/REGISTRY.json",
    "docs/source-only/20261102-resume-30r/gamma_grid_level/REPORT.md",
    "docs/source-only/20261102-resume-30r/gamma_grid_level/REGISTRY.json",
    "docs/source-only/20261102-resume-30r/reviews/r29_review_gamma_pp.md",
    "docs/source-only/20261102-resume-30k/upper_fourier_tail/REPORT.md",
    "docs/source-only/20261102-resume-30k/upper_row_mode/REPORT.md",
]

def record(path):
    raw = path.read_bytes()
    lines = raw.decode("utf-8-sig").splitlines()
    try:
        rel = path.relative_to(ROOT).as_posix()
    except ValueError:
        rel = path.as_posix()
    out = dict(path=rel, absolute_path=path.as_posix(), raw_sha256=hashlib.sha256(raw).hexdigest(),
               bytes=len(raw), lines=len(lines))
    if path.suffix == ".lean":
        out.update(module="ImbalancedChen." + path.stem,
                   intended_install_path="ImbalancedChen/" + path.name,
                   direct_imports=[dict(line=i, module=line.split(maxsplit=1)[1])
                                   for i, line in enumerate(lines, 1) if line.startswith("import ")],
                   namespace_lines=[dict(line=i, text=line) for i, line in enumerate(lines, 1)
                                    if line.startswith("namespace ")],
                   declarations=[])
        for i, line in enumerate(lines, 1):
            match = re.match(r"(?:@\[.*?\]\s*)?(?:private\s+)?(theorem|lemma|def|abbrev|structure)\s+([^\s({:]+)", line)
            if match:
                out["declarations"].append(dict(kind=match[1], name=match[2], line=i, header=line))
    return out

new_records = [record(p) for p in NEW]
reuse_records = [record(ROOT / p) for p in REUSED]
lookup = {r["module"]: r for r in new_records + reuse_records}
for rec in new_records:
    for imp in rec["direct_imports"]:
        source = lookup[imp["module"]]
        imp.update(source_path=source["path"], raw_sha256=source["raw_sha256"], bytes=source["bytes"])
    rec.update(compiled=False, kernel_verified=False, formal_credit=0)

# Read and preserve the inherited registries' full structured source metadata.
inherited = []
for rel in EVIDENCE:
    if rel.endswith("REGISTRY.json"):
        prior = json.loads((ROOT / rel).read_text(encoding="utf-8-sig"))
        inherited.append(dict(path=rel, status=prior.get("status"),
                              compiled=prior.get("compiled"), kernel_verified=prior.get("kernel_verified"),
                              top_level_keys=list(prior)))

result = dict(
    task="S19 actual upper same-rho PP",
    status="PARTIAL_ACTUAL_TRIM_AND_CONCRETE_SUPPORT_APPLICATION_WHOLE_P3_6_HOLD",
    whole_assigned_scope_source_complete=False,
    compiled=False, kernel_verified=False, formal_credit=0, finite_bodies="UNEVALUATED",
    original_manuscript=record(PAPER),
    source_pins=dict(lean="leanprover/lean4:v4.33.0-rc1", mathlib="e4c91783ca8e6a7c693ae624ade32fd22d4e43c1",
                     native="subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958",
                     parent_commit="e2a05f73d5f169fff847d72dcfcc66ec54ad4f87"),
    original_terminal=dict(path="ImbalancedChen/P4BCurrentSmoothBadUpperSuppliers.lean", line=45,
                           premise="hUniformPP", instance="literal attachedUpperModuli and attachedUpperCoefficient at the same delta/epsilon/retain/cap; rank two smoothPhysicalPairOuterRamp; every legal fixed width"),
    unchanged_constants=dict(c="49044063/25000000", K="8452171/1250000", rough_cutoff="19/96"),
    new_sources=new_records, reused_sources=reuse_records,
    evidence_sources=[record(ROOT / p) for p in EVIDENCE], inherited_registry_metadata=inherited,
    report=record(HERE / "REPORT.md"),
    newly_supplied=[
        "Ordered original-prime low-product fibre count from existing orderedFactors/fouvryTau, preserving all labels and repeated primes.",
        "Complete actual arbitrary-width upper trimReserve logAccuracy after the full same signed physical modulus sum, conditional only on same-rho polynomial active cap.",
        "Existing policy8 .599 support instantiated at literal attachedUpperCoefficient, nu=1, epsilon<=1/1000, preserving arbitrary enumeration cap.",
        "Existing whole K Fourier tail and new trim actually applied to that concrete policy8 with no remaining active-support premise for that instance."],
    new_premises=["No new PP/density/source-mass/desired-error/source-equality assumptions.",
                  "Generic actual trim has primitive same-coefficient active-cap<=N^theta, fixed theta>=0.",
                  "Concrete structural policy8 instance uses existing OriginalData and 0<=d.e, nu=1 and epsilon<=1/1000."],
    removed_final_premises=dict(hUniformPP=0, hdensity=0, hLower=0, hUpper=0,
                               hstarts=0, h34=0, h5=0, h6=0, h7=0, h8=0, h9=0, h1011=0),
    remaining_full_scope=[
        "Final full87 buffered retain/cap equality to actual licensed physical coefficient.",
        "Full same-integer-rho enhanced factorization cover retaining every full/selected square and complete physical levels.",
        "Actual selected common physical Q versus t-dependent rootQ and nonnegative occurrence/scalar source dictionary.",
        "Positive-Theta relative payment, all outer joint lower/order/trim costs in original quantifier order.",
        "Full actual proper-powerReserve chart/rough-projector/scalar payment, preserving its minus sign.",
        "Complete retained arithmetic medium/SW/classical BV/one-long/two-long mode estimates and coupled Mellin/Fourier amplitude norms/restoring scalars.",
        "Actual normalized trace, full spectral classes and true energy/7/32 source supplied by S20/S21/S22.",
        "All retained original positive switched/marked/ordinary attached-upper source families; final hUniformPP and independent hdensity."],
    difficulty=dict(new_trim="class II supplied omitted deduction", validation="class I unexecuted import/API/elaboration",
                    full_scope="genuine unprovided original-source analytic obligations; no substantive manuscript counterexample established"),
    remote_plan=dict(owner="root", targets=[r["module"] for r in new_records],
                     reuse_identical_artifacts_first=True, local_execution_permitted=False,
                     scope="elaborate and kernel/axiom audit bounded source terminals; successful run is not whole P3.6 closure"),
    peer_review=dict(owner="/root/s29_review_actual_pp", status="running independent bounded-source review; no mathematical substitution issue reported; final bytes require frozen review"),
)
(HERE / "REGISTRY.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
for item in new_records:
    print(item["path"], item["raw_sha256"], item["bytes"])
print("REPORT", result["report"]["raw_sha256"])
print("REGISTRY", hashlib.sha256((HERE / "REGISTRY.json").read_bytes()).hexdigest())
