"""Source/byte metadata only. Does not import/execute a proof producer.

The table comparison below compares literal coefficient STRINGS. It never
evaluates an affine form, a rational, a point, a guard, or an integral.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
P = "docs/source-only/"
S = P + "20261102-resume-30s/s11_saving16_complete/"

SOURCES = [
    (S + "P2OriginalSaving16Full87SourceBinding.lean", "new"),
    (S + "P2OriginalSaving16WholeIntegralPresieve.lean", "new"),
    (P + "20261102-resume-30j/saving16_geometry/P2OriginalSaving16FourteenPhysicalAtlas.lean", "direct import: actual fourteen-cell atlas"),
    (P + "20261102-resume-30r/full87_source_history/P4AOriginalFull87PrefixBinding.lean", "direct import: original87 own-prefix dictionary"),
    (P + "20261102-resume-30r/all22_actual_sources/P4AOriginalArchiveFourteenPositivePresieve.lean", "direct import: actual original-bank policy and positive-w source"),
    (P + "20261102-resume-30r/full87_source_history/P4AOriginalFull87SourceDictionary.lean", "actual original87 source constructors"),
    (P + "20261102-resume-30r/full87_source_history/P4AOriginalRemainingEighthSources.lean", "exact original affine source semantics"),
    (P + "20261102-resume-30r/full87_source_history/P4AOriginalAscendingFourteenAffineSource.lean", "all fourteen ordered 96-row source arrays"),
    (P + "20261102-resume-30r/full87_source_history/P4AOriginalSeed7Unequal15Literal.lean", "actual affine evaluator"),
    (P + "20261102-resume-30o/all22_common_history/P4AOriginalCommonArchiveSchedule.lean", "whole actual source-integral/common-history supplier"),
    (P + "20261102-resume-30o/adopted87_policy/P5OriginalFourthFifthSourceInputs.lean", "actual fourth bytes/admission and original fifth bank"),
    (P + "20261102-resume-30o/saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean", "whole ordinary family including harmful complement"),
    (P + "20261102-resume-30q/saving16_scope/P2OriginalFourteenCommonScheduleEndpoint.lean", "reused original Q96 endpoint on same schedule"),
    (P + "20261102-resume-30o/saving16_pulling_ownership/P2OriginalSaving16OwnedIntegral.lean", "original39741 legal owned simplex endpoint"),
    (P + "20261102-resume-30k/saving16_trim/P2OriginalFourteenWeightedTrim.lean", "actual weighted trim supplier"),
    (P + "20261102-resume-30j/saving16_compiler/P2OriginalSaving16TrimmedHistory.lean", "actual source trim"),
    (P + "20261102-resume-30k/saving16_glue/P2OriginalSaving16CommonOldPolicy.lean", "local actual parent/history supplier"),
    (P + "20261102-resume-30j/saving16_compiler/P2OriginalFourteenSignedParentLedger.lean", "literal signed charge/current-minus-new identity"),
    (P + "20261102-resume-30i/common4_source/P5OriginalCommonFourthSourceNavigation.lean", "original4 declaration"),
    (P + "20261102-resume-30o/all22_common_history/P4AOriginalCausalHistory.lean", "original5 declaration and archive causal schedule"),
    (P + "20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedConstructor.lean", "actual old3/policy6/lambda6 definitions"),
    (P + "20261028-resume-30e/coefficient_physical/P5OriginalCommonRefinedSource.lean", "actual signed stage sources"),
    (P + "20261028-resume-30/coefficient_rosser/P1Pair12RetainedSignedSource.lean", "arbitrary full-q attached signedTest"),
    (P + "20261102-resume-30h/coefficient_physical/P5OriginalCommonPositivePresieve.lean", "same normalizer/raw/physical definitions"),
    ("ImbalancedChen/ActualFirstExitDensityProjection.lean", "one-whole-tree actual beta-error supplier"),
    ("ImbalancedChen/P2OriginalAscendingEighthCapDictionary.lean", "mask129/coefficient4/original M,R,kernel"),
    (P + "20261028-resume-30d/upper_chronology/P4AOriginalAscendingCell1Affine.lean", "atlas original cell1 exact patch"),
    (P + "20261028-resume-30e/upper_chronology/P4AOriginalAscendingCell2Affine.lean", "atlas original cell2 exact patch"),
    (P + "20261028-resume-30f/upper_chronology/P4AOriginalRemainingAscendingAtlas.lean", "atlas eleven exact row patches"),
    (".lake/proof-continuation/source-reviews/drafts/20261028-Upper-Sol6-PhaseB-Chronology/P4AOriginalAscendingCell0Literal96.lean", "hidden exact original cell0 table reused"),
    (P + "20261102-resume-30p/saving16_pulling_ownership/P2Winner9ActualEightSimplexMoment.lean", "required same-module forward integral_const_mul minimal replacement"),
    (P + "20261102-resume-30r/all22_actual_sources/REPORT.md", "R06 final scope read"),
    (P + "20261102-resume-30r/all22_actual_sources/REGISTRY.json", "R06 source pins read"),
    (P + "20261102-resume-30r/reviews/r26_review_reserves_density.md", "independent R06 review read"),
    (P + "20261102-resume-30q/saving16_scope/REPORT.md", "Q08 original necessary-scope audit read"),
    (P + "20261102-resume-30r/full87_source_history/REPORT.md", "R03 source-dictionary boundary read"),
    ("../chen-imbalanced-semiprimes/paper/source/manuscript-body.tex", "original fixed manuscript"),
    ("../chen-imbalanced-semiprimes/proof-library/source/eighth-prefix-family-20261009.tex", "original source-family geometry/current-parent paragraph"),
    ("../goldbach-research/eighth-prefix-family-20261009-exact.py", "original program read as source text only"),
    (S + "REPORT.md", "delivery scope and exact remaining obligations"),
    (S + "collect_metadata.py", "source/byte metadata generator only"),
]

def record(relative, purpose):
    path = (ROOT / relative).resolve()
    raw = path.read_bytes()
    txt = raw.decode("utf-8-sig") if path.suffix in (".lean", ".md", ".json", ".py") else ""
    ns = re.search(r"^namespace\s+(\S+)", txt, re.M)
    declarations = []
    if path.suffix == ".lean":
        for n, line in enumerate(txt.splitlines(), 1):
            m = re.match(r"(?:private\s+)?(?:protected\s+)?(?:noncomputable\s+)?(def|abbrev|theorem|lemma|structure|inductive)\s+(\w+)", line)
            if m:
                declarations.append({"name": (ns.group(1) + "." if ns else "") + m.group(2), "kind": m.group(1), "line": n})
    return {"path": relative, "absolute_path": path.as_posix(), "purpose": purpose,
        "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw),
        "line_count": len(txt.splitlines()), "module": "ImbalancedChen." + path.stem if path.suffix == ".lean" else None,
        "imports": re.findall(r"^import\s+(\S+)", txt, re.M), "declarations": declarations}

def tokens(s):
    return [re.sub(r"\s+", "", x) for x in s.split(",")]

def source_string_comparison():
    base_path = ROOT / SOURCES[29][0]
    text = base_path.read_text(encoding="utf-8-sig")
    base = [tokens(v) for v in re.findall(r'\("[^"]*",\s*!\[([^\]]*)\]\)', text)]
    assert len(base) == 96, len(base)
    cell1 = ROOT / (P + "20261028-resume-30d/upper_chronology/P4AOriginalAscendingCell1Affine.lean")
    cell2 = ROOT / (P + "20261028-resume-30e/upper_chronology/P4AOriginalAscendingCell2Affine.lean")
    patch1 = tokens(re.search(r'\("old subset 58[^\"]*",\s*!\[([^\]]*)\]\)', cell1.read_text(encoding="utf-8-sig")).group(1))
    patch2 = tokens(re.search(r'\("old subset 60[^\"]*",\s*!\[([^\]]*)\]\)', cell2.read_text(encoding="utf-8-sig")).group(1))
    atlas = [list(base) for _ in range(14)]
    atlas[1][90] = patch1
    atlas[2][90] = patch1
    atlas[2][92] = patch2
    rest_path = ROOT / (P + "20261028-resume-30f/upper_chronology/P4AOriginalRemainingAscendingAtlas.lean")
    rest = rest_path.read_text(encoding="utf-8-sig")
    changes = re.search(r"def changedRows.*?:=\s*!\[(.*?)\]\s*\n\s*def rightPatch", rest, re.S).group(1)
    change_lists = [[int(k.strip()) for k in x.split(",")] for x in re.findall(r"\{([^}]+)\}", changes)]
    patches = {int(k): tokens(v) for k, v in re.findall(r'\|\s*(\d+)\s*=>\s*\("[^"]*",\s*!\[([^\]]*)\]\)', rest)}
    for i, changes in enumerate(change_lists, 3):
        for k in changes:
            atlas[i][k] = patches[k]
    rtext = (ROOT / (P + "20261102-resume-30r/full87_source_history/P4AOriginalAscendingFourteenAffineSource.lean")).read_text(encoding="utf-8-sig")
    pool_text, indices_text = rtext.split("def literalPool", 1)[1].split("def literalIndex", 1)
    pool = [tokens(v) for v in re.findall(r"!\[([^\[\]]*)\]", pool_text)]
    indices = [[int(x.strip()) for x in v.split(",")] for v in re.findall(r"!\[([^\[\]]*)\]", indices_text)]
    assert (len(pool), len(indices)) == (104, 14)
    assert all(len(v) == 96 for v in indices)
    mismatches = [(i, k) for i in range(14) for k in range(96) if atlas[i][k] != pool[indices[i][k]]]
    assert not mismatches, mismatches[:20]
    return {"kind": "literal coefficient-string identity only", "cells": 14, "ordered_rows": 1344,
        "coordinates_per_row": 9, "string_mismatches": [], "evaluated_affine_forms_or_proofs": False}

records = [record(path, purpose) for path, purpose in SOURCES]
registry = {
    "schema_version": 1, "batch": "20261102-resume-30s", "task": "s11_saving16_complete",
    "owner": "/root/s11_saving16_complete", "write_scope": S.rstrip("/"),
    "status": "SOURCE_ONLY_ACTUAL_SOURCE_MEMBERSHIP_AND_WHOLE_INTEGRAL_PRESIEVE",
    "whole_assigned_yellow_source_complete": False,
    "compiled": False, "kernel_verified": False, "formal_credit": 0,
    "finite_bodies": "UNEVALUATED", "original_terminal": "P2.5 saving16：十四组ascending第八前缀cell",
    "original_yellow_leaves": ["完整第四原始实例、positive-w与87实际族成员绑定", "共同旧策略实现全部历史门限", "连接signed compiler并证明整体积分包络"],
    "new_sources": [r for r in records if r["purpose"] == "new"],
    "reused_sources": [r for r in records if r["purpose"] != "new"],
    "source_string_identity": source_string_comparison(),
    "new_axioms": [], "target_equivalent_hypotheses": [], "endpoint_assumptions": [],
    "removed_premises": [
        "Atlas-to-full87 source membership is derived using every original row, not a label-only bijection or caller Source hypothesis.",
        "Whole actual fourteen integral appears in positive-w upper envelope without a caller integral or numeric endpoint premise.",
        "Original fourth rows/admission and geometry are instantiated; original fifth archive and arbitrary full-q signed gains are supplied on the same q."],
    "remaining_mathematical_premises_or_constructions": [
        "S09 complete actual original-sixth source and its current-parent bounds on retained fourteen histories.",
        "S10 actual full87 chronology: literal fourteen splice's signed source on the same final policy, preserving earlier decisions and allowances.",
        "S14 same-policy whole signed compiler coverage/error envelope and actual budget payment.",
        "The concrete fourth geometry admission filter is not a proof that every archived row supplies all original analytic licences or its saved whole gain."],
    "quantifier_order": "nu,eta,betaMax -> beta,n,e0 -> e,omega -> q,N0 -> N,cap,w,z,L,G",
    "constants": {"mask": 129, "coefficient": 4, "cutoff": "53/13824", "presieve_cutoff_exponent": "19/96", "new_cap_buffer": "1/1000000", "Q96_endpoint": "1222997719565324892497827/2^96"},
    "budget": "Whole ordinary comparison eta/2 and the one-whole-new-tree beta projection eta/2 are combined once; this is an alternative strengthening of R06's local envelope, not an additional saving or reserve debit.",
    "remote_target": ["ImbalancedChen.P2OriginalSaving16Full87SourceBinding", "ImbalancedChen.P2OriginalSaving16WholeIntegralPresieve"],
    "remote_check_plan": "Root materializes exact direct/transitive source closure, applies the registered P moment replacement, verifies with pinned Lean/mathlib, and prints axioms for both new terminals and original_rows_exact. No local build has occurred.",
    "prohibited_operations_performed": [], "transitive_import_closure_verified": False,
}
(HERE / "REGISTRY.json").write_text(json.dumps(registry, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"files": len(records), "new_lean": 2, "rows_textually_matched": 1344, "proofs_evaluated": False}))
