# Common refined policy preservation: diagnostic-bound proof repair

Status: **source candidate; normal/kernel/full-owned acceptance pending**.

Only `ImbalancedChen/P5OriginalCommonRefinedPreservation.lean` was changed.
The preimage at commit `01b0646416ea0b1c612f29ad301052d52e0bf78e` is the
previous Batch10 repair. Its fresh normal run failed with nine target errors;
no successful build or acceptance is inferred from this source edit.

## Source and failed-run bindings

| Item | SHA-256 |
|---|---|
| Failed source preimage | `2692c94da8ad4b2c0bc53b74d3212d07ac161828147254dc67fdfcca0d95e121` |
| Candidate source | `ddca6c374ca3e3722d4498f17a2543b610fa8c2e241b13e79903a4829a803aaf` |
| Complete failed normal log | `ce479bf3ca676f11b13aa1da3757bdf11dbfa09692e69aeda15be5219abf644c` |
| Captured target diagnostic JSON | `34647ebe866e5b7375c4f6be28e022fd542ce1ab7ab2fff7874635105ca08eaf` |

The candidate Git blob is `0e4a39beb69a8b720e50109cc9534ff61ed515fe`.
The failed log has 196,186 bytes and is stored at
`/workspace/p1-complete-proof/20261125-batch10-resume/normal/ImbalancedChen.P5OriginalCommonRefinedPreservation/attempt-00000/normal.log`.
The original guarded command was
`python3 /workspace/blue-build-tools/run_guarded.py --state /workspace/blue-build-tools/member-runtime-evidence/state.json lake build +ImbalancedChen.P5OriginalCommonRefinedPreservation:olean`,
with working directory `/workspace/blue-member-build`; it exited 1 at
`2026-11-25T01:39:43.239577+00:00` and built no target module.

## Diagnosis and changes

The three errors at old line 95 left the right-hand conditional unreduced
after splitting the left-hand branch. `lambda3_ancestor` now applies
`congrArg₂` directly to the literal cap function and the existing rank-three
and rank-two ancestor equalities. Its branches, exponents, guards and the
order of those guards are the constructor's existing formulas.

The six errors at old lines 176, 181, 203, 218, 224 and 240 were exact
`decide P = true` versus `P` mismatches. Merely adding `decide_eq_true_eq` to
the previous broad simplifications had left those mismatches. The candidate
first unfolds only the existing policy wrappers and then explicitly applies
`of_decide_eq_true` or `decide_eq_true`. Existing local reuse includes the
policy-wrapper reduction in `P5OriginalCommonFourthActualAdmission` lines
43–46 and its explicit `of_decide_eq_true` application at line 118.

## Contract and manuscript boundary

Fresh static verification reused the declaration inspection functions from
the earlier Batch10 `verify_static.py`, without running that script's
historical mutation/output logic. All 22 theorem headers, declaration order,
imports, namespace commands and bytes outside theorem proof bodies match
the preimage. There are no definition changes. The edits lie in five
existing proof bodies, preserve CRLF, and introduce no `sorry`, `admit`,
axiom, `native_decide`, option or new assumption.

The manuscript is the pinned 20261106 English release at
`a988cba584d803ae2856a0de50efb582f4f3dd6a`. The relevant arguments are
`sieve-appendix.tex` lines 45–53, 111–155 and 273–302, and
`coefficient-appendix.tex` lines 20–22 and 103–116: earlier admission tests
and ancestor decisions remain fixed, with refinement in increasing prefix
order and one common finite policy for count and density. The source
continues to prove actual approval and retained-modulus containment. It
does not assert signed coefficient monotonicity or numerical gain
preservation.

No Lean, Lake or compiler service was called by this repair task. The
root-controlled guarded normal retry and subsequent acceptance gates remain
the required validation.
