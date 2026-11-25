# Compact04: literal tent selector and positive-log integer guards

Date: 2026-11-25. Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

## Actual diagnostic input

The failures were read from P1 job `job_4c8505b542074aefb7fd6d98b9dd55ad`,
source commit `086696e51088eb93942abf2fcc1ce48e148ad842`. The local log is
`p1-compact-04.log`, 26,159 bytes, SHA-256
`f015edcbd99538444447dea15cf96860121c0972e4724f30211f0d91ffee86dc`.

The selector file has seven failing order-API applications, at original
lines 78, 89, 106, 121, 123, 135 and 153, plus a redundant `ring` at line 101.
The strict applications at 106, 121 and 153 report `MulRightStrictMono Real`;
the four weak applications resolve to a different theorem and fail at `.mp`.
The positive-log file has the reported cast mismatch at line 127.

Only the two assigned production files were edited. This repair did not run
Lean, Lake, a generator, a cloud job, or a new CI/archive audit.

## Frozen manuscript and formula correspondence

The frozen 1106 sources come from publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/numerical-appendix.tex`, SHA-256
  `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
  Its directed arithmetic section requires lower floors, upper ceilings,
  four endpoint products for multiplication, and positive divisor intervals.
- `verification/data/certify_extended_prefix.py`, SHA-256
  `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.
  The read sections were `v_planes`, `active_min_plane`, `affine_cap_lower`
  and the residual/divisor formulas in `jensen_difference_upper`.

For a selected sum S, the two planes remain `(1+S)/2` and
`(57-96*S)/64`. With D = 48000*2^24 and the integer sum S_I, their difference
times 128*D is `-50*D+256*S_I`. The first matching plane is still the rising
plane when the upper delta is nonpositive. The falling plane still requires
failure of that first test and a nonnegative lower delta. The root filter
retains `<=`, while the residual numerator retains strict positivity.
All multiplier positivity premises come from the existing D > 0 proof.

The appendix also describes an odd-power logarithm enclosure used by its
paired-cell calculation. The existing original-positive implementation is
kept exactly as represented in `ActualThirdOriginalPositive256Log.lean`:
z = 1-1/x, 256 positive-series updates at P160 = 2^160, the existing tail,
and the final rounded log(2) multiple. The range-32 implementation still
uses at most four exact divisions by two and exits on `<= 2`, including its
existing equality cases at 2, 4, 8, 16 and 32. Neither implementation file
was changed. No odd-power formula or other precision was substituted.

The integer-guard proof already derives the needed first-term threshold.
Writing K = 2^80, the positive integer width gives x1-x0 >= 1; the original
rho bound gives x1 <= K; hence K*x1 <= P160 <= (x1-x0)*P160. Division by
positive x1 gives K <= z*P160. Taking the floor, then using the existing
lower-sum monotonicity proof, gives raw log.lo >= K. Every original endpoint
product of the valid interval with itself is at least K^2 = P160, so its
rounded square lower endpoint is at least one. This derivation and every
hypothesis remain unchanged.

The separately named historical
`numerical-w2-affine-series-independent-20261010.py` was not available in
the already bounded local source lookup. No wider retrieval was attempted;
this note does not claim a new full source-equivalence audit for that script.

## Minimal repairs and classification

| Original location | Repair | Classification |
|---|---|---|
| Selector 78, 89, 123, 135 | Use `mul_le_mul_iff_right₀` with the same existing positive common left factor. | Current order API; exact weak inequality preserved. |
| Selector 106, 121, 153 | Use `mul_lt_mul_iff_right₀` with the same existing positive common left factor. | Current order API; exact strict inequality preserved. |
| Selector 101 | Delete `ring` after `field_simp` already closed the identity. | Redundant tactic reported as “No goals to be solved”. |
| Positive guards 127 | Supply `Int.le_floor.mpr (by simpa only [Int.cast_pow] using hfirst)`. | Explicit cast normalization omitted at the floor boundary. |

The `_iff_right₀` orientation cancels a common positive left factor;
existing repository applications, including
`Part5SavedParent394700Buchstab.lean`, use this orientation. The replacement
does not assert global multiplication monotonicity over all real factors.

No new mathematical lemma or estimate is required by these reported
failures, and no mathematical gap was identified in them. The only omitted
step was explicit expression normalization. This classification is limited
to these local errors and gives no credit to other proof or finite-check
obligations.

## Source bindings and static checks

| File | Before SHA-256 | After SHA-256 |
|---|---|---|
| `ImbalancedChen/ActualThirdOriginalLiteralTentSelectorGuardBridge.lean` | `a1875ffca5ea17f162239775e2e5729f92788cf279c561d7de7a768a0913d130` | `b9282ed1191c5f64a09569b94081952f16f75e7ae29e096602ff3c2e0c2e534a` |
| `ImbalancedChen/ActualThirdOriginalPositive256LogIntegerGuards.lean` | `d0bc52e621d93fdf8adf8e4262eac0dccd39813fb6c3430a579c1b5dd108c933` | `2e2b7614686c58fabd57ac9a8842b60d306f04cd334c966995f7956d35f9b80d` |

All 12 theorem headers, including four private helpers, and all three
computational declarations are byte-identical to the captured pre-edit
files. Imports, constants, assumptions, conclusions, and computational
branch order are unchanged. `git diff --check` passes. No `sorry`, `admit`,
axiom, `native_decide`, `unsafe`, or linter-disabling option was added.

## Read-only cross-review of the root agent's five small fixes

The five diffs were compared with the same diagnostic log and their SHA-256
values in `compact-04-root-linter-repairs.json`. All recorded hashes match.
No Critical or Important issue was found in this bounded source review:

- `P2HistoricLogPointInterpreter`: removes only the reported ineffective
  `ring`; the historical sharp odd-log remainder and its factors are intact.
- `ActualThirdOriginalBelowMuBMassCeil` and `P4AActualSquaredGapDecay`:
  sequence the same `field_simp` and `ring` on the single remaining goal.
- `P4AClosedCutTreePositionalChargeBinding`: sequences the same `simp_wf`
  and `omega` inside the left recursive termination proof. The recursor,
  left-before-right concatenation, and actual charge list are unchanged.
- `P2OriginalEfficientPriorityHeap`: retains `split <;>` across both merge
  branches, then sequences the existing `simp` and `Multiset.cons_swap`
  within each branch. Heap operations and multiplicities are unchanged.

All 63 actual theorem headers in those five files, including eight private
helpers, are byte-identical to commit 086696e5. Root record separately
used an earlier regex count that included a header comment. The later
token-aware comparison covers all 63 actual headers, including eight private
helpers. This cross-review did not
edit those files and is not a compiler result.

Root owns the next Lean run. The repaired sources have not been freshly
compiled by this task; compilation, kernel, numerical evaluation, and P2.4
completion credit remain zero here.
