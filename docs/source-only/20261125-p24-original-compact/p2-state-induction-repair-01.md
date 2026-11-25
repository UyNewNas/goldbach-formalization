# P2 strict run: historical Q80 state-induction expression repairs

Status: source-only candidate pending actual retry.

## Actual failure binding

- P2 job: `8fcc0987e7cc4f6f8d7613ee772f3609`.
- Input commit: `fb61b4cd912765dc7975051055b0d2c3ed3d3714`.
- Owned source: `ImbalancedChen/P2HistoricSieveStateInduction.lean`.
- Read-only failure source: `/workspace/scratch/daaa8ebc2a3f/p24-p2-live/current.log`.
  The observed live-log snapshot had SHA-256
  `084f7dd8555164ea2269220acfa3bd25f863378857cd59adc259e10d9177af74`;
  the job was still running, so this is a snapshot binding, not a final-run hash.

## Frozen manuscript and source boundary

Consulted the frozen publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/numerical-appendix.tex`, directed rounding
  (94–102) and delayed numerator recurrence, initial branches, mesh/knot
  conventions, and interpolation/curvature bounds (122–164). SHA-256:
  `bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
- `verification/data/certify_extended_prefix.py`, the literal Q80 table
  update, integer ceilings, divmod interpolation, and point rule (51–113).
  SHA-256:
  `1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.

The original Q80 recurrence and its two nested division layers are retained.
The manuscript's separate weighted-numerator-chord implementation is not used
to identify or replace this table. The maximum-eight carrier, existing cell
increment lemmas, and existing interpolation allowance remain unchanged.
No finite-recursion argument is promoted to an infinite-limit assertion.

## Seven reported locations, six minimal edits

| Actual location | Repair | Classification |
| --- | --- | --- |
| 79, 124 | Replace broad `simp [cellLeft, cellRight]` with `simp only [cellLeft, cellRight, Nat.cast_add, Nat.cast_one]`. | Restricted equation normalization resolves the reported recursion-depth failure without raising limits. |
| 109, 118 | Explicitly `change` the existing `htrap` equality to use the local `j := i - 16385` before rewriting the goal. | Definitionally equal index expressions now match the endpoint branch hypotheses. |
| 274, 284 | Add `Nat.cast_ofNat` to the existing restricted simp lists. | Normalize the query index/residual's cast natural literal `16384` to the existing integer literal. |
| 333 (reported enclosing proof) | After aligning `hwForm`, derive `(b : ℝ) ≠ 0` from the existing `hb`, then rewrite with `Int.cast_sub`, `sub_div`, and `div_self`. | Explicit elementary cancellation: `(b-r)/b = 1-r/b`. |

The first six reported locations are expression/API issues. The final one
makes a small algebraic inference explicit from an already available positive
denominator; it adds no premise or analytic estimate. These errors identify
no substantive manuscript gap. Unreported proof sites were left unchanged.

## Static verification and review

- All **16 theorem headers**, **6 complete definition/structure blocks**, and
  imports are byte-identical to the input commit.
- `git diff --check` passed; no prohibited proof construct, linter setting,
  extra hypothesis, or computational definition was introduced.
- Independent read-only review by `p24_stage_closure` confirmed the local-index
  alignment, cast equations, and the direction and nonzero premise of the final
  coefficient cancellation; no required further change was found.
- Before source SHA-256:
  `53a452e5f70773d26e79bba7d007dedae4ee0284d85fb71dedc8c939bcde5894`.
- Candidate source SHA-256:
  `46a4c46db1ebea7064b041cae0e2c37ffd859ac972de9e709c5229f1ddca5b88`.

Only the owned Lean file and this note were edited. No CI/archive re-audit,
Lean/Lake invocation, remote job, staging, index update, or commit was performed.
Compile and kernel credit for this candidate remain false pending actual retry.
