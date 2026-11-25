# P3.5 continuous trace continuation — 2026-11-25

## Goal and frozen scope

Continue P3.5, the original full-physical-range `7/32` small-kernel
estimate, from `ef1479c272bdd6b24800fa10409d793f0a2fe95c`. The frozen
2026-11-06 manuscript's `ana:spectral-polynomial` and `ana:returned-polynomial` are
equations (96) and (97), respectively. The existing Lean names `eq24`
and `eq25` use earlier equation numbers.

The user authorizes implementation and GitHub submission, prohibits
duplicating available work, and prohibits formalizing external theorems.
No new axiom, sorry, admit, native_decide, or unsafe proof is permitted.
The pinned Lean, Mathlib, and goldbach dependency versions stay unchanged.

## Existing work reused

- The 80-module baseline and 11-module accepted continuation remain
  unchanged. Their 1,983 declarations are historical acceptance, not a
  certificate that P3.5 is complete.
- `Part3SpectralReturn25` already proves the scalar (96)-to-(97) return,
  including the occupied common-Poisson-block cutoff. Do not repeat it.
- The 2026-11-23 Y04 sources already contain the actual printed continuous
  trace identity, the source-row ABL cost, cumulative energies for both
  rows, and the signed six-spectrum identity. Do not rewrite them.
- `original_two_cumulative_windows` has no located consumer establishing
  the absolute integral of the actual printed pair. This is the selected
  new manuscript-internal Cauchy step.

## Implementation plan

- [ ] Prove the finite-cusp Cauchy inequality for the literal expression
  `sum (star M * S / pi)` and the two literal `sum (norm row ^ 2 / pi)`
  energies. Use Mathlib's existing Cauchy and Holder results.
- [ ] Integrate that inequality on a compact spectral window with an
  actual bounded complex test. Keep all integrability requirements and
  the same conjugated left row. Do not hide a large-sieve conclusion in
  a target-shaped hypothesis.
- [ ] Deduce the explicit cumulative-window bound. A source energy
  charged by `d^2` contributes exactly `d` after Cauchy; a common positive
  large-sieve constant contributes once, not its square.
- [ ] Connect the new theorem to the existing Y04 expressions without
  changing any source-row definition or classical normalization. If the
  historical dependency closure cannot be recovered, label this adapter
  source-only and keep it outside the accepted module inventory.
- [ ] Extend the existing incremental verifier with one dedicated group;
  run strict Lean compilation, bundled kernel replay and the complete
  declaration/transitive-axiom gate on the exact committed sources.
- [ ] Obtain an independent mathematical and implementation review,
  submit the actual changes, and retain the precise validation evidence.

## Validation scope

The first compilation attempt exposed a needlessly broad import path:
the project finite-Cauchy wrapper imports 48 other project modules and
`MathlibNt.SieveTheory.LiLiuPanBoundedAggregate`. The selected proof now
calls the existing `Real.sum_sqrt_mul_sqrt_le` from the pinned Mathlib
directly. This changes no theorem statement and avoids rebuilding that
unrelated project chain just to use its finite Cauchy helper.

The selected private P3 service and the user's backup service both
returned HTTP 429 during environment discovery. No local Lean toolchain
is installed. A dedicated GitHub workflow may verify the new small
module using the existing pinned verifier; other proof areas are not
selected by this workflow.

Fresh compilation proves only the new module's declared statements.
An adapter with unrecovered source dependencies is not compiled merely
because its independent Cauchy supplier is compiled.

## Open full-P3.5 obligations

The full original spectral kernel still requires a compatible, validated
actual trace/Fourier/continuous-spectrum closure, the manuscript's
external ABL/KS/Pascadi/regular-sieve inputs on the actual family, and
uniform payment of all Fourier, level, height, sign and six-scale costs.
The new Cauchy step supplies neither a classical theorem nor those
remaining actual-family inputs. P3.5 stays open until those suppliers
are actually connected and accepted.

## Review focus

The normalizing factor is `1/pi` on each energy and on the paired trace;
the same positive measure is used throughout. Check the conjugated
left coefficient, zero energies, empty spectral windows, the one-power
divisor price after square roots, and uniform quantifier order before
the original data and Fourier frequency. No conclusion may change the
status of an unrelated P3 node.
