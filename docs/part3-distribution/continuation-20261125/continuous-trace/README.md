# P3.5 continuous trace: accepted core and source-only actual-row adapter

## Acceptance

**Four public Cauchy theorems are accepted. The actual-row adapter is
source-only. The original full-range P3.5 `7/32` estimate is still open.**

| Item | Exact evidence |
| --- | --- |
| Mathematical commit | `de24ecddb6f5bdb0c8173c788ace734207c457a0` |
| Module | `ImbalancedChen.Part3ContinuousTraceCauchy` |
| Core SHA-256 | `4c6a664915885c31f2d0f8960b2650daa5b7ae44bc31f697a08bbf9a52974c3c` |
| Successful run | [45571177099](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45571177099) |
| Successful job | [139058079508](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45571177099/job/139058079508) |
| Artifact | `15002790963`, 26,887 bytes |
| Original artifact SHA-256 | `196bbf683b6fa2986939a920b95f4ef49f97a161c922544b28e8b99efab53f4e` |
| Complete owned inventory | 5 declarations: 4 public theorems and 1 compiler-generated simplification theorem |
| Allowed and observed transitive axioms | `propext`, `Classical.choice`, `Quot.sound` |
| Acceptance finished | 2026-11-25 15:55:39 Asia/Shanghai / 07:55:39 UTC |

The exact committed source passed ordinary Lake build, a fresh strict
compile with `warningAsError=true`, the pinned installation's bundled
`leanchecker` replay, and the existing full declaration/type/transitive-axiom
audit. All 39 source/configuration hashes in the report match the submitted
files. The original ZIP digest, all stage-log digests, and the complete
declaration inventory were checked after download and independently reviewed.

This receipt follow-up changes documentation and evidence only. Its parent
contains the accepted mathematical bytes. It does not repeat acceptance for
the old P3 modules or relabel the actual-row adapter as compiled.

## Mathematical increment

For a finite cusp index type, continuous rows `M_i(t)` and `S_i(t)`, and
`W = [-T,T]`, the new module proves Cauchy for the literal printed pair

`P(t) = sum_i (star (M_i(t)) * S_i(t) / pi)`.

Both energies retain exactly the same normalization:

`L_W = integral_W sum_i (norm (M_i(t))^2 / pi)`,
`R_W = integral_W sum_i (norm (S_i(t))^2 / pi)`.

The four public declarations are:

1. `printed_trace_norm_le`: pointwise finite-cusp Cauchy.
2. `integral_printed_trace_norm_le`: integrated absolute Cauchy on the
   common compact height window.
3. `norm_integral_test_mul_printed_trace_le`: a continuous complex test
   bounded by `B` on that window gives `norm (integral_W test * P) <=
   B * sqrt(L_W) * sqrt(R_W)`.
4. `norm_integral_test_mul_printed_trace_le_of_energy_bounds`: from the
   separate inequalities `L_W <= C * Eleft` and
   `R_W <= d^2 * (C * Eright)`, with `B,C,d >= 0`, obtain
   `norm (integral_W test * P) <= B * d * C * sqrt(Eleft) * sqrt(Eright)`.

The conjugate remains on the original left row. The source divisor price
`d^2` contributes exactly one `d` after square roots, and the shared sieve
constant contributes one `C`. No paired-trace estimate is assumed. Empty
finite families, zero energies and reversed empty windows are covered.

This is the Cauchy derivation in Appendix A.5 of the frozen 2026-11-06
manuscript, with the continuous measure in Appendix B, equation (104).
The spectral estimate and its return have frozen labels
`ana:spectral-polynomial` (96) and `ana:returned-polynomial` (97).
The older Lean names `eq24`/`eq25` are not the frozen manuscript's equation
numbers. The existing scalar return in `Part3SpectralReturn25` was reused,
not re-proved.

## Actual-row adapter and remaining boundary

The [source-only adapter](../../../source-only/20261125-p35-continuous-trace/Part3OriginalGeometricWindowEnergy.lean)
preserves the historical Y04 `Part3OriginalGeometricWindowEnergy` source
apart from the new core import and `original_tested_continuous_window`.
It reuses `original_two_cumulative_windows` and the private
`printedR_cont`, so no gamma-normalization continuity proof is repeated.
The same `C(e)` is selected before the original data, levels, signs,
Fourier frequency, height and test. The actual divisor-cardinality price
and both original row energies are retained.

The [reuse manifest](../../../source-only/20261125-p35-continuous-trace/REUSE.json)
binds donor commit `fa22a56829ee880404516a36d498ce27dcb32f92`, the exact
source blob and candidate SHA-256, and the historical missing/ambiguous
dependency inventory. Six sources have known registered hashes but their
matching bytes could not be recovered from the checked trees, objects and
archives. They were previously registered; this is not a claim that they
were never implemented. The [recovery note](SOURCE_RECOVERY.md) states the
checked scope without making a universal absence claim.

The source-only adapter has no strict-compile, kernel-replay or axiom
acceptance. Restoring those six files would still not by itself establish
all of P3.5. The complete original trace/Fourier/continuous-spectrum
connection, the manuscript's external ABL/KS/Pascadi/regular-sieve inputs
on the actual family, and the uniform level, height, Fourier and six-scale
costs must all be connected and validated. No new external theorem or
substantive manuscript gap is asserted here. No parent board node is
promoted to completed status by this receipt.

## Retained evidence

- [RECEIPT.json](RECEIPT.json): compact acceptance and scope binding.
- [report.json](report.json): unmodified verifier report with source,
  compiler, dependency, object and stage-log hashes.
- [declarations.json](declarations.json) and [theorem-types.txt](theorem-types.txt):
  complete audited declaration names, full types and transitive axioms.
- [Strict compile log](Part3ContinuousTraceCauchy-strict.log),
  [kernel replay log](Part3ContinuousTraceCauchy-replay.log), and
  [axiom audit log](axioms.log).
- [Generated audit source](Part3ContinuationAudit.lean).
- [Independent review](INDEPENDENT_REVIEW.md), including the exact-source
  acceptance addendum.
- [Original GitHub artifact ZIP](p35-continuous-l2-de24ecdd-45571177099.zip):
  all 39 original artifact members, including dependency and environment
  logs not duplicated as separate files here.

The first broad-import run `45569351145` was cancelled after the proof
was narrowed to Mathlib's existing finite Cauchy supplier. It supplies no
acceptance. The successful run above is the sole fresh acceptance claimed
for this increment.
