# P3 continuation from c509267

## Baseline and scope

The baseline is `c509267dc630d91df33033abde1c484ec86b96ae` on
`codex/p3-formalization-20261123`. The user supplied the successful
80-module, 1,774-declaration strict compilation, kernel replay and axiom
audit result. That receipt is not part of the Git tree; this continuation
keeps the baseline proofs and records its own verification separately.

The frozen manuscript is the 2026-11-06 release at
`chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
The earlier equation (24) is the stable label `ana:spectral-polynomial`,
equation (96) in that release. The prime-product target is
`eq:current-PP`, Proposition D.3.

## Implementation plan

1. Reuse `Part3OffDiagonalModuli` to pay the signed progression kernel
   after the whole modulus sum. Keep the same complex modulus weights,
   complete product, coprimality predicate and totient denominator. Keep
   the actual product-equals-target diagonal separate from the divisor
   bound for nonzero differences.
2. Apply that finite bound to the existing labelled proper-power
   residual. Prove its zero fibre, its total mass from the existing
   proper-prime-power count, and its diagonal multiplicity. Connect the
   result to the existing exact prime/von Mangoldt identity. Derive the
   square-root box budget, then supply its geometric inputs from the
   original integer-shifted dyadic windows and the source's effective
   support, treating empty charts separately.
3. Reuse the existing common-interval Fourier completion and archived
   scalar threshold proofs to extend a full-block exceptional spectral
   estimate to the actual clipped interval and arbitrary positive
   physical weight. Retain each spectral exponent at the threshold,
   and use the exponent cap only on the excess-weight ratio.
4. Strictly compile and kernel-replay the new modules with the original
   pinned toolchain. Audit their complete serialized declaration
   inventories and transitive axioms using the existing audit rules.
   Rebuild only missing dependencies; do not erase or revalidate all
   80 baseline proof objects as part of an incremental run.
5. Review the statements against the manuscript, publish the source and
   incremental receipt, and identify exactly which P3 obligations remain.

## Boundaries

The prime-power payment is a theorem about the actual labelled residual,
not a residual-bound assumption. The original-chart source now derives
the coordinate box support, lower scale and padded volume from an
effective source witness; it does not assume the box volume. The
remaining proper-power obligations are to instantiate `hGeometry` for
the actual integer source on nonzero `W * VM` support, fix constants
uniformly over the finite family, sum the original charts, turn the
physical coordinate cap into a logarithmic growth bound, and pay the
divisor, exact-coprime-mean and modulus masses asymptotically. A
prime-only support bound cannot replace that integer-source geometry.

The spectral extension consumes an explicit full-block classical
estimate and a spectral-parameter bound; it does not assert that these
automorphic inputs have already been formalized. No ordinary
Bombieri--Vinogradov theorem is substituted for the missing spectral
estimate. The frozen manuscript's external Kuznetsov, ABL, Kim--Sarnak
and Pascadi inputs remain visible. `RestrictedMediumObligation`,
`UniformPrimeProductTarget` and the full P3 assembly remain open.

Pascadi's full-block exceptional Theorem J allows the weight threshold
`max(V, Z^2 / V)`. Its common-phase clause and the exact integer interval
endpoints must be preserved. The actual `4*pi` normalization cannot be
dropped when the physical weight is substituted.

## Exact remaining spectral inputs

`ExceptionalWeightGeometry.commonIoc_plateau_tauEnergy_le` still takes
the actual eigenvalue lower bound `hlambda` and `full_uniform`: a uniform
full-block energy estimate for both classical level windows and every
common phase. No instance of either hypothesis on the actual automorphic
spectrum is supplied by this continuation. The separate full-spectrum
`tsum` theorem also requires a bound uniform over every finite spectral
cut. Its summability proof does not supply that analytic bound.

The downstream `Part3SpectralReturn25.eq24_to_eq25_*` theorems compare
two scalar costs. They do not bound the actual separated Kuznetsov sum
by `eq24Cost`. Correspondingly,
`Part3E3FixedDTransport.exists_source_rectangular_rpow` still needs a
uniform bound for the original bare coefficient on every rectangular
prefix. These are genuine missing suppliers, not elaboration errors in
the newly added transport lemmas.

The old source-only candidate
`Part3OriginalExceptionalJInitialAverage.initial_average` at
`228ee511f27ad2d12450b431ba5a1acdc0b5ac9d` only has the initial range
`X <= A * max(1, Q/M)`. It cannot replace full-range J: for `Q` of order
`S^2` and `M` of order `S`, that initial range has size `S`, whereas the
manuscript needs the threshold of size `S^3`. The old native common-phase
completion explicitly leaves the full-interval estimate and Kim--Sarnak
as separate obligations. Old actual Kuznetsov/continuous-removal proof
candidates exist, but their source-selection records do not provide a
complete validated import closure. This does not alter the successful
80-module baseline receipt.

Kim--Sarnak is used twice in the manuscript: the eigenvalue bound giving
`tau <= 7/32`, and the Hecke-coefficient cost with exponent `7/64` in
ABL removal. The conditional `tau` conversion supplies neither actual
classical input. Full-range J, these KS inputs, the compatible ABL/trace
normalizations, and the final actual-source assembly therefore remain
open. No new axiom has been introduced for them.

## Task ledger

| Task | Owner | Status |
| --- | --- | --- |
| `Part3SignedModulusPayment`: whole-modulus signed kernel payment | `p3_modulus_payment` | Strict compile and kernel replay passed on Cloud; full inventory pending |
| `Part3ProperPowerResidualPayment`: actual labelled proper-power residual | `p3_proper_power` | Complete source; development harness passed; actual imports pending |
| `Part3ProperPowerDyadicBudget`: actual box budget to square-root saving | `p3_power_saving` | Complete source; compilation pending |
| `Part3ProperPowerOriginalChart`: original-chart support, volume, empty case and physical cap | root; independent review by `p3_existing_audit` | Complete source at the SHA-256 below; read-only semantic review found no blocking issue; not compiled |
| `Part3ProperPowerLogSaving`: actual distance, mean and complete-diagonal asymptotic payment | `p3_power_saving` | Complete source; not compiled; awaiting the user-selected Workspace Compile connection |
| `Part3ExceptionalWeightExtension`: exceptional weight and common integer interval | `p3_spectral_extension` | Strict compile, kernel replay and full axiom inventory passed at `80d7eeb`; 43 declarations |
| `Part3ExceptionalWeightGeometry`: physical scale and two level windows | `p3_spectral_extension` | Strict compile, kernel replay and full axiom inventory passed at `80d7eeb`; 45 declarations |
| Dependency reuse, verification, review and publication | root | The two-module spectral group passed; proper-power group and original-chart verification remain pending |

## Original-chart source checkpoint

The sixth source module is `Part3ProperPowerOriginalChart.lean`, with
SHA-256
`50a372771ebfa4cee6554402e938e5b7d334bd3cc1c0440a57df39c86fed26ca`.
It has not been compiled. Independent read-only review of this exact
source found no blocking semantic issue; that review is not a
compilation, kernel-replay or axiom-audit receipt.

The module reuses `originalDyadicChartWeight chi L j` with the original
integer shift `L`. Its fixed coordinate endpoint is
`U_i = Nat.ceil (2 * 2^(L+j_i))`; no nonnegative-exponent assumption is
introduced. A nonzero window at an integer `n_i` gives `n_i <= U_i`
and `U_i+1 <= 5*n_i`.

An effective witness is a tuple where
`(W * originalDyadicChartWeight) * labelledVonMangoldtWeight` is nonzero.
It retains the same original weight and implies nonzero `W * VM`.
The source's geometric support at that witness supplies the coordinate
lower bounds and complete-product bound `product <= C*x`, from which
the module derives padded-box volume at most `5^k*C*x`. Every coordinate
is a positive integer, so each divides and is at most the complete
product; hence `max_i U_i <= Nat.ceil (5*C*x)`.

If there is no effective witness, the actual labelled proper-power
residual is identically zero, even when the formal box is large. The
empty-rank case is retained. The resulting bound preserves the same
modulus weights, exact coprime mean and separate complete-product
diagonal. For `a > 0`, the factor `x^(1-a/2)` gives the intended power
reserve, subject to the remaining uniform asymptotic assembly above.

## Original-chart logarithmic saving candidate

`Part3ProperPowerLogSaving.lean` reuses the existing divisor subpower,
weighted divisor means, constant absorption and arbitrary-log accuracy
lemmas. It retains the actual residual and finite signed error. Its
source is not yet compiler-verified. Independent semantic review found
no blocking issue. The sole unused-parameter lint risk was resolved by
renaming `hK` to `_hK`, preserving the statement. Current source SHA-256:
`289913d4c27daee7b556f7d4a1bd5d68c38b44f375cde28baa16905665c672fc`.

For fixed rank, divisor order, polylogarithmic amplitude degree and
geometric constants, its final threshold precedes every varying source
cap, physical product subcarrier, modulus set, same complex rho, weight,
cutoff and original chart. It assumes the actual positive-modulus range
`q <= K*N^theta` with `0 <= theta < 1`, a fixed divisor-order rho bound,
and geometric support of `W*VM`. It does not assume the desired residual
bound or a uniform distance-divisor estimate.

The distance budget is computed on the actual `B.erase N`, with
`B` contained in `[1, ceil(C*N)]`. This physical-carrier restriction
prevents unrelated huge zero-coefficient indices from inflating the
supremum. The exact-product diagonal retains `tau(N)^k`; the primitive
mean is bounded by logarithms separately from the total modulus mass.
The resulting candidate gives any real logarithmic exponent, uniformly
across the individual original charts. Actual policy-specific rho
instances and full chart-bank linear reassembly are still separate.

## Requested compilation environment

The user selected **Workspace Compile 27f68009** for subsequent
compilation. Its private plugin was found, separate from the old
Cloud Compile connection. The current conversation has not exposed its
command tools, so no task has been submitted to that environment yet.
The earlier successful spectral receipt remains valid for its recorded
source hashes. The pre-existing proper-power GitHub build is retained;
new checkpoint publication does not start another CI build while waiting
for the requested environment.

## Compilation continuity

Cloud Compile reached its 128-retained-job limit during this continuation.
Its exposed tools have no archive operation. No other task was cancelled,
and the limit was not modified. The single-module strict/kernel receipt is
preserved in `continuation-20261124/cloud-modulus-receipt.json`.

The new GitHub workflow runs the original pinned Lean and dependencies.
It verifies two disjoint groups, `spectral` and `proper-power`, so a missing
heavy arithmetic dependency does not delay diagnostics for the light
spectral modules. Both groups use the original complete inventory rules.
Only a successful receipt for the exact source hashes is a proof-validation
result; static review, source-only checks and the development harness are
not substitutes for that result. The spectral group passed all gates at `80d7eeb`, covering 88 complete
serialized declarations. Its original artifact, report and complete types
are retained in `continuation-20261124/spectral-80d7eeb/`. The proper-power
group is still awaiting its acceptance result; `Part3ProperPowerOriginalChart`
has no compilation result yet.

The proper-power box budget now supplies an explicit `x^(1-a/2)` factor
from a coordinate lower bound `c*x^a` and complete box volume `C*x`.
The original-chart source derives those box inputs, with the padded
factor `5^k`, from the actual source's effective geometric support and
handles empty charts by zero residual. Its physical cap is bounded by
`Nat.ceil (5*C*x)`; the logarithmic-growth and uniform source-family
instances remain to be supplied.
The spectral adapters now include arbitrary common integer intervals,
both classical level windows, the positive-integer endpoint `m=1`, and
a proof of summability before passing from finite spectral sums to `tsum`.
The actual automorphic input instances and the final uniform P3 assembly
are still separate obligations.

This file is a work ledger, not a completion certificate.
