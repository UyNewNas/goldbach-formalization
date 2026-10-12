# Part 4 round 2: proof repairs and incomplete verification evidence

## Status of this checkpoint

**Delivery A (the actual manuscript K density bound) is not closed.
Delivery B (hUpper) is not closed.** The five existing modules remain
components with their displayed hypotheses; this checkpoint adds no new
conditional analytic assembly theorem. The common proof baseline remains
`1a80c1bcce67886f699d097fc37fd245cd3620bf`. The parent checkpoint is
`3d5dd058cf6bef5fe90719ee277580baf8b5bf41`, on
`chatgpt/chen-p4-upper`. The commit containing this file identifies the
complete source delivery; it is not a sealed proof-verification receipt.

Earlier in this continuing session, **all five strict source compilations,
all five individual original-kernel replays, and the strict compile of
`verification.Part4UpperAudit` actually returned success**. Environment
maintenance removed the raw logs, generated objects and complete compiler
inventory before the aggregate fresh replay and finalizer. A second
maintenance event removed the first recovery working directory. The proof
repairs have now been restored and their source hashes rechecked.

`OBSERVED_CHECKS.json` is explicitly a transcription of observed terminal
results, **not a reconstructed raw log**. No lost output, compiler type,
declaration count, per-declaration axiom list or final PASS is invented.
Fresh aggregate replay and final sealing did not run. This evidence is
insufficient for final P0 acceptance, despite the actual earlier successes.

## Actual earlier executions

The strict driver used the unchanged pinned `Lean.Elab.runFrontend`, trust
level 0 and warnings as errors. It was not an ordinary `lake build` run.
The five replay commands used the pinned original
`leanchecker --verbose MODULE`, with exact target replay markers checked.

| Module | Strict compile | Individual kernel replay |
|---|---|---|
| `ActualUpperPolicyDensity` | exit 0; 97.813 s | exit 0; 50.465 s |
| `UpperCoefficientPerturbation` | exit 0; 4.618 s | exit 0; 10.926 s |
| `ActualUpperDensityAssembly` | exit 0; 67.865 s | exit 0; 51.165 s |
| `RealPhysicalUpperWeightBridge` | exit 0; 4.686 s | exit 0; 12.412 s |
| `RealUpperCountingAssembly` | exit 0; 76.012 s | exit 0; 50.788 s |

The strict Audit compile returned exit 0 in 383.887 s. Its unchanged source
rejects unsafe declarations, newly declared axioms, transitive axioms other
than `propext`, `Classical.choice`, `Quot.sound`, and elided printed types.
It inventories defining-module metadata, including private, generated and
structural declarations. Its raw output was not inspected for a declaration
count or per-declaration type/axiom records before deletion, so those fields
are unknown here. The public source-type inventory is a different artifact.

An earlier per-module `--fresh` attempt was interrupted with exit 130 and
is not a success. The intended single aggregate fresh replay was never
executed. No new Lean verification is claimed during recovery: the prior
complete Mathlib object cache and verified target objects were no longer
available. No blind CI rerun or upstream polling was used to fill that gap.

## Proof changes and unchanged obligations

Only proof bodies in three of the five owned modules changed:

* `UpperCoefficientPerturbation`: make the real cast in the totient
  nonnegativity proof explicit.
* `ActualUpperDensityAssembly`: remove two unused simp arguments that the
  strict gate rejects, and use the correct additive monotonicity proof.
* `RealPhysicalUpperWeightBridge`: supply the pinned Finset API's named
  argument; repair additive monotonicity and the divisibility/congruence
  conditional rewrites, including the zero outside the source.

The other two modules and the Audit source retain their fixed bytes. No
theorem statement, constant, dependency pin, manuscript definition or
quantifier changed. The core workflow change already present at the parent
checkpoint is preserved. The owned verification runner's changes are
verification infrastructure, not additional mathematical premises or a
replacement for the missing final run.

The runner retains all five strict builds and all five individual kernel
replays, then requires a single original `--fresh` replay of the Audit
module's combined import closure. It snapshots the complete current set of
target object parts immediately after each strict build, rechecks them
around replay and at completion, and rechecks all three toolchain binary
hashes. The dependency-build allowance is 5400 seconds; the owned workflow
job allowance is 180 minutes. This addresses the observed 1800-second
dependency-build timeout without removing a proof gate or changing a pin.

The new recovery-only Python execution has **39 passing cases, exit 0**,
covering actual inventory-parser gates, object-part/byte mutation detection,
binary mutation detection, replay-marker checks and workflow outcome gates.
See `runner-recovery-python.json` and its actual stdout/stderr logs. Both
Python files passed AST parse/compile. The first fixture attempt returned
exit 1 because its last check wrongly assumed a lowercase Python outcome
guard instead of the workflow's uppercase shell guard; the original
`attempt1-*` records are retained. Only that fixture was corrected before
the successful run. These are Python checks, not Lean proof evidence.

[`SOURCE_TYPES.md`](SOURCE_TYPES.md) and
[`SOURCE_TYPES.json`](SOURCE_TYPES.json) contain the full **53 public
source-extracted theorem signatures** from the five modules. They are not
compiler-printed elaborated types and do not include private/generated
declarations. A compiler inventory must be recovered by an actual new Audit
execution; the source inventory cannot substitute for it.

## Same coefficient, carrier and normalization

For the actual raw rough policy before the outer coefficient compiler,
`actualSmallRoughRho` is the
literal small/rough attachment of `fixedRoughCoefficient`, with
`actualSmallRosserMinus` and `actualSmallRosserPlus`, and carrier
`actualSmallRoughModuli`. The policy module identifies both the coefficient
and its carrier with an even-retaining first-exit policy. The nonnegative
pointwise object is the divisor sum, not each signed coefficient.

The density is exactly `physicalDensitySum Q rho`, the reciprocal-totient
sum over that same finite carrier. The scale is
`singularSeries N / Real.log (N : ℝ)`. For count estimates, the source mass
scale is `N / log N`, and their product is exactly
`singularNormalization N`. `same_rho_normalized_mainTerm` also supplies
the exact quotient identity. The scale inequality equivalence requires
`2 ≤ N`; the algebraic identities use Lean's total division at small N.
No extra ordering factor or factor two is introduced. An upstream integral
normalized by `log (N^nu)` still needs its exact conversion to `log N`:
its coefficient converts by division by `nu` when `nu > 0`. The current
attachment estimate is not a proof of an unrelated integral's conversion.

The finite real counting bridge retains the same `Q` and `rho` in its
pointwise majorant, density, coprime correction and signed distribution
error. It retains both endpoint costs `z` and `T + 1`; the asymptotic bridge
uses `Nat.ceil ((N : ℝ)^sieveExponent)` for the strict real sieve cutoff.
The fixed legal real imbalance parameter `b` is distinct from internal
`nu`, `sieveR`, `sieveExponent` and attachment precision. The ordered source
mass is `Real.log (1 / b)` with no rational approximation to `b`.

The finite zero-coprime-correction theorem still requires actual nonzero
support to divide `sieveProduct N z` and
`(z : ℝ) ≤ T ^ (b / (1 + b))`, with `0 < b`, `0 < T`. Weighted outer-source
Fubini explicitly requires `m ≤ N` on its carrier; truncating natural
subtraction outside that range is not silently replaced by integer
translation.

## Raw-to-compiled reserve is still unpaid

`compiled_physicalDensity_le_currentK_of_raw_and_coefficient_budget` uses
one common small/rough carrier and the same two small weights. Its inputs
are a raw density cap `rawBound`, small-density bounds by `M`, and the
literal error

```lean
M * reciprocalTotientDensity rough (fun d => |compiled d - raw d|) ≤
  compilerReserve * (singularSeries N / Real.log (N : ℝ))
```

together with `rawBound + compilerReserve ≤ currentK`. Therefore a raw
bound equal to `currentK` supplies no positive compiler reserve. The
general full-policy limit theorem exposes a separate `densityCap` precisely
so that raw attachment can stop below the final K. Its `hIntegral`,
`hCertificate`, `hcap` and strict gap are still hypotheses.

The existing numerical slack can only be used after the actual full
upper-integral certificate is supplied. Neither a rational comparison, the
first-cell lower certificate nor one A5 saving discharges this premise.
`RoughPrimeSupportedAt` by itself is not the complete squarefree,
coprime-to-N, exponent and unit-bound support package.

## Fixed upstream fragments and exact remaining inputs

P0's fixed round-2 ledger inspected for this work is
`cce2334906f068fda2f58c400646366f2aa2d417`,
`verification/parts/p0/round2/ledger-final/MODULE_LEDGER.md`. It does not
certify these five new P4 modules and does not replace the accepted baseline.

P1's inspected fixed fragment is
`7f894bfb57b7aa561360e335c6d610b7c30614e0`,
`ImbalancedChen/HistoricalPrefixCertificate.lean`.
`HistoricalPrefixCapData.upperFifthPolicy_even` supplies the existing
`heven` parameter in `actualSmallRoughRho_eq_firstExitAttachment` once a
particular cap datum is supplied. Its policy equality supplies the matching
odd first-exit representation. This is an aligned finite input, but does
not construct the complete adopted datum, all historical levels, compiled
support, majorant transport or the full-density limit. No production P1
cherry-pick or uncompiled wrapper is represented as an accepted integration.

P2's inspected fixed fragment is
`076473720210ee602e6e9735902e16bb6c5f1398`,
`ImbalancedChen/Certificates/AboveMuSecondCoarse.lean`. It proves
`(640339 / 15210735000 : ℝ) ≤ totalChartIntegral`, a lower bound for one
A5-saving chart. It is not an upper bound for the complete actual policy
density. Its pointwise pullback also does not supply all integration and
domain coverage transformations needed for the full manuscript constant.

The minimal A inputs are the actual complete policy/support construction,
the normalized full-policy limit `hIntegral` with the precise even-target
filter and universal small-precision range displayed in
`exists_actualSmallRoughRho_density_le_of_full_policy_limits`, the bound
`hCertificate` for that same integral and precision, cap coverage `hcap`,
and a genuinely positive gap after all attachment/limit/compiler errors.
If the supplied analytic result is a limsup upper envelope, it must be
proved to compare with the displayed actual density; it cannot be called
that density's exact `Tendsto` limit. Complete support and pointwise
majorant after compilation are also needed for a final same-weight handoff.

The exact additional B inputs are the four parameters `hmajor`, `hdensity`,
`hcoprime`, `hdistribution` of
`eventually_RealB_le_currentK_log_of_same_rho_inputs`, all instantiated
with the same `Q delta N` and `rho delta N`. Their full source types are in
`SOURCE_TYPES.md`. P3's inspected fixed fragment
`f37f341412eb239f7e7e8937921ee8d01c9c2922` supplies normalized slot results,
not the actual same-weight prime-product-source distribution estimate and
legal smoothing transfer. A smooth outer source must explicitly majorize
the exact ordered source, retain the arithmetic range, and bound the
mass/coprime/distribution changes. The counting theorem does not assume
`hLower` and does not close any of these inputs by circularity.

## One finite next component, explicitly a candidate

[`COMMON_CARRIER_CANDIDATE.lean.txt`](COMMON_CARRIER_CANDIDATE.lean.txt)
records the selected finite extension-by-zero adapter. Its downstream
purpose is to compare raw and compiled rough supports on their union while
preserving the raw physical rho, its density sum and its divisor sum.
The required zero outside the raw first-exit support is already a finite
supplier; an arbitrary support extension does not establish legality of
the compiled support or its error bound. This file is **uncompiled**, is
not a production `.lean` import, and is outside the five-target Audit.
No theorem from it is used to claim A or B.

## Recipients

* **P0:** these proof repairs and the explicit evidence deficit; final
  acceptance needs reproducible raw strict/replay/Audit output, complete
  compiler inventory, aggregate fresh replay and source/object sealing.
* **P1/P2:** the precise remaining actual-policy, full upper-integral,
  normalization and compiler-reserve inputs described above.
* **P3:** the unchanged same-rho source-error and legal outer-transfer slots.
* **P5:** the interface/status only. This checkpoint is **not** a K supplier
  and is not a proof of `hUpper`; no completion claim should be propagated.
