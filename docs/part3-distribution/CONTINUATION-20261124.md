# P3 continuation from c509267

## Baseline and scope

The baseline is `c509267dc630d91df33033abde1c484ec86b96ae` on
`codex/p3-formalization-20261123`. The actual original successful receipt
was located in the user-selected Workspace Compile 27f68009 environment,
at `/workspace/goldbach-p3/.lake/p3-fourth-verification/report.json`.
It records **80 modules and 1,774 declarations**. Its exact bytes are
preserved in [baseline-c509267-report.json](continuation-20261124/baseline-c509267-report.json).
All 80 baseline Lean source files remain byte-identical. Their existing
proof objects and receipt are reused rather than revalidated.

The frozen manuscript is the 2026-11-06 release at
`chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
The earlier equation (24) is the stable label `ana:spectral-polynomial`,
equation (96) in that release. The prime-product target is
`eq:current-PP`, Proposition D.3.

## Verified checkpoints and current source

At `60cf3d49f8aefc687a6ce3dd7008ae5804cc61d3`, all seven continuation
modules have strict compilation, kernel replay and complete serialized
inventory/transitive-axiom acceptance: five proper-power modules with
77 declarations, and two unchanged spectral modules with 88 declarations.
The only allowed transitive axioms are `propext`, `Classical.choice`,
and `Quot.sound`.

At `70e8f69cbbacb2b851147a5fa51948a106beeca7`, the public-helper
LogSaving version and the new ChartSum both passed all gates in the
selected workspace: 9 and 11 declarations, respectively. Selecting the
latest complete inventory per defining module gives **8 continuation
modules and 176 declarations** (`68 + 88 + 20`), without re-counting the
old private-helper LogSaving inventory. Together with the unchanged
baseline this is 88 modules and 1,950 declarations, not a certificate
that the full P3 targets have been proved.

The machine-readable [aggregate](continuation-20261124/aggregate.json)
validates the saved ZIP/report/inventory/log evidence and the current
source/import closure for each selected module. It performs no new Lean
compilation and explicitly records that P3 remains open.

## Implementation plan and completed mathematics

1. The whole-modulus signed kernel is paid using the existing nonzero
   distance divisor bound, keeping the same complex rho, complete
   product, coprimality predicate and totient denominator. The actual
   product-equals-target diagonal is kept separate.
2. The actual labelled proper-power residual is bounded by the existing
   proper-prime-power count. Its zero fibre and diagonal multiplicity
   are proved, then connected to the exact prime/von Mangoldt identity.
3. The box budget gives `x^(1-a/2)`. Original integer-shifted dyadic
   windows and the effective source support supply the padded box
   geometry and physical cap; empty effective charts have zero residual.
4. Existing divisor subpower, weighted divisor means and logarithmic
   absorption pay the actual distance budget, exact coprime mean and
   full-product diagonal, uniformly in individual original charts.
5. The new ChartSum source reconstructs the complete original residual
   and same-rho signed error before taking norms. Its bank cardinality
   costs `log(N)^k`; invoking the per-chart result at `A+k` gives arbitrary
   logarithmic accuracy for the full residual and for prime minus VM.
6. The spectral adapters extend a supplied full-block energy estimate
   to common integer intervals, arbitrary physical weight and two level
   windows. They preserve the full threshold power and actual `4*pi`.
7. Strictly compile, kernel-replay and audit only affected modules using
   the original pinned toolchain, then retain exact source hashes,
   complete declaration types and actual logs. No source-only check or
   conditional transport theorem is a certificate of the full P3 target.

## Boundaries

The proper-power result estimates the actual labelled residual. It does
not assume the desired residual bound, the box volume or a uniform
nonzero-distance divisor estimate. The original chart bank has now passed strict compilation, kernel
replay and the complete declaration/transitive-axiom gate. The physical cap, logarithmic growth, divisor/mean masses
and complete diagonal have already been paid in the accepted per-chart
proof. Actual upper/lower/marked source instances must still provide
uniform amplitude and geometric support on **nonzero W * VM integer
support** and the fixed divisor-order bound for their actual rho.
Prime-only support cannot replace that integer-source geometry.

The spectral extension consumes an explicit full-block classical
estimate and an eigenvalue bound. It does not assert their instances on
the actual automorphic spectrum. No ordinary Bombieri--Vinogradov bound
is substituted for the missing spectral estimate. The frozen
manuscript's external Kuznetsov, ABL, Kim--Sarnak and Pascadi inputs stay
visible. `RestrictedMediumObligation`, `UniformPrimeProductTarget` and
the full P3 assembly remain open.

Pascadi's full-block exceptional Theorem J permits threshold
`max(V, Z^2/V)`. The common-phase clause, exact integer endpoints and
physical `4*pi` normalization are all retained.

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

| Module | Status | Accepted declarations |
| --- | --- | ---: |
| `Part3SignedModulusPayment` | Full acceptance at `60cf3d49` | 21 |
| `Part3ProperPowerResidualPayment` | Full acceptance at `60cf3d49` | 23 |
| `Part3ProperPowerDyadicBudget` | Full acceptance at `60cf3d49` | 7 |
| `Part3ProperPowerOriginalChart` | Full acceptance at `60cf3d49` | 17 |
| `Part3ProperPowerLogSaving` | Public-helper version fully accepted at `70e8f69c` | 9 |
| `Part3ProperPowerChartSum` | Full acceptance at `70e8f69c` | 11 |
| `Part3ExceptionalWeightExtension` | Full acceptance at `80d7eeb`, unchanged | 43 |
| `Part3ExceptionalWeightGeometry` | Full acceptance at `80d7eeb`, unchanged | 45 |

## Actual original-chart geometry and logarithmic saving

The accepted OriginalChart source has SHA-256
`50a372771ebfa4cee6554402e938e5b7d334bd3cc1c0440a57df39c86fed26ca`.
It reuses `originalDyadicChartWeight chi L j` for arbitrary integer `L`,
with `U_i = Nat.ceil (2 * 2^(L+j_i))`. An effective integer witness gives
`U_i+1 <= 5*n_i`, hence padded box volume at most `5^k*C*x` and physical
cap `Nat.ceil (5*C*x)`. Without an effective witness the actual residual
is identically zero, including the empty-rank case.

The accepted LogSaving proof uses the actual distance budget over
`B.erase N`, with `B` contained in `[1, ceil(C*N)]`, while retaining the
complete `N` diagonal with `tau(N)^k`. The exact primitive mean has a
separate logarithmic estimate; it is not bounded by the much larger
total modulus mass. The threshold precedes all varying carriers,
weights, cutoffs and charts. The accepted private-helper version has
SHA-256 `289913d4c27daee7b556f7d4a1bd5d68c38b44f375cde28baa16905665c672fc`;
the current public-helper version has SHA-256
`136815a60067b4e7eded3df5f9782b2d0cb3632d3e5da510019a04b6c86b5954`.

## Accepted full original chart bank

`Part3ProperPowerChartSum.lean` has source SHA-256
`6033d5b3e829400a2b91bd8c55f7a61b4adcc72b853c1d6beff412aab0fac9c1`.
It takes `L=0`, `H=Nat.log 2 (Nat.ceil (C*N))+2` and the tensor bank of
`range H`. Every effective integer coordinate is positive and at most
the complete product, so the original partition covers proper powers
as well as primes. The bank depends on the physical cap, not on rho.

The proof first reconstructs the actual union residual pointwise, then
its original signed error. There is no overcounting of tuples with
multiple proper-power coordinates and no deletion of the product-N
diagonal. The exact bank cardinality is `H^k` and is at most
`(2/log 2 + 2)^k * log(N)^k`. The existing per-chart theorem at accuracy
`A+k` and suitably divided epsilon pays the full bank. A final corollary
uses the unchanged exact prime/von-Mangoldt identity. Independent review
found no blocking mathematical issue. The first selected-workspace run
built both modules and strictly compiled LogSaving, then rejected an
unused `ring` after a `field_simp` that had already closed the goal. The
redundant tactic was removed without changing any statement or disabling
lint. The corrected two-module run then passed all strict, kernel and
full inventory/transitive-axiom gates at `70e8f69c`.

## Requested compilation environment and receipts

All subsequent compilation uses **Workspace Compile 27f68009**, as
explicitly selected by the user. The original workspace was found at
`/workspace/goldbach-p3`, initially clean at c509267, with 9,336 existing
Lean objects. The continuation branch was fetched into that worktree
without replacing the original branch ref. Lean is `4.33.0-rc1`, commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`; Mathlib is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Actual pinned revisions and
clean status of all eleven manifest packages passed the gate.

The five-module proper-power verification task
`01939e7a38db48588e48759820e6a787` completed successfully in that workspace
at `60cf3d49`, with 77 declarations. It ran all strict, literal kernel
replay and full inventory/transitive-axiom stages, and final clean-tree
checks. The [complete receipt](continuation-20261124/proper-power-60cf3d49/README.md)
retains the exact report, declarations and ZIP of all logs. ZIP SHA-256:
`0f6b483e36815cd341896b8e84027a7a4c7540fa49c9317b29567a054cc15fee`.

The [two-module spectral receipt](continuation-20261124/spectral-80d7eeb/README.md)
remains valid for its unchanged source hashes, with 88 declarations.
GitHub run `45343356986`, job `138272108983`, artifact `14897342383` passed
all gates at `80d7eeb`. Its ZIP SHA-256 is
`02b1f2f9dd1afb828166ae4ee619481c0e71d706e8aba678a90144ac1ededb1e`.
Both archives were checked against their recorded log digests, source
hashes, literal module replay messages and complete inventories.

The full chart-bank verification task
`e59ba7fbaf2c4d1fb38d51af2c0b6580` succeeded with exit code 0 at
`70e8f69c`, covering the current LogSaving and ChartSum with 20 declarations.
The [complete receipt](continuation-20261124/chart-sum-70e8f69c/README.md)
retains all stage logs, types and hashes. ZIP SHA-256:
`f99f8e72deedc8a7b0b6468da82c230a9ca3db9dfa9db0fff9f387ba46def6a2`.

## Actual-source reuse identified for the next connection

The blue snapshot `10b89181754c78c0e77616677295ee2105de0bb6` already has
an accepted `P4BSmoothPrimeVariableProfile` (batch86), source SHA-256
`ca93e79e4022b473e0b2ce90e766b14d84eec76e15ba4b2eb79d32c34d0deca5`.
Its positive-real support theorems apply to effective VM integer tuples,
so the actual rank-two smooth pair has amplitude one, lower coordinate
scale `N^a`, and complete-product cap `exp(width)*N`. This supplier will
be reused rather than re-proved. Its 94-module project closure shares
74 identical files with this P3 baseline, adds 19 missing files, and has
one definition-placement conflict in `ActualSmallRoughAttachment`.
A compatibility import must retain the same literal rho definitions and
avoid duplicate declarations or changes to the accepted baseline.

The actual upper/lower rho amplitude bounds already exist. A literal
final-policy instance still needs that same policy's active-modulus cap;
the old `policy8` range cannot be substituted for a different final
policy. A prime-filtered marked weight likewise cannot stand in for the
unfiltered smooth integer source used by VM/HB.

## Historical compilation continuity

The old Cloud Compile connection reached its 128-retained-task limit.
Its single-module strict/kernel receipt is preserved in
`continuation-20261124/cloud-modulus-receipt.json`. This limit does not
apply to the newly connected, user-selected Workspace Compile service.

The earlier GitHub proper-power run `45340826739`, job `138263810092`,
at `21bd742f8e42e7ba2fb507bddc47ff40d94b25f2` built the actual residual
module and found a dyadic-budget `add_le_add_right` API mismatch. The
replacement `refine add_le_add ?_ le_rfl` preserves the theorem statement
and is now fully accepted in the successful workspace run above.
The failed historical artifact is `14898615187`, SHA-256
`c8ab6a5e44d47b2b32cce50871f1de5c59f5ffcafa945b7fb0730ec0fdb351bd`.
Its reusable dependency cache is retained; no new GitHub CI is started
for checkpoints compiled in the selected Workspace environment.

This file is a work ledger, not a completion certificate for P3.

## Actual-pair integration candidate

`Part3ProperPowerActualPair.lean` now applies ChartSum to the literal
`smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width`.
The VM-effective integer support gives positive coordinates, and the
already accepted positive-real P4B profile supplies the lower scale and
product cap. The existing pointwise profile bound gives amplitude one.
Thus this source's `hGeometry` and `hW` are proved rather than assumed.
The final threshold remains before B/Q/rho/chi. The modulus cap, fixed
rho divisor order and original cutoff conditions remain explicit.

Fifteen missing donor files are copied byte-for-byte from the fixed blue
commit; three reuse the exact existing accepted proof repairs at
`48db3d603d632bc60037e149a55717832e4c04be`, after the dependency build showed
that the canonical blue tree still held their preimages. Those repairs
preserve imports, definitions and theorem statements. `FiniteUpperCarrierCore`
imports the unchanged existing Attachment
instead of redeclaring its two identical rho/carrier definitions; every
old finite identity proof is retained. The full adapter import closure
has 125 project modules, no missing file and no cycle. Independent review
found no blocking semantic issue. [Provenance](continuation-20261124/actual-pair-reuse/README.md)
binds all file hashes and the original profile acceptance. The changed
Core and actual adapter await a dedicated two-module acceptance; the
previous eight-module receipt remains valid for its unchanged sources.

## Task-internal parallel compilation

Workspace Compile 27f68009 permits four CPU quota cores but executes one
service task at a time. A capability probe ran two independent direct
`lean -j1` processes concurrently in one task. Both exited successfully and
produced their own objects; their execution intervals overlapped for 0.425
seconds. The task used 0.8 CPU-seconds in 0.501 seconds of wall time, with a
combined sampled peak RSS of 994,582,528 bytes. The exact report is retained
in [parallel-compile-capability.json](continuation-20261124/parallel-compile-capability.json).

This establishes lightweight task-internal parallelism, not a safe budget
for two full-Mathlib compilations: the current dependency run alone reached
8,671,346,688 bytes, and heavier preliminary probes exceeded their small
2/4 GB allocations. The probe adds no manuscript theorem or P3 acceptance
credit. Independent lightweight work can be parallelized; heavy proof gates
retain an explicit memory budget and preserve their dependency order.

## Existing regular-spectral proof to reuse

The archived `Part3RegularCumulativeShellPayment` and
`Part3RegularPositiveMeasureExhaustion` at `fa22a56829ee880404516a36d498ce27dcb32f92`
already contain the manuscript's genuine positive-measure shell argument,
including local L2, global integrability and the full absolute integral
bound. They are source-only candidates, with no acceptance receipt found;
their analysis should not be duplicated. The latter's source SHA-256 is
`9cee631c6bdfd388c1d3987b16a495e2550cd94d2912d3a20cbe2eefd62e5d71`.
The actual 1106 regular direct-sum measure and coefficient arrays still
need a compatible connection. The older continuous consumer uses native
`dt/cosh(pi*t)` and an exterior `1/(4*pi)`, so it cannot be silently
identified with the manuscript's printed `dt/pi` normalization. Existing
printed-normalization candidates remain the intended reuse path.
