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

The current source adds `Part3ProperPowerChartSum` and makes the already
proved `ProperPowerLogSaving.log_ceil_linear_le` public, without changing
its proof. These two current module versions are not yet compiler-verified.
Their dedicated `--group chart-sum` verification will reuse the other six
accepted modules. A final aggregate must select the latest verified
version of each module: the old nine LogSaving declarations must not be
counted again alongside the replacement LogSaving inventory.

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
nonzero-distance divisor estimate. The original chart bank now has a
source implementation and independent semantic review; its validation
is pending. The physical cap, logarithmic growth, divisor/mean masses
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
| `Part3ProperPowerLogSaving` | Full acceptance at `60cf3d49`; public-helper revision awaits revalidation | 9 at accepted revision |
| `Part3ProperPowerChartSum` | Complete source and independent semantic review; not compiled | Pending |
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

## Full original chart-bank source

`Part3ProperPowerChartSum.lean` has source SHA-256
`57b29276be9b5ece9a2f794f78d84e488ecc91a9e6983844121d00bb6a1c5fae`.
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
found no blocking mathematical issue; compiler validation is pending.

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
