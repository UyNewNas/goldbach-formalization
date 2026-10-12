# Part 1 round 2: historical fifth common cells and actual prime integrals

## Status and fixed references

**Current status: UNCOMPILED CANDIDATE.** The two production files and the
computation probe are written. Independent static review of the geometry
has found no necessary change. Strict compilation, original `leanchecker`
replay and the complete defining-module axiom inventory remain pending.
This paragraph must be updated only from the actual current-source receipt.

The separate main queue has now been stopped at its supplier-recovery
checkpoint: **162 of 683 local entries** are complete (44 archived reuse,
118 actual supplier compilations). None of the four new historical targets
started. The queue's observed session exit was 130; no independent child
exit was observed. [UNCOMPILED.json](UNCOMPILED.json) records the exact source
identities and `STOPPED_PENDING` scope. [CHECKPOINT_EVIDENCE.tar.gz](CHECKPOINT_EVIDENCE.tar.gz)
preserves the original logs, source snapshots and verified completed-entry
bindings, with archive metadata in [CHECKPOINT_ARTIFACT.json](CHECKPOINT_ARTIFACT.json).
These are recovery evidence, not successful historical-target validation.

The independent [stored-cap permit milestone](permit/HANDOFF.md) has its
own three validation targets and evidence. Its result does not compile or
validate the historical geometry/integral candidates described here. For
the present delivery, Part 0 should use that milestone's now-verified leaf
import proposal and complete current-source receipt; the candidate import
proposal below remains pending separate validation.

| Reference | Complete identity |
| --- | --- |
| Common mathematical baseline | `1a80c1bcce67886f699d097fc37fd245cd3620bf` |
| Source branch | `codex/variable-envelope-boxes` |
| P1 delivery branch | `chatgpt/chen-p1-history` |
| Previously verified P1 milestone | `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` |
| Observed delivery parent | `7f894bfb57b7aa561360e335c6d610b7c30614e0` |
| Observed parent tree | `acf949dc236cd9856308eaeaf50db095e7d6901d` |
| Frozen manuscript commit | `ba6ec11d800eccc54406490631895e174de85766` |
| Frozen manuscript body blob | `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` |
| Fixed Lean | `leanprover/lean4:v4.33.0-rc1` |

The observed parent is an external workflow-only change after the previous
verified milestone: the Lean job timeout is 150 minutes and its full-build
step timeout is 90 minutes. This batch preserves that change. It does not
replace the common mathematical baseline or change any dependency pin.

The previous milestone already supplies the ordinary-parent lower-fourth
restoration integral and finite inherited third/fourth/fifth cap interface.
Its six strict original-frontend compilations, six original checker
replays and 150-declaration audit are recorded in the parent directory.
Those historical successes are not current round-2 target successes.

## Fifth-candidate reconciliation and present scope

The initial bounded upstream intake is [UPSTREAM_INTAKE.md](UPSTREAM_INTAKE.md)
and [upstream-intake.json](upstream-intake.json). The final read-only refresh
is [FINAL_HEAD_RECHECK.json](FINAL_HEAD_RECHECK.json), with fixed-source
details in [FINAL_P0_INTAKE.md](FINAL_P0_INTAKE.md) and
[FINAL_P2_INTAKE.md](FINAL_P2_INTAKE.md). P0's integration head
`28fd630ef7cc38eba86beb6c0ba123336b5d05f2` has now accepted all four
production modules from the previous verified P1 milestone and imports
them in its public root. Exact-head GitHub step metadata subsequently
reports successful root build, original checker, axiom audit and full-type
export; that metadata is not a new local replay or raw-artifact audit here.
The separately reported
inherited-fifth integral candidate remains **SOURCE_PENDING**. This batch
does not identify newly written files as that missing source. To receive
it, Part 0/P1 still need its full SHA or patch, filename, dependencies and
actual original validation logs.

The candidate contribution here is the historical **actual prime-tuple
correction**: its exact common-cell decomposition, actual arithmetic
fallback, and genuine Ico-cell integral limit. The full nested
`actualHistoricalFifthSaving` to tuple-sum identity is a separate remaining
link. No theorem in this batch asserts the full adopted retained-polynomial
fifth density limit or numerical K/c bounds.

## Files and ownership

| Owned new file | Responsibility |
| --- | --- |
| `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean` | Exact actual third-capped parent on a common fifth cell, inherited level dictionaries and strict affine gates |
| `ImbalancedChen/ActualHistoricalFifthCellIntegral.lean` | Actual prime correction, exact cell decomposition and fallback, separate old/new residual sums, real integral and finite-family limit |
| `verification/parts/p1/round2/HistoricalCellProbe.lean` | Kernel finite-check and rational-point regression for the distinct historical gates and residual cutoffs |
| `verification/parts/p1/round2/Part1HistoricalCellAudit.lean` | All declarations defined by the two production modules and probe, including private and generated declarations |
| `verification/parts/p1/round2/check.sh` | Explicit stock-CLI reproduction targets, for an environment where the pinned Lean CLI starts |
| `verification/parts/p1/round2/KEY_THEOREM_TYPES.md` | Complete source types and their actual audit correspondence when verification finishes |
| `verification/parts/p1/round2/UPSTREAM_INTAKE.md` and `upstream-intake.json` | Read-only, fixed-SHA intake and cross-Part distinctions |

Public root imports and canonical integration gates belong to Part 0.
An explicit P1 module build is required before those root imports are
integrated; a root build without them does not cover these new leaves.
[INTEGRATION.patch](INTEGRATION.patch) is an unapplied cumulative proposal
for the original root file: it includes the prior lower-fourth/historical
imports and the two new leaves. It remains a candidate-only proposal and
is not the incremental patch for P0's current root. For the independently
verified permit, use [PART0_28FD_PERMIT_IMPORT.patch](PART0_28FD_PERMIT_IMPORT.patch)
against the exact P0 root at `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`.
Its successful text applicability check is recorded separately in
[PART0_IMPORT_CHECK.json](PART0_IMPORT_CHECK.json). No public root was edited.

## Fixed data and coordinate contract

This batch consumes the already verified `HistoricalPrefixCapData`.
Its rational endpoints, mesh size, selected sets and cap tables at ranks
3, 4 and 5 are fixed before the target integer `N` is introduced.

| Item | Required convention |
| --- | --- |
| Coordinates | Processing order `t0 > t1 > t2 > t3 > t4` |
| Stored history | Reverse processing order; `rosserAncestor` agrees with projection to the first processing coordinates |
| Grid | One common rational grid `a + i * ((b-a)/(m+1))`, cast exactly to the reals |
| Cell ownership | Coordinatewise lower-inclusive, upper-exclusive `Ico`; every shared face has at most one owner |
| Arithmetic carrier | Actual prime tuples, every `p i` prime with `p i ∤ N`, strict upper power cutoff, explicit enumeration cap |
| Parent first gate | `3*t0 < D.old` |
| Parent third gate | `t0+t1+3*t2 < D.cell3 (project3 j)` |
| Old fifth residual | `D.old5 j = D.cell4 (project4 j)`, including fourth-to-third fallback |
| New fifth residual | `D.cap5 j` on `j ∈ D.cells5`; otherwise the complete inherited fourth level |
| Own-cube test | `sum t + 2*t4 < lambda`, evaluated independently at the old and new level |
| Cap coverage | `(N : ℝ)^D.b ≤ cap`; the ceiling enumeration supplies this directly |
| Finite legality | `D.levelCheck = true`, a finite rational level-order check; no K/c or integral bound hypothesis |

Part 2's current publication head is
`e6d6d57323cc358cef060fb243ec386c13cb662d`, with new mathematical sources
at `f0c00f9ccce98e04af439321a92eb9fd0dd26203`. Its E0 fibre uses
`(t,u,z,w)` and a frozen endpoint `Z = min(ul, (3/13)*(1-tr-ur))`.
Prefix64 now includes Prefix4 and the sixty new rows `[4,64)`; these
overlapping results must not be added again, and `K/80` already includes
the quarter factor. The P1 interface file is unchanged. Those data are a
separate analytic object from P1's lower-fourth Rosser restoration. In
particular, `exact_Z` is not a historical stored cap. The new batch does
not instantiate this historical fifth table or discharge its arithmetic
ownership and support licenses. See [FINAL_P2_INTAKE.md](FINAL_P2_INTAKE.md)
for the producer evidence and the remaining interface inputs.

## Exact historical geometry

For a fifth cell `j`, write

```text
j3 = historicalPrefixProject (3 <= 5) j
j4 = historicalPrefixProject (4 <= 5) j
third_j = D.cell3 j3
old5_j = D.cell4 j4
new5_j = D.cap5 j.
```

The common geometric parent is precisely

```text
R_j = cell_j intersect
  {t | t0 > t1 > t2 > t3 > t4,
       3*t0 < D.old,
       t0+t1+3*t2 < third_j}.
```

`fifthParentGateBounds` supplies bounds for the six existing nonzero rows
`ordinaryUpperFiveGateForms`; the rows are reused without a new linear-form
implementation. `mem_fifthParentGateRegion` proves the displayed domain.
`historicalUpperFiveFrontierTuples_cell_filter` identifies the actual
rank-four frontier of `D.upperThirdPolicy N`, filtered to `cell_j`, with
the actual target-deleted prime box filtered to `R_j`. The fourth level
does not add an admission test to this parent, and neither fifth own-cube
test restricts its candidate enumeration.

The finite proof retains complete ordinary admissibility, including its
total-product condition. It reuses `ordinaryUpperFive_parent_valid_iff`
at the effective third level and uses the checked inequality
`D.old ≤ third_j` to keep the first gate at the original, smaller level.
No total-product hypothesis is silently dropped.

`level3_on_fifth_cell`, `level4_on_fifth_cell` and `level5_on_fifth_cell`
link reverse-stored actual histories to their projected effective cells.
The fourth dictionary gives `N^(D.old5 j)` even when the fourth cell was
not selected. `level3_tuple_on_fifth_cell` gives the exact processing-tuple
form used by the arithmetic frontier proof.

## Actual correction, support and fallback

Let `A_lambda(N,p)` denote `actualPrimeTupleOwnCubeMinus N cap lambda p`.
It already includes the residual normalization `log N / singularSeries N`
and its own-cube indicator. Define the tuple difference by reading the
fifth and fourth levels from this same tuple:

```text
Delta(N,p) = A_exponent5(log_N p)(N,p)
             - A_exponent4(project4(log_N p))(N,p).
```

`fifthPrimeCorrection` is the literal finite sum over the actual
third-capped rank-four frontier of

```text
(product_i 1/(p_i-1)) * Delta(N,p).
```

There is no additional outer normalization. The selected fifth-cell
theorem replaces `Delta` by `A_new5_j - A_old5_j` on that same owned cell.
`fifthTupleOwnCubeDifference_on_unselected_cell` and
`fifthTupleOwnCubeDifference_outside` prove exact zero contributions
before a limit is taken. The latter applies outside every selected cell,
including outside the ambient cube.

`fifthPrimeCorrection_eq_cells` is the exact finite identity

```text
D.fifthPrimeCorrection N cap
  = sum_{j in D.cells5} D.fifthCellPrimeCorrection N cap j.
```

It follows from unique Ico ownership and the existing arbitrary-function
exponent-difference identity. It introduces neither an arithmetic-boundary
remainder nor a discarded tail. This is a support statement about this
correction. It is not the complete physical support or well-factorability
license for the adopted sieve weights.

On a selected cell, `fifthCellPrimeCorrection_eq_residual_sums` gives the
literal difference of `actualPrimeBoxOwnCubeMinusSum` at `new5_j` and
`old5_j`, both on `R_j`. The old and new own-cube indicators stay inside
their own actual residuals throughout that equality.

## Genuine real integrals and their limit

Write

```text
Phi5(t) = sum_i t_i + 2*t4
g_lambda(t) = 1_{Phi5(t) < lambda}
  * (2*exp(-gamma)/t4)
  * suzukiContinuousLowerFactor(max 2 ((lambda-sum_i t_i)/t4)).
```

The definition `fifthCellIntegral` is the difference of two genuine
`primeOwnCubeIcoIntegral` values, and
`fifthCellIntegral_eq_integral` proves its single-domain form

```text
I_j = integral_{R_j}
  (g_new5_j(t) - g_old5_j(t)) * product_i (1/t_i) dt.
```

`fifthCorrectionIntegral` is the fixed finite sum of these `I_j` values.
It is defined as an integral, independently of any prime-sum limit or
certificate endpoint. With `0 < D.a < D.b`, `0 < D.old` and the finite
`D.levelCheck = true`, `tendsto_fifthPrimeCorrection_ceil` asserts

```text
D.fifthPrimeCorrection N (ceil(N^D.b)) --> D.fifthCorrectionIntegral
```

along positive even integers tending to infinity. Its general-cap version
requires only eventual cap coverage. The proof applies the existing
actual-prime Ico integral supplier separately to the old and new levels,
then sums the fixed finite selected family.

The boundary argument comes from that actual-prime supplier. The finite
weighted ramp-gap estimate in
`ImbalancedChen.tendsto_actualPrimeBoxTestSum_cube_affineSandwich` controls
the actual discrete prime contributions, including atoms on a wall. It
uses the private source lemma `affineSandwich_test_error` in
`ImbalancedChen/ActualPrimeIcoCellTestFunctions.lean` and nonnegative
actual prime weights, followed by the continuous-test prime-sum limit.
The same file's private `integral_affineSandwich` uses null-wall identities
only for continuous integrals. No zero-volume assertion removes a discrete
prime contribution. This describes the proof dependencies; it does not
claim that a separate boundary-mass Tendsto occurs earlier in the source
script than every use of a continuous integral identity.

## Regression point

The probe fixes one selected cell at every rank, with

```text
a = 1/100, b = 1/4, m = 0,
old = 1/2, cap3 = 3/5, cap4 = 5/8, cap5 = 2/3,
t = [3/20, 3/25, 1/10, 9/100, 13/200].
```

It checks the actual finite `levelCheck` by kernel decision and proves
that this point belongs to its Ico owner and historical parent. Here the
third parent form is `57/100`: the root-old ordinary parent rejects it,
while the inherited third cap accepts it. The fifth own-cube form is
`131/200`: the effective fourth old residual rejects it, while the fifth
new residual accepts it. This regression distinguishes the two domain
issues. It is not an adopted manuscript certificate or an actual prime
tuple at a specified target.

## Unclosed inputs and receiving Parts

| Receiver | Delivered interface and remaining input |
| --- | --- |
| Part 0 | The four prior `b09d5361e0b30f3e85cb912a03c7bfb85a99bf8f` production leaves are already accepted and imported at `28fd630ef7cc38eba86beb6c0ba123336b5d05f2`. Integrate only the new verified permit through the separate incremental patch and run its canonical integration gates. Keep the two historical leaves here outside verified imports until their own gates finish. |
| Part 2 | Supply fixed adopted common-grid/history data, prove the finite `levelCheck` and the actual whole-box/square/support licenses, and connect its fibre coordinates and boundary treatment to unique arithmetic Ico ownership. No final K/c bound is needed to use the current geometry or prime-integral supplier. |
| Part 3 | Use the fixed actual arithmetic parent/carrier dictionary; the complete adopted coefficient support and factorization license still needs its own checked construction. |
| Part 4A | Use the precise inherited old level, separate own-cube gates and residual-cell formula; remaining adopted physical support and distribution interfaces are not implied by a level-order check alone. |
| Part 5 | Consume the genuine lower-fourth and historical fifth-cell integrals only after the adopted finite ledger and density links are proved. The new prime-tuple limit still needs the `actualHistoricalFifthSaving` nested-sum bridge before insertion into a full upper retained-polynomial density formula. |
| Part 0 / Part 1 | Receive the reported independent fifth candidate when its source identity becomes available; complete the adopted upper/lower policy instance, all-layer composition and any truncation licenses beyond the explicit fixed ambient cap. |

The lower-fourth restoration from the previous delivery, the ordinary
parent fifth integral from the original baseline, the historical finite
telescoping identity, and this historical tuple-cell supplier are distinct
components. Their complete adopted combination remains an integration
proof obligation.
