# P1: actual third coarse rule, one finite increment

Status: SOURCE_ONLY, REQUESTED to P0, then WAITING_FOR_P0. No Lean, Lake,
checker, environment-loaded audit, CI, install, commit, or push was run by P1.

## Repair after the first strict attempt

P0 run `38682333676`, source `75096929`, rejected source `ca213f74` at
strict compilation in 2.872 seconds, with no memory-limit failure. The complete
original log and receipt are retained under `failures/38682333676`.

The new source is `86424459ed1208c11b400c56e1127c9fb39f2d137773eb2505c735361accbc50`.
It fixes every reported root error in one source change: fully qualify the
intended real `VariableEnvelope.B` in the two rescue signatures and relevant
unfolds; leave each conditional inside its own max leaf instead of applying
the overbroad `apply_ite` rewrite; explicitly normalize rational zero and
19/96 at the four real mesh bridges. The remaining original diagnostics were
cascades from these failures. `repair-static-checks.json` confirms all 56
declaration names, all definitions/abbreviations, and every other signature
are text-identical. No hypothesis or verification gate was weakened.
The replacement source is uncompiled and must be rechecked by P0.

## Source and scope

- Baseline: `08899a3f44fa61ea6dfe33d4cb557693cbac1590`.
- Worktree: `/workspace/shared/chen-coordination/p1-coarse-policy`.
- Exclusive new source: `ImbalancedChen/HistoricalThirdCoarsePolicy.lean`.
- Frozen source/hash and textual signatures: `source-manifest.json` and
  `proposed-types.json`; the adjacent `.lean` is an exact snapshot.
- Frozen specification: manuscript repository
  `ba6ec11d800eccc54406490631895e174de85766`,
  `proof-library/source/upper-finite-compact-margin-audit-20261010.txt`,
  blob `0bf009e7a3de5524dc728029af65e9b29fed1fa1`, lines 38--130.

This is a concrete, generated finite third-coarse **subpolicy**, not a full
instantiation of the manuscript upper strategy. It selects wholly ordered
closed rectangles from the half-open `[0,19/96)^3` mesh, requiring the
first-label upper stop and width bound. It keeps the inherited policy on
the other cells. There is no arbitrary user-supplied cap or Gamma property
field. The partial coverage boundary is explicit and must not be erased
when integrating this file.

## New mathematics represented by the source

1. `xzGap` and `yzGap` are exact whole-rectangle infima of the complete
   selected-product gate gaps. `xzGate_iff` and `yzGate_iff` prove the
   pointwise-for-all-box-points equivalence, by monotonic affine pieces and
   the actual upper-corner witness. They do not replace `inf v` by `v(upper)`.
2. `rescue` is `max(qA lx,qB uz)`. Its lower-bound and mixed-corner
   attainment theorems concern the actual `max(A,W)` rescue. No ungated W
   action or W licensing at the actual lambda is asserted.
3. `interval_lower_endpoints` and `interval_lower_iff` identify the exact
   interval infimum used in the branch expressions, including the mu peak.
4. `fullGamma` takes the specified six-entry maximum, including each
   nonleading pair exactly when its complete whole-box gap is at least e.
   Failed pairs contribute the already-present baseline. `gamma` uses
   the full rule only if `ux <= mu-4e`; the complete transition region uses
   `qVLo lx ux`. This is not `ScaledBox.extendedClippedLower`.
5. `gamma_le_cap`, `fullGamma_le_original` and `gamma_le_endpoint` prove
   the actual coarse lower bound and the ceiling `Lambda=153/256`.
   `levelExponent = Gamma-2e`, `initial = Theta-2e`, and
   `levelExponent_lt_initial` prove the strict descending comparison.
6. `first_cube_margin`, `first_prime_cube` and
   `rawLevel_first_cube_on_cell` pay the strict first cube from the genuine
   Gamma baseline, first stop and interval width. They require
   `0<e<gamma/100`, `chi<e/10`; the stronger second chi condition from the
   approximation proof is not needed for these statements. There is no
   assumption that a third cap exceeds the initial exponent.
7. `cells` and the rational Gamma list precede omega and N. The lookup
   stores rational Gamma, then subtracts the common real `2e`, so e is
   not silently restricted to rational values. `rawLevel` tests the literal
   `N^omega <= p3`, with equality active. Failure or an unselected cell
   returns `N^(Theta-2e)`.
8. `frozenLevel_append` and `frozenActive_append` show that all later
   prepended selections retain the same rank-three ancestor and rough
   decision. `policy_through_two`, `policy_even`, `policy_inactive` and
   `policy_third_iff` give the finite-policy dictionary. The last theorem
   retains the third level's own first cube and strict third cube.
9. `initialPolicy` explicitly includes the first coarse-label upper-endpoint
   stop at rank one; `firstStop_of_triple_cell` binds a selected third cell
   to that inherited first label. It does not claim a new fifth-parent
   seven-gate formula for this altered initial policy.

## Exact unpaid work

- The approximation estimates (C3) and (C5), in particular
  `0 <= L_endpoint - lambda <= 4e + 6chi`, are not proved and are not
  inserted as certificate/structure fields.
- Coverage and small density cost of the omitted order-wall cells, and a
  sufficiently fine finite mesh covering the needed compact set, remain
  unproved. This implementation interprets its adopted boxes as wholly
  ordered rectangles; it does not identify rectangle infima with infima
  over a larger rectangle's ordered intersection.
- The W auxiliary level and the other analytic licence reserves from
  audit lines 95--130 are not paid. The actual density cap stays lambda;
  no auxiliary level is used to inflate it.
- The complete proper-parent/fifth-frontier dictionary for this explicit
  first-stop policy is not yet connected. Only the immediate third test
  reuses the accepted `historicalUnorderedThird_admissible_iff`.
- Successor fourth/fifth levels, actual finite-tree-to-integral identities,
  full numerical K/c, signed distribution, hLower and hUpper remain open.
- All 56 textual source declarations remain uncompiled. P0 must obtain
  elaborated complete types, generated/private inventory, original-object
  replay and full transitive standard-axiom checks under the standing gates.

## Existing suppliers and resource boundary

The exact source bytes of `FinitePrimeGeometryCore` and
`HistoricalUnorderedThirdGeometry` match the leaves accepted by P0 run
`38671169182` (70 and 36 complete declarations respectively). Receipt SHA256:
`ca0a40b5300acd7ea46c5287cc4c956a2f35b56bc476c6087ff36c7082893747`.
That leaf acceptance is reused with its stated imported-dependency scope.

`BufferedFirstCubeGeometry`, `VariableEnvelopeRegularity`,
`RationalBox`, and `SelectedPrefixRationalMesh` are existing project
suppliers at this baseline. No new independent acceptance is claimed for
them; P0's exact closure still controls their imported objects. Textual
closure has 39 project modules and 21 goldbach modules, no
`PrimeNumberTheoremAnd`, `Wiener` or `ZetaBounds` node. Mathlib and Lean
frontiers are opaque fixed-pin boundaries in this static evidence.

No public root, existing accepted source, pin, workflow or other part's
source was edited. Only P0 may validate and publish. After receiving the
frozen request, the next P1 action is a repair of exact P0 feedback, or a
new explicitly scoped mathematical increment after acceptance.
