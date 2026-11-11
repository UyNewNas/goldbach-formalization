# P5.6 / h34 — exact source-occupied finite-position slack

Date: 2026-11-12 (Asia/Shanghai).
Repository: UyNewNas/goldbach-formalization.
Dedicated h34 branch: chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109.
Verified baseline HEAD: 4ccd980c1b10f3d96479ed5241d32b4c46e94c86.
New manuscript-INTERNAL Lean source commit: bfb7c9eaeb294c73f38e84792161ba86bf924c0b.
New module: Part5OriginalH430OccupiedSlotSlack.lean.
Source blob: eb8c6136c04be4bfe8c07a0c3497b0ae50c2b5d9.
Source diff: +181/-0 lines, one definition, seven candidate theorems.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Fixed provenance / ownership

Manuscript fixed at UyNewNas/chen-imbalanced-semiprimes,
ba6ec11d800eccc54406490631895e174de85766.
Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Original c/K, root norm 7/2, row norm 12, real alpha, signed -1/4
for BOTH U3 and U4 tags, same-Q requirements and reserve 430+11
are unchanged. No P1.4/P3.6 file or CI configuration is modified.
The direct import remains the previous source-only candidate
Part5OriginalH430FilteredQPositionCapacityDebt; it and its pinned
transitive dependencies have not been installed/compiled.

## New exact arithmetic-source invariant

The preceding packet proves, for every Q-dependent Bool position filter:

  C_slot = S_keep + E_erase,
  S_keep <= F_keep.

Here every quantity is an actual fixed-Q rank-two LIST occurrence count.
F_keep counts all surviving Fin positions; S_keep counts actual distinct
observed physical slots whose chosen Fin positions survive; E_erase
counts original observed physical slots deleted by the filter.

The new definition gives an exact **unoccupied surviving position slack**:

  U_keep = sum over observed physical Q of (F_keep(Q) - S_keep(Q)),

where each subtraction is in Nat, justified by the actual proved
per-Q injection of kept physical slots into kept Fin positions.

Seven new Lean theorem proof bodies establish the CANDIDATE equalities:

  U_keep >= 0,
  F_keep = S_keep + U_keep,
  F_keep + E_erase = C_slot + U_keep.

Together with the already-existing ORIGINAL double-tagged source identity

  Upsilon3(N) + Upsilon4(N) = C_slot + L_six(1),

the new exact accounting identity is

  Upsilon3(N) + Upsilon4(N) + U_keep
    = F_keep + E_erase + L_six(1).

Consequently the original signed Chen coefficient can be written EXACTLY as

  -(Upsilon3(N)+Upsilon4(N))/4
    = -(F_keep+E_erase+L_six(1))/4 + U_keep/4.

In particular the previous upper envelope is tight iff U_keep=0.
This is not another estimated error allowance: the slack records
the precise difference between actually surviving list positions and
observed source-occupied slots, separately at each physical Q.

At the TRUE ordinary full-prefix Rosser gate, previously proved to erase
no observed slot and preserve all actual list positions, the candidate
specialization is

  C_frontier = C_slot + U_full.

This shows exactly which FULL frontier positions were not needed to
represent even one observed physical (Q,p,ell) slot. A post-filter
that simply discards occupied slots cannot reduce the TOTAL
F_keep+E_erase payment; it transfers source obligation to E_erase.
An effective original count-owner replacement must prove the actual
historical selected/inherited interpretation, not assume that U_keep
may be credited as already paid.

## Exact declarations

Definition:
- actualUnusedKeptQPositionSlack

Candidate theorems:
1. actual_unused_kept_q_position_slack_nonneg
2. actual_filtered_q_capacity_eq_kept_plus_unused
3. actual_filtered_capacity_with_erasure_exact
4. original_tagged_source_plus_unused_exact
5. original_signed_quarter_with_unused_exact
6. actual_filtered_bound_tight_iff_no_unused
7. actual_full_prefix_frontier_eq_slots_plus_unused

The proofs use only existing internal cardinal identities, existing
original U3/U4 source identities, Finset.sum, Nat subtraction/casts,
and exact real linear arithmetic. NO new external number-theory input,
custom axiom, sorry/admit or target-equivalent hypothesis is introduced.

## Validation — strictly limited

The actual GitHub source diff and fetched blob were read back against
the source commit: one NEW module, +181/-0 lines, blob
eb8c6136c04be4bfe8c07a0c3497b0ae50c2b5d9.
The static text scan found no sorry/admit/axiom/unsafe.

In this run's container, git ls-remote could not resolve github.com,
and lean, lake, elan were not installed. The pinned source-only
transitive import closure was not staged. No actual Lean parsing,
elaboration, local module compilation, kernel replay, transitive axiom
audit, finite-table replay or new CI validation was performed.
All declarations are CANDIDATE_UNCOMPILED; zero green credit.
Hash readback and static scanning are NOT Lean verification.

## Remaining manuscript-INTERNAL obligations

1. Bind true frozen full/selected/inherited Q-dependent count-owner
   predicates and prove they are causal along the actual request tree.
   This packet's arbitrary Bool filter is NOT that identification.
2. Derive the original 7/2 weighted selected root capacity, genuine
   tagged q owner and multiplicity; retain both U4 overlap labels.
3. Pay erased original slot debt, six literal q/tag collision/rejection
   lanes and correct signed first-excluded Euler suffix. The new
   positive slack is NOT a bound on those charges.
4. Close physical next-table residual, q multiplicity, selected row
   error, predecessor CLOSED-CELL and base/switched/seed/floor.
5. Manuscript-local PP/same-rho, native-history quality control,
   outer integral–Theta–count identity and common causal 430+11 nesting.
6. Stage frozen imports and incrementally compile, kernel-replay,
   audit transitive axioms and replay finite certificates.

NEXT: use the original tagged-source/selected-gate definitions to
identify a genuinely causal owner (rather than choosing a filter to
optimize capacity), then bound the resulting erased arithmetic debts
and six lanes. Do not treat a tightened inequality as a closed theorem.

**Complete h34 manuscript-internal proof remains OPEN.**
