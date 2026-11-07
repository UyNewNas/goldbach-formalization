# P5.6 → h34 — actual fixed-Q Fin-position history mass and complete U3/U4 unpaid signed source

Date: 2026-11-07.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Predecessor HEAD: `9c787465dceca93cdf6ccaff2b3d14f5c83df4bd`.
New Lean source commit: `6f7131977012608896ae3f88fe4ee72f7b14b695`.
New source: `Part5OriginalH430ActualPositionMassGap.lean`, 248 lines.
Verified new source Git blob: `976d270a43dabc2679771957771008318833760c`.

Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Toolchain unchanged: Lean `v4.33.0-rc1`, Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.**

## Why this increment is not the preceding interface again

Previous `TruePositionReceiptLedger` reindexed the **retained** original q/tag
representative arithmetic weight onto genuine fixed-Q rank-two `Fin` list
positions; it did NOT connect the source to the *mass of the particular
list state* at that chosen index, nor include all original root/second-stage
rejections in one such position formula.

This packet fills those two narrower source-to-history accounting gaps:

1. `observed_fixed_q_position_true_sign_mass` uses the literal
   `firstExitDepthFrontier 2` invariant at the chosen actual `Fin` index,
   plus the proved `[ell,p]` prefix, to recover its **positive** even-depth
   sign and the true multiplicative history mass
   `(1/(ell-1))*(1/(p-1))`. This is not a fictional second-stage weight
   per original integer quotient q.
2. `observedRankTwoMassAtPosition` and
   `observed_rank_two_mass_by_distinct_slots` reindex the actual
   rank-two LIST state masses by distinct observed physical `(Q,p,ell)`
   slots, separately for every genuine physical Q. There is no
   unproved global common-Q count and no duplicated mass for q/tag
   receivers sharing a physical slot.
3. `originalSixUnpaidReceiptLanes` preserves six EXACT, signed,
   q-dependent sources: (i) cross-tag collisions of tagged keys at one
   physical slot, (ii) further q receivers of a tagged key,
   (iii) a geometrically eligible q factor rejected by the true second
   Rosser policy, (iv) no eligible q factor, (v) physical root cutoff,
   and (vi) root policy rejection.
4. `complete_original_source_at_actual_positions` composes the
   previously established true five-lane original arithmetic source
   with the fixed-Q actual-position q/tag ledger. Its left side is
   **all** original U3/U4 tagged q receipts, not just retained second
   candidates, and its right side retains every unpaid lane.
5. `originalRankTwoPositionMassGap`,
   `per_q_original_receipt_vs_history_mass`, and
   `complete_original_source_true_mass_and_all_debts` split the full
   signed original source into (a) actual observed rank-two history
   mass at genuine positions, (b) an explicit source-weight-minus-
   history-mass gap on those positions, and (c) the six source
   collision/rejection lanes. No sign bound or payment equality is
   smuggled into the gap.

These are manuscript-internal **candidate Lean proofs** in a source-only
staging packet. The exact finite accounting is not the full
`full/selected/inherited` stage filter and has NOT established actual
signed Euler first-excluded payment: a positive retained rank-two state
is *not* itself the rejected event carrying the full Euler suffix.
History mass and q-dependent arithmetic source weight are kept distinct.
Even-rank sign alone does not give a directional signed payment.

## Precise remaining manuscript-internal obligations

- Bind actual full/selected/inherited count filters, physical z0 and
  lower/upper phase at the literal selected source receipts and real
  `Fin` positions. Ordinary full-prefix Rosser retention is strictly
  weaker. Determine which positions survive and which must remain unpaid.
- Connect original U3/U4 count/root weights and every original q/tag
  appearance to a genuine unique historical owner, including repeated
  q, cross-tag slots and mismatch debt. Establish the **directional**
  signed Euler event including its remaining product; do not treat a
  retained mass as a first-excluded signed correction.
- Pay actual cutoff/second-policy/no-factor/non-event rejection terms
  using valid manuscript-internal bounds, not dropped counts.
- Complete request-level Buchstab/retention consumption and all-action
  CLOSED-CELL induction, feedback/floor integrals, ordinary/fixed/
  switched bases and seed, manuscript-local PP/same-rho.
- Connect native-history masses, outer integrals, Theta and counts, and
  construct one shared causal 430+11 nested refinement in the prescribed
  reserve order.
- Stage/install and compile the chain; perform kernel replay, full
  transitive-axiom audit and inherited finite numerical430 replay.

Genuine outside PNT/Mertens/BV/Mathlib inputs are unchanged and not
reproved. The internal PP/same-rho/count/cell obligations are NOT
reclassified as external. Original c/K, root norm 7/2, row norm 12,
true alpha, frozen same-Q per root, count occurrences and 430+11
refinement budget are unchanged.

## Engineering verification

GitHub remote source readback checked the new blob
`976d270a43dabc2679771957771008318833760c`.
The source commit is a fast-forward of
`9c787465dceca93cdf6ccaff2b3d14f5c83df4bd`;
the actual compare returned **one added Lean file, 248 additions,
zero deletions**. A text-only forbidden-token and raw delimiter
count check passed before staging. Those checks are NOT Lean parsing,
elaboration, compilation, kernel replay or independent theorem review.

No Lean/Lake was run; NO CI was dispatched; NO compilation, kernel
replay, transitive-axiom audit or numerical430 certification occurred.
Every newly added proof and inherited finite guard remains UNEVALUATED.
No green node or genuine h34 theorem closure is claimed. P1.4, P3.6,
production modules, CI, toolchain and fixed manuscript were untouched.

## Next concrete action

Use the **true** selected/inherited count predicates and real phase
parameters to filter these indexed source positions, then connect the
kept position's arithmetic-minus-mass signed gap to a genuine
first-excluded Euler owner with its correct direction. The six
unpaid q/tag/second-policy/root rejection lanes MUST remain
separate until a real argument pays each of them.
