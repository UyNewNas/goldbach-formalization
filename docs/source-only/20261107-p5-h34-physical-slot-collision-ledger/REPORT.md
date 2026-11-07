# P5.6 → h34 — actual physical-Q rank-two slot collision ledger

Date: 2026-11-07.
Branch: \`chatgpt/p5-h34-request-admission-20261105\`.
Previous verified HEAD: \`7919973d0d949aa03345040e863840278176850f\`.
New mathematical source commit: \`379a419c29656507f2800be1fe418b6178a29797\`.
Fixed manuscript: \`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766\`,
\`paper/source/manuscript-body.tex\`, blob \`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`.
Lean / Mathlib: \`v4.33.0-rc1\` / \`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\`.

**PARTIAL_SOURCE_INCREMENT; SOURCE ONLY / UNCOMPILED / UNEVALUATED.
The complete manuscript-internal h34 is OPEN.**

## What the prior packet left open

The previous \`Part5OriginalH430TaggedRankTwoFibreCapacity\` packet separated
each retained original \`(tag,p,q)\` receipt by a selected actual prime factor
\`ell | q\`, then kept one representative for each tagged \`(tag,p,ell)\`
key and every additional original q as an unpaid residual.

That was not enough to identify even distinct historical state VALUES:
different tags at the same p and ell can have identical physical Q,
although no such equality may be assumed in general.

## Concrete new Lean source

Added \`Part5OriginalH430PhysicalSlotCollisionLedger.lean\` (323 lines,
11 candidate theorem proofs, 4 definitions, blob
\`9987d03c3b9758af09e86d9e4586ec8513494bb0\`).

1. \`physicalRankTwoSlot\` uses the ACTUAL triple
   \`(originalPhysicalQ N precision tau key, arithmeticPrime key,
   arithmeticQuotientPrime key)\`, where the last coordinate of a
   *tagged rank-two key* is \`ell\`, not the original q.
   \`chosen_key_physical_source\` proves the physical Q and root p
   survive the real q-to-ell choice unchanged.
2. \`physical_slot_eq_iff\` identifies a collision with equality of all
   three coordinates, including real physical Q; it never assumes a
   common Q across different tags or roots.
3. \`equal_physical_slot_same_frontier_state\` uses the existing
   \`actual_frontier_state_determined_by_prefix\` candidate to show that
   two genuine rank-two frontier members at equal physical slots have
   equal STATE VALUES (mass, sign, prefix, remaining suffix). It does
   not prove unique list positions or a payout.
4. \`physical_slot_has_actual_source_and_frontier\` recovers a real
   original retained q receipt, prime factor and actual rank-two
   frontier witness from each observed physical slot. No fabricated
   empty-source slot is admitted.
5. \`physical_slot_weighted_partition\`,
   \`physical_slot_representatives_and_collisions\` and
   \`physical_slot_capacity_card\` partition the real tagged keys by
   physical slots, choose one tagged-key ledger representative per
   occupied slot, and keep all colliding tagged keys separately.
6. \`retained_physical_slot_capacity_card\` and
   \`retained_physical_slot_signed_ledger\` compose this **second**
   exact finite quotient with the previous q-fibre surplus, without
   losing original occurrences or arbitrary signed q/tag weights.

The new exact cardinal identity is:

\[
\#R
= \#S
+ \sum_{s\in S}\#\bigl(K_s\setminus\{k_s\}\bigr)
+ \sum_{k\in K}\#\bigl(F_k\setminus\{r_k\}\bigr).
\]

Here R denotes all retained ORIGINAL tagged q receipts, K their real
tagged (tag,p,ell) keys, S distinct physical (Q,p,ell) slot values,
K_s the complete tagged-key fibre for slot s, and F_k the complete
original q fibre for tagged key k. Each k_s and r_k is ONLY a finite
ledger representative. The corresponding signed identity retains
weights \`w(tag,p,q)\` and both collision/surplus residual sums.

**This is not a proof that \`#S\` is a paid historical mass, or a
one-to-one full/selected/inherited owner map.** The actual recursive
frontier is a LIST; uniqueness of its state VALUE cannot establish
uniqueness or distinctness of LIST OCCURRENCE POSITIONS. Nor have
different historical Q trees been added into one physical payment pool.

## Engineering validation and ownership

- Existing \`7919973\` branch head was re-read and matched before writing.
  The source was added only under the new h34 source-only directory.
- Source commit \`379a419c29656507f2800be1fe418b6178a29797\` was read back from the branch.
  The returned Git blob was \`9987d03c3b9758af09e86d9e4586ec8513494bb0\`.
- Compare \`7919973d0d949aa03345040e863840278176850f\` → \`379a419c29656507f2800be1fe418b6178a29797\` reported exactly **one added
  323-line file**, zero modifications or deletions.
- Static forbidden-placeholder scan found no \`sorry\`, \`admit\`,
  \`axiom\`, \`unsafe\`, \`native_decide\`, or \`run_tac\` token.
  These are text-only checks, **not Lean compilation**.
- No Lean/Lake executable was found in this runtime; no elaboration,
  compilation, kernel replay, transitive-axiom audit, independent
  mathematical review, finite numerical430 certification, heavy CI
  or toolchain update was performed. Finite guards remain UNEVALUATED.
- No P1.4/P3.6 files, existing source-only packets, production files,
  manuscript, CI settings or dependencies were changed. No merge and
  no forced push.

## Manuscript-internal remaining obligations and next exact action

1. **Next:** inspect the actual \`firstExitDepthFrontier 2\` LIST
   occurrence-position semantics and then map actual
   full/selected/inherited positions to the physical (Q,p,ell)
   representatives. Prove a genuine independent paid-position
   injection/capacity bound if valid; otherwise preserve its
   collision/residual lane. Do NOT count equal state values as
   distinct positions or assume cross-Q histories share a pool.
2. Match the original owner selection and actual root weights,
   physical z0, lower/upper phase and complete U3/U4 selected-count
   filters. The present chosen prime factor is a ledger picker, not
   the manuscript owner.
3. Pay/estimate q surplus, tag collisions, cutoff failures,
   Rosser failures, no-candidate and non-event rejection; retain the
   signed Euler correction's genuine orientation.
4. Prove request-level Buchstab/retention and all-action CLOSED-CELL
   induction, correct base/switched/seed/floor/feedback-integral/Theta
   consumer inequalities, manuscript PP/same-rho, native-history
   control and ONE common nested 430+11 causal refinement.
5. Stage all source-only modules, compile, kernel-replay, audit
   transitive axioms and independently verify finite certificates.
   None is complete yet.

No external analytic proof is implemented; consult
\`EXTERNAL_INPUTS.md\`. The fixed c/K, root norm 7/2, row norm 12,
real alpha, same-Q within each physical root, per-q multiplicity,
and 430+11 budget remain untouched.

**完整 h34 稿内证明仍未闭合。**
