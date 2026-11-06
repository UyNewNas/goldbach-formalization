# P5.6 → h34 — real unsifted quotient source and two distinct rejection lanes

Date: 2026-11-06 UTC. Parent commit: `9f225c156e3f58f97ed879f8ff826b3e87a1b134`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Scope: manuscript-internal, source-only. **PARTIAL_SOURCE_INCREMENT / UNCOMPILED / ZERO FORMAL CREDIT.**
Complete h34 manuscript-internal proof is still **OPEN**.

## Mathematical correction and this packet

The repository's literal `chenQuotientPrimeSource N p` ranges over **positive natural quotient receivers q**, not necessarily prime q. The factor may be 1 or composite (including squareful). The phrase “receiver prime q” in older handoffs was imprecise. The literal original source is the strict roughness filter `chenSiftedQuotientPrimeSource` over that quotient source; this packet does not alter it.

New source: `Part5OriginalH430TaggedSourceRejections.lean` (268 lines, 19 source theorem bodies including three private lemmas, four definitions).

1. `rawPairs` and `rawTagged` construct the **actual full unsifted quotient-receiver carrier** for both original U3/U4 selected prime bands. Each tagged occurrence retains its band tag, original p and individual quotient q. The original overlapping p bands still count twice.
2. `frozen_receiver_mem_raw`, `frozen_pairs_subset_raw`, `frozen_tagged_subset_raw` and `raw_quotient_data` connect literal frozen strict-roughness membership to the real quotient source and prove positive, bounded, centre-coprime quotient data. They do **not** assume q prime.
3. `rejected_original_U3_iff`, `rejected_original_U4_iff`, `rejected_frozen_U3_iff`, `rejected_frozen_U4_iff` separately identify the exact original-cutoff and frozen-cutoff rejection filters on each real (tag,p,q) fibre.
4. `rejected_frozen_card_by_fibres` counts all q rejected even after freezing (not the already-recorded frozenOnly additions). `rejected_original_partition` and `rejected_original_card_split` account for each original rejection once, partitioning it into newly admitted `frozenOnly` and still rejected `rejectedFrozen`.
5. `raw_original_partition`, `raw_tagged_card_three_lanes` and `raw_U34_plus_two_rejections` give the proposed literal **full source = original U3+U4 + frozen-only + still rejected** three-lane finite identity. All original strict cutoffs, multiplicities and tags remain unchanged.

These theorems are manuscript-internal proof *candidates*. No closed-cell count inequality, real feedback owner or selected/full/inherited historical filter equivalence has been assumed. The saved arithmetic roughness decomposition is not a claim that a quotient q corresponds to a unique request occurrence or that a feedback root's mark equals its count.

## Precise remaining obligations

- Bind each real (tag,p,q) source receiver, including its ORIGINAL prime label P behind q, to the actual manuscript full/selected/inherited **history owner**, preserving root weights, multiplicity and exclusion/retention decisions.
- Pay the `frozenOnly` excess and the separate `rejectedFrozen` channel in the correct count-versus-feedback direction; construct the all-action closed-cell arithmetic count induction without a target-equivalent assumption.
- Supply original base/fixed/switched/seed and integer floor/rounding payments, manuscript-local same-rho/PP instances, actual feedback integrals and outer Theta–count normalization.
- Prove native-history proper/equality/inherited mass and the **one common 430+11 nested causal refinement**, retaining c/K, root norm 7/2, row norm 12 and true alpha.

P1.4, P3.6, original modules, manuscript pin, toolchain, dependencies and CI were not modified.

## Verification

Only source text / scope / no-placeholder inspection and Git object readback are planned. **Lean parser/elaborator, kernel replay, transitive axiom audit, numerical430 and finite certification are UNEVALUATED.** No compilation or CI dispatched. Not a green status.

Next action: locate and instantiate the *actual* original owner/selection/rejection predicate on these explicit (tag,p,q) fibres, instead of inventing a new abstract count licence or repeating another unweighted finite-set partition.
