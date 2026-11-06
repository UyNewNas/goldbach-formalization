# P5.6 h34 genuine external dependencies — pinned and not reproved

Parent: `9f225c156e3f58f97ed879f8ff826b3e87a1b134`; manuscript map remains `docs/CURRENT_MANUSCRIPT_MAP.md`, pinned at source commit `ba6ec11d800eccc54406490631895e174de85766` with body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. No automatic switch of manuscript edition or constants.

No new external analytic input is needed in this packet. We reuse the repository's existing Mathlib finite-set sigma/disjoint-union/difference identities, card and natural-to-real casts, and elementary `omega` for exact finite cardinality equalities, at the existing `lake-manifest.json` lockfile. Invocations are in `Part5OriginalH430TaggedSourceRejections.lean`: `Finset.mem_sigma`, `Finset.mem_filter`, `Finset.card_disjSum`, `Finset.card_sigma`, `Finset.card_union_of_disjoint`, `exact_mod_cast`, `omega`.

The existing **manuscript-local** source interfaces, not additional external results, are:
- `ImbalancedChen.chenQuotientPrimeSource_data`: membership of q in the literal unsifted quotient source implies `0 < q ∧ q ≤ N ∧ Nat.Coprime q N`, called by `raw_quotient_data`.
- `Part5OriginalH430TaggedArithmeticReceivers.original_tagged_subset_frozen`, including its `N≥2`, `0≤tau≤1/12`, `1/(n+1)≤11/384` premises, called by `original_tagged_subset_raw`, `rejected_original_partition`.
- `Part5OriginalH430TaggedArithmeticReceivers.original_U34_eq_tagged_card`, called by `raw_U34_plus_two_rejections`.
- The frozen receiver's *literal* `chenSiftedQuotientPrimeSource` filter (original q may be 1 or composite), unfolded in `frozen_receiver_mem_raw`.

PNT, Mertens, BV and other genuinely external analytic proofs remain outside the implementation scope. **Actual manuscript owner/filter matching, same-rho/PP consumption and common causal refinement are internal obligations, not renamed external inputs.** External proofs are neither added nor checked here. No new axiom.
