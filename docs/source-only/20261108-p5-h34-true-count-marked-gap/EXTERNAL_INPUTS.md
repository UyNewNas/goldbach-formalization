# P5.6 / h34 — genuine marked source comparison, unpaid arithmetic mismatch

Source commits: `fce6e15654f08f1901c245f5e06d908656ef8c54`, `9da130d9479a69ecb600026dcad2a15d2622600d`.
Pinned manuscript and toolchain remain as in REGISTRY.json.

## Existing source theorem, not newly postulated

- Existing internal source in `ImbalancedChen/P2EnhancedTwentyOneSourceComparison.lean`:
  `P2EnhancedTwentyOneSourceComparison.twentyOne_source_comparison`. For eta>0 and epsilon>0, a single T>=4 precedes all N>=T, Even N and all Q,D,sigma. Under Q<=N, d>0 on D, sigma>=0 on D, 1<Q/d, every prime of d >= N^eta and `N^eta <= P2EnhancedTwentyOneSameQWeighted.cutoff Q d (227/50)`, it proves
  `5 * Phi N Q D sigma (11/5) <= weightedQuotient N Q D sigma + epsilon * Theta N Q D sigma`.
  This imports the prior finite collision/bad-prime payment chain. It is *already source-only / uncompiled*, and neither it nor its transitive analytic inputs were reverified here.
  This call appears in `original_q_count_le_positive_marked_with_unpaid_gap` for `Q=rootQ N precision k tau p`; the total U3/U4 theorem consumes the resulting local inequality.
- Existing manuscript-INTERNAL `TaggedArithmeticReceivers.original_U34_eq_tagged_card` and `original_tagged_card` identify the **actual** `currentChenUpsilon3+currentChenUpsilon4` with two separate tagged q-receiver finite fibres. Called in `original_U34_le_positive_marked_budgets_with_unpaid_gap`. Their proofs and their dependencies have not been kernel replayed here.
- Mathlib finite-sum monotonicity, elementary real linear arithmetic and max ordering are reused. No custom axioms or proof escapes were created.

## What is NOT an external input

There is no proved correspondence between the literal integer originalReceiver q count and the marked-product `Phi N Q D sigma`. This packet does not identify q with the marked product d and DOES NOT bound `unpaidOriginalMarkedGap`. The manuscript's own source/owner/PP/same-rho/430+11 obligations remain internal. An unbounded algebraic positive-part gap is an explicit open account, not a new source estimate.

No new PNT/Mertens/BV or outside theorem is added; no finite certificate was evaluated. Compilation, kernel replay, and transitive axiom audit remain **UNEVALUATED**.
