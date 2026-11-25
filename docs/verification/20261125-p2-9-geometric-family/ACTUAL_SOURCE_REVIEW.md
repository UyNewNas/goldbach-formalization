# Independent review of the actual U4 source adapter

Status: static text review only; no new compilation, replay, declaration or endpoint credit.

Reviewed source: `docs/source-only/20261125-p2-9-actual-family/ImbalancedChen/P2FiniteMarkedGamma5ActualFamily.lean`.

Reviewed SHA256: `2bbe7f58daba884bcf67d5073465edc0726ea258b92771cc1bcab3a0ca55a4ed`.

The author validated the candidate and dependency snapshots before the local executor became unavailable. The independent reviewer then inspected the complete 132-line source text. This second review did not repeat the on-disk hash check. A subsequent pure-JavaScript SHA256 check of the recovered source text matched the recorded digest before the GitHub blob was created.

## Findings

No blocking mathematical or scope defect was found in the adapter.

1. `sourceIntegerPoint` uses the original `slotEquiv.symm`, old-list coordinates, ordered fresh pair and complete canonical tail. Its real cast matches the old physical point branch by branch. There is no sorting, deduplication, product collapse, new primality filter or replacement of an empty tail.
2. The source theorem derives its rank witness internally with the existing `enhanced_position_source_rank`. The dependent Fin index follows from that witness. The local and conclusion witnesses differ only by proof terms; proof irrelevance handles this transport.
3. The whole-function equality `geometricFamily_at_rank` is instantiated with the same scale, endpoint function, cutoff, width and rank. The final step directly reuses `enhanced_position_finPhysical_source_one`; the old plateau proof is not reconstructed.
4. The Euler constant is selected before n, p, t, both split ranks, scale, active rank, Euler word and physical point. This follows from the supplier's explicit quantifiers and not from a separate Family-wise existential. Width and derivative order remain fixed before the constant.
5. The original Family is instantiated, not redefined. The selected heavy-owner postimage must still be used if that owner is later loaded. The source contains no definition or rewrite of J and no aggregation of marked arithmetic histories.
6. The explicit large-scale hypothesis is retained. The finite low-scale zero extension is not identified with the original profile at every natural scale.

## Unresolved verification and semantic boundaries

Lean elaboration, kernel replay and the complete owned-declaration audit of this adapter remain unperformed. Its old ActualRank/ActualPhysicalPlateau dependency closure has not been qualified by this increment.

The pointwise identity and common geometric Euler estimate do not supply collar mass, original integral payment, same-rho PP/VM distribution or W1/W2 directed debts. No uniform PP statement for arbitrary moving arithmetic families is inferred.

The 29 native-Wu/H247 endpoint conditions belong to the existing native Binder compatibility route. Their necessity for the manuscript's actual enhanced finite-family route has not been established; see `MANUSCRIPT_SEMANTIC_BOUNDARY.md`.
