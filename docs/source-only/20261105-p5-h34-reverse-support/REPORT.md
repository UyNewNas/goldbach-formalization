# P5.6 / h34 — reverse generated-frontier support

2026-11-05. Parent: `d7639e1ea08cc1d14ba324bbd352d1c650de090c`.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT**.
The complete manuscript-internal h34 remains **OPEN**.

## New candidate proof body

Add `Part5OriginalH430RequestedReverseSupport.lean`, following the earlier
`Part5OriginalH430RequestedFrontierTransport` source.

The parent commit proved that every genuine selected child from an indexed
generation-(g+1) parent occurs in the generation-g list. This packet proves
the converse **on support**, using the original recursive `history`:

1. `history_top_is_origin`: `history_facts` gives the exact path-length
   relation. A node at its starting generation has empty path, unchanged
   request and is the literal `origin`, not a catalog/product surrogate.
2. `history_reverse_child`: induction on the original recursive history.
   Each nonroot member of remaining generation g admits a parent at g+1
   and its final edge belongs to the original `children N Q g` list.
   The immediate-child case uses the root constructor and
   `extend_origin`; the deeper case transports the induction witness
   through `prepend` and `extend_prepend`.
3. `nextLevel_reverse_support`: specializes the induction to the actual
   frozen U3/U4 `rootHistory` and genuine filtered `levelRequests`
   at g and g+1 for `g : Fin 430`.
4. `nextLevel_support_iff`: combines reverse support with the previously
   established `history_extend_mem` to characterize generated successors
   by the same root Q and actual winner's child list.
5. `indexed_nextLevel_reverse_support`: specializes reverse support to
   an actual successor LIST POSITION, retaining the original occurrence
   instead of replacing it by a deduplicated integer catalog label.

### Exact scope of the mathematical result

This is a membership/support equivalence. It is **not** a proof that
the list of all child occurrences is positionwise or multiset equal to the
next-level list, nor a bijection between (parent position, edge position)
and next-level positions. That stronger multiplicity identity is the
specific next target. No count-source, root-weight, floor or analytic
license is smuggled into a hypothesis.

This packet deliberately does **not** introduce a synthetic count model,
change the selected scalar/specified-cell choice rule, quotient products,
change coefficients, or merge different roots/generations. Original
c/K, norm 7/2, row norm 12 and 430+11 reserve are unchanged.

## Open manuscript-internal work

1. **Exact positional/multiset frontier equality** and reindexing of sums
   preserving duplicate paths and selected-edge weights. Current support
   iff does not imply a multiplicity identity.
2. Original U3/U4 complete arithmetic selected-count source and root
   weights, owner multiplicity, full/selected/inherited filters and
   rejection lanes; prove the closed-cell count induction with correct
   signed count directions.
3. Ordinary/fixed/switched base, true seed, integer floors/rounding and
   same-rho/PP realization; genuine feedback integral and outer Theta/count.
4. Native-history proper/equality/inherit mass, and ONE nested causal
   430+11 refinement in the original reserve order.
5. Install candidate sources, compile, kernel replay and audit exact
   transitive axioms under P0 resource control.

The genuinely external analysis inputs are carried forward and recorded
only; no external prime-distribution theorem is implemented.

## Verification and checkpoint

The single new Lean module has five declared proof bodies. The source
was checked for prohibited placeholder tokens and for consistent names
against the remotely read prior source; remote SHA/commit readback is
required after publication. This is **NOT** Lean parsing, elaboration,
compilation, replay, theorem verification, or independent review.
No Lean/Lake or CI was launched. All new and inherited held-source
proof bodies remain **UNEVALUATED**, and no node is promoted to green.

Next: prove the exact child-list/parent-level position bijection or
multiset identity. Only after that, connect the actual original
U3/U4 arithmetic count predicates and signed base/floor/seed charges.
