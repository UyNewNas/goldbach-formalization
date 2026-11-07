# P5.6 / h34 — original generated child-frontier transport

Date: 2026-11-05.
Parent HEAD: `42859b2163b210f2a6f2e22108a30b89d148c657`.
Target branch: `chatgpt/p5-h34-request-admission-20261105`.
Status: **PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED**.
**Complete h34 manuscript-internal proof remains OPEN.**

## Why this packet

The prior signed-step packet establishes a bound on the actual selected
`generationValue` versus its bank/Buchstab ideal profile. It had not
exhibited the corresponding successor occurrences in the existing
`rootHistory` and had not transported the exact path-product weights
to their child table terms. This is required before any honest
source-count-to-request identification. It does not itself establish
an arithmetic prime/PP count identity.

## New Lean source

`Part5OriginalH430RequestedFrontierTransport.lean` is additive and
depends on the previous `RequestedSignedStep` package.

1. `extend` appends the actually selected edge to an existing
   occurrence path, updates to its literal `nextRequest`, and
   decrements the remaining generation. The proof `mark_extend`
   establishes `mark (extend o e) = mark o * edgeWeight e`
   by the original list product. It neither drops duplicate edge
   occurrences nor changes any of the retained, Buchstab, W1/W2
   coefficients. `extend_prepend` and `extend_origin` ensure
   the path orientation agrees with the historical tree constructor.

2. `history_extend_mem` is an induction on the original recursive
   `history`. For a parent already in that history with remaining
   generation `g+1`, it proves that EACH edge belonging to the
   literal selected `children N Q g` generates another occurrence
   in that SAME history. `actual_level_extend_mem` instantiates
   the statement at the original level-list `Index`, proving the
   child generation really is `g` and its exact mark is the
   parent mark times the original edge weight.
   `actual_child_mem_next_level` places that child in the
   actual next `levelRequests` list (forward support inclusion);
   `actual_child_sameQ_word` obtains the original frozen root Q
   and ordered integer-word identity for each child.
   There is no assertion that equal products/cells can be deduplicated.

3. `childTableMass` is a finite sum over each selected CHILD EDGE.
   `childTableMass_eq_mark_edgeValue` unfolds the original
   `edgeValue` and transports the real path mark through the
   literal edge list. `nextLevelMass` sums this over the actual
   parent-level `Index`, and
   `generationValue_eq_nextLevelMass` proves exact equality with
   the previously defined one-step generation value. No closed
   integer count, prime count or analytic density is introduced.

## Boundary

The important remaining bridge is the **reverse multiset/list-position
coverage** for the actual next-level occurrences, followed by their
correct identification with the COMPLETE original U3/U4 selected-count
source, including original root weights, full/selected/inherited
filters, rejection lanes, owner multiplicities and count signs.
The current inclusion does NOT imply that coverage, and the table's
`requestValue` is NOT declared equal to the original arithmetic
prime/PP count.

Original ordinary/fixed/switched base, integer floor, true seed,
manuscript-local same-rho PP instances, native-history masses,
outer Theta/count normalization and the single common 430+11 nested
refinement remain manuscript-internal obligations.
External PNT/Mertens/BV or stronger distributions remain recorded
only; no theorem of that kind is implemented here.

This packet does not touch production imports, the default branch,
P1.4, P3.6, original constants, tools, pinned dependencies or CI.

## Verification

Only static-source review, namespace/declaration inspection,
balanced-delimiter inspection and remote Git blob/commit readback
are available. No Lean/Lake executable, elaboration, kernel replay,
axiom audit, numerical430 replay or CI dispatch was executed. The
entire new module and the inherited held source files remain
**UNEVALUATED** as Lean proofs, not green nodes. This additive package
must be installed AFTER `RequestedSignedStep` in the previously
recorded order.

Next target: prove the reverse child-frontier multiplicity identity
against the real next `levelRequests` list, then use genuine
arithmetic source predicates and signs to begin the closed-cell
count bridge, WITHOUT assuming it as an input.
