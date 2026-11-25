# P2 adaptive forest: isolate the tree equality before leaf traversal

Status: proof-only source candidate, awaiting actual Lean verification. No new
compilation, kernel, cache, numerical endpoint, or resource-success credit.

## Actual failure and unchanged mathematics

The earlier compact-05 diagnostic failed in
`originalAdaptiveTree_closedLeaves` with `(kernel) excessive memory consumption
detected` at Lean limit `-M6144`. The subsequent generic projection candidate
has source SHA-256
`d67cfe0873fb2273297e0601a9750a58419d19019ae3118e8b7cb8edf367431e`.
Root has now received the same kernel error for that candidate at
`P2OriginalAdaptiveForestSourceIdentity.lean:143:8` in the actual P2 checker
with `-M11264`; the reported whole-job peak was 11,996,565,504 bytes. At this
repair's inspection the local live-log copy still ended at the module's
`START`, so the current error and peak are recorded from root's returned
result, pending the complete archived log. The earlier generic projection
change therefore has no demonstrated resource success.

The frozen manuscript source is commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. Its
`certify_extended_prefix.py` has SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`;
`numerical-appendix.tex` has SHA-256
`bed33b90419c125c841e7dd4978042e8f663f41bbe5ab211caf6e701b5342232`.
The appendix's compact partition account and the already audited source
inventory are reused. A narrow reading of `initial_cells()` confirms cuts
`h, 2h, 4h, 8h, 16h, mu, rho`, x-outer/y-inner order, and lower x/y endpoints
at the current strip's z0. The first five strips each have four rectangles;
the final strip has one. Existing `initialSeeds`, `initialTree`,
`normalized_initial_boxes`, and
`closedLeaves_initialTree_eq_original_seedCells` retain that exact order.
The complete forest still includes empty portions and both closed split
faces. The producer, initial-mesh proof, and numerical endpoint were not rerun.

## Remaining conversion and minimal candidate

The existing generic `graftSubtrees_closedLeaves` theorem hides the recursive
Subtype property projection. The public theorem nevertheless still relied
on definitional equality between
`closedLeaves (originalAdaptiveTree trees hsize) compactRegion` and the same
recursor applied to the concrete `graftSubtrees initialTree ...` value.
`closedLeaves` is a tree recursor; `graftSubtrees` is a recursive,
proof-carrying constructor whose branch lengths use the well-founded
`splitCount`. This remaining outer conversion is a plausible reduction
boundary; the kernel error does not identify the internal allocation hotspot.

The candidate adds only the private reflexive equality
`originalAdaptiveTree_eq_graftSubtrees`, at type `ClosedCutTree`. The public
proof transports that opaque tree equality with
`congrFun (congrArg closedLeaves treeEquality) compactRegion`, using the named
function rather than a new concrete lambda. Its remaining explicit `calc`
steps apply the existing generic projection, initial-seed identity, and
forest-to-integer-domain identity. Thus the tree alias conversion is checked
separately, and adjacent leaf-list endpoints use matching expressions.

## Static verification and next gate

Comparison against the exact previous source, with comments masked while
retaining original source offsets, confirms that all 11 existing theorem
headers, all four complete computational definitions, and imports are
unchanged. Only one private theorem and the public proof body are added or
changed. `git diff --check` passed. No new assumption, axiom, native
computation, linter override, or resource override was introduced.

Candidate source SHA-256:
`2f1429d2e08b51a2df175e541a15b4be62772c9bd49cea77aafa9c67d5cab568`.

Root owns independent review and actual compilation. This candidate has not
been run through Lean; any reduction in memory consumption remains unverified.
