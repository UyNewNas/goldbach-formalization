# Compact 05: adaptive forest proof projection

Status: source candidate only; no local or remote Lean execution by this repair.
No compilation, kernel, cache acceptance, or numerical endpoint credit is claimed.

## Actual failure and source

The P1 compact-05 diagnostic at source `f51e91aa` reported only
`(kernel) excessive memory consumption detected` for
`P2OriginalAdaptiveForestSourceIdentity.lean:134:8`, the declaration of
`originalAdaptiveTree_closedLeaves`, with Lean memory limit 6144 MB.
The log is `p1-compact-05.log`, SHA-256
`916894d7a1d84a6fde68dd230d3bca2b9c8248b19fe66f6e37c24d21f5e9ab38`.
The module's source was unchanged between that run and repair base
`24867d3abd0990b1ef80bf3fd1982d74831f7eb4`.

The pinned manuscript commit is
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
Its `certify_extended_prefix.py`, SHA-256
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`,
defines `initial_cells()` using geometric z strips, the exact mu cut,
and x-outer/y-inner traversal; `main` initialises the heap from those cells.
The existing `initialTree`, `initialSeeds`, and named source identity retain
that 21-root order, including closed faces and empty source portions.
The numerical appendix's compact partition account is unchanged.

## Diagnosis and minimal candidate

This is a proof representation/resource issue, with no identified mathematical
gap or missing hypothesis. The failing proof unfolded `originalAdaptiveTree`
and directly projected `.property` from
`graftSubtrees initialTree trees ...`. The latter is a tree-recursive,
proof-carrying `Subtype` constructor. Its recursive branches destructure further
subtypes and transport length proofs; `splitCount` itself uses `WellFounded.fix`.
The concrete projection exposes this recursive construction to kernel
conversion. The diagnostic alone does not establish which internal reduction
accounted for the memory usage.

The candidate adds one private, generic `graftSubtrees_closedLeaves` theorem.
It checks the property projection while `skeleton` remains a variable, and
provides an opaque theorem boundary before specialising to `initialTree`.
The original public theorem now composes that theorem with the existing
`closedLeaves_initialTree_eq_original_seedCells` and
`forestLeaves_eq_source_integer_domains`, using equality transitivity and
congruence. It no longer directly projects the concrete recursive proof.

All four existing computational definitions, all ten existing theorem
statements, imports, seed data, adaptive traversal, and the conditional
2,000,000-split / 2,000,021-leaf statement remain unchanged. No new assumption,
axiom, native computation, linter setting, or resource override is introduced.
This declaration does not enumerate a concrete two-million-step run.

## Verification and remaining gate

`git diff --check` passed. Static comparison against the repair base confirmed
the unchanged existing definitions, theorem statements, and imports; the only
new declaration is the private projection theorem. Root owns compilation.
Recheck the candidate at the original 6144 MB Lean limit to determine whether
this boundary removes the observed resource failure. Passing is not inferred
from the source change.

Source SHA-256 before:
`fcffe335e01873c643c7b0ebaaa532dbb3f5d9e2c197f662dc5fc39a7065197d`.
Source SHA-256 after:
`d67cfe0873fb2273297e0601a9750a58419d19019ae3118e8b7cb8edf367431e`.
