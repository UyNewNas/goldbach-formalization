# P5.6 / h34 exact frontier — external inputs (record only)

Source parent: `2d392e5dd469c61b469cfbf24a8e0d5590c367cc`. Exact held source: `b427861a2217ad1b6567c0ee551bb8b97e55380b`.
No external analytic theorem is implemented, strengthened, or introduced
as an axiom.

## Reused finite Lean library infrastructure

The candidate uses pinned Lean4 `leanprover/lean4:v4.33.0-rc1` and the
unchanged repository Mathlib lockfile, with ordinary `List.filter`,
`List.map`, `List.flatMap`, `List.count`, `List.sum`, `Fin`,
`List.map_append`, list recursion, and the `omega` tactic. The actual
Mathlib revision and any transitive axioms are inherited from the
repository lockfile; not independently built/audited in this run.

## Reused manuscript-internal interfaces (not externalized)

`RequestedHistory.history`, `history_facts`, `origin`, `prepend`,
`rootHistory`, `rootRequest`, `rootQ`, `levelRequests`;
`RequestedBranches.children`, `nextRequest`; and
`RequestedFrontierTransport.extend`, `extend_origin`,
`extend_prepend`. These are held source modules from the existing
h34 branch and remain uncompiled. No new implementation of PNT,
Mertens, BV, or PP distribution is present.

## Still manuscript-internal and open

Generated request history versus COMPLETE original U3/U4 selected count,
root count weights, actual owner and ancestor filters, rejected lanes,
signed closed-cell counts, base/fixed/switched/seed/floor payments,
same-rho/PP consumer adaptation, native-history mass, outer Theta/count
normalization and common 430+11 causal refinement. None is shifted to
an external premise or claimed as a theorem here.

External provenance for earlier bank and strict Buchstab error suppliers
remains in the preceding EXTERNAL_INPUTS records; this list-only module
does not call those suppliers or add their charges.
