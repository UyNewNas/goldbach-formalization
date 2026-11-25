# P2.5 saving16 continuation — 2026-11-25

Status at source checkpoint: **SOURCE SELECTED; current P2 closure not compiled or kernel accepted. Full P2.5 remains open.**

This continuation uses the 2026-11-06 manuscript, the current P2 branch at
`a929011ec95843553fc2e10b7291c8077e0952c0`, the original full87 manifest, and
existing P1 repairs at `298670f119d24874b719facb3ef756f1e01223a1`.

The new `P2Saving16Full87IntegralIdentity` identifies the whole original
saving16 integral with exactly its fourteen original full87 summands. It also
partitions the full87 sum into that contribution and the unchanged complement
of 73 source integrals. IDs 0 through 14 except 7, all 96 affine rows per cell,
the original factor-four kernel, the two residual denominators and the eight
coordinate factors are preserved. No quantitative PP, Q96 lower bound, or
complete P2.5 acceptance is inferred from this identity.

The original `P2OriginalSaving16CellOwnership` and
`P2OriginalSaving16Full87SourceBinding` are reused. Thirty original archived
logical modules are restored; existing P1 proof repairs are reused where
available. Six restored original owners import their already accepted
definition cores and remove exactly 34 byte-identical declarations. This is
the previously published owner movement, not a replacement of the original
sources, cells, caps or integrals.

Evidence:

- `SOURCE_SELECTION.json`: original minimal source-selection analysis.
- `P1_SOURCE_REUSE.json`: the eleven existing P1 repaired sources reused.
- `OWNER_MOVEMENT.json`: exact declaration identity and before/after hashes.
- `CURRENT_SOURCE_CLOSURE.json`: the complete current source/import graph.

Independent static mathematical review found no changed kernel, hidden
premise, double-counted saving or lost complement. This review is not Lean
compilation or kernel evidence. Current strict compilation, independent
replay and owned-declaration auditing will be recorded separately.
