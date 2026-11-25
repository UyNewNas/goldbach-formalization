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

The initial native-context preflight (`face0a20e6874991a93f7c9266cc443e`)
reported a Lean memory exception while loading/elaborating
`ImbalancedChen.RosserEndpointBridge` with `-M5800`. The verification driver
therefore uses one worker and at least 11264 MiB for closures requiring the
qualified native environment. Non-native settings are unchanged; the
explicit `--external-memory-mb 0` option preserves the caller's requested
worker and heap settings. Actual Lean commands remain in the receipts, and
all source/dependency checks and strict proof flags remain unchanged. This
resource adjustment is not evidence that the failed module has passed.

## Q96 source preparation

The original Q96/ownership chain is now selected from thirteen existing
P1 source files, including the already repaired `SimplexMoments` and
`SourceMeasure`. Six unchanged affine-geometry declarations have been
moved from `P2OriginalSaving19OwnedSource` to
`P2OriginalAffineSimplexGeometry`, retaining their original namespace,
types and complete proof bodies. The old owner imports the new module;
saving16's pulling-ownership module changes only that import. The
`OwnedIntegral` source closure is reduced from 361 to 357 modules and no
longer reads the unrelated 26 M19 numerical inputs. The original fourteen
saving16 witnesses, 39741 simplices and exact Q96 endpoint are unchanged.

P1's live copies of all fourteen witnesses have the exact registered sizes
and SHA256 hashes. This authenticates the inputs; it does not evaluate
the Lean finite checks. Current Q96 elaboration and kernel acceptance are
still pending. The original 355-module integral-identity source graph is
unchanged by this preparation.

The production import scanner previously misread a double quote in a
Lean `Char` literal in the existing pure JSON reader. Its fix has five
passing regression cases, including the actual reader. The old/new
scanners return identical import graphs for the existing 355 modules,
and the fixed production runner now scans all 357 Q96 modules normally.

Additional evidence:

- `P1_CACHE_AND_INPUT_INVENTORY.json`: live read-only cache/input census;
  object existence is distinguished from historical kernel acceptance.
- `Q96_EXISTING_INPUTS_AND_SOURCES.json`: original input and source reuse.
- `Q96_EXACT_SOURCE_INSTALLATION.json`: thirteen exact source preimages.
- `AFFINE_SIMPLEX_DECLARATION_IDENTITY.json`: six byte-identical declarations
  and the two precise owner/import changes.
- `Q96_LIGHT_SOURCE_CLOSURE.json`: complete 357-module source graph.
- `IMPORT_SCANNER_REGRESSION.json`: observed failing and passing checks.
- `ACCEPTANCE_SCOPE.md`: actual P2.5 responsibilities and the cross-P3
  distribution boundary, without promoting a target definition to a theorem.
