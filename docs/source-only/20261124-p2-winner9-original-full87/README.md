# Exact original Full87 definition bridge — source-only candidate

**Integration candidate with isolated verification.** The exact bridge and eleven definition cores have now passed strict private-environment compilation, independent replay, and complete owned-declaration audits. The four former owner modules still require their combined compatibility check before promotion. The frozen source banners describe the earlier preparation state; see [current verification](../../verification/20261124-p2-private/README.md) for the exact subsequent receipts.

The candidate connects the existing literal Winner9 integral to the actual
original declaration:

```lean
P2Winner9OriginalTerminal.terminal41Integral =
  P4AOriginalFull87SourcePrimeTests.cellIntegral (.remaining (.nine 11))
```

It does not introduce a replacement definition of that target. The original
`cellIntegral` declaration and its complete definition closure are moved into
small core modules with their original fully qualified names, types, and
bodies. Both original `Cell` types retain every constructor, hence all 87 source
cells. Every literal source row and every source/cap dispatch branch remains.
Only unrelated theorem dependencies are excluded from these definition cores.

## Reused sources and exactness

The pinned source baseline is
`8fdeb981e9cd29d336adb811f9558081e2ae9be8`.
Two original files were absent from that checkout and were read by their exact
GitHub blob IDs from the original source commit
`be2efd01c561080672e6c0ad0ba21638837afe4c`:

| Original module | Original Git blob |
|---|---|
| `P4AOriginalFull87StrictActionTrim` | `c815fd9a9adf51ba1e84bcf38354126084690f56` |
| `P4AOriginalFull87EighthKernelControl` | `9c463af5937bd4c15ea95239d10470de5089b380` |

Their exact bytes are retained under `reference-blobs/` with a `.lean.txt`
extension. The extractor verifies their Git blob hashes before using them.

`DEFINITION_RECEIPT.json` records all 62 extracted declarations: original
commit, path, blob, source hash, line positions, namespace, open commands,
normalized declaration hash, declaration head/type hash, and body/RHS hash.
CRLF is normalized to LF and trailing blank lines are omitted; no Lean token
in the declaration is changed. Eleven definition modules are generated.

The original integral formula is the factor-four density in
`paper/release-20261106/en/argument.tex`, `eq:current-eighth-saving`.
The bridge preserves its two residual denominators and eight coordinate
factors. The terminal's 97 tagged rows were also compared directly with
`P4AOriginalSeed7Unequal15Literal.nineRows 11`; all labels and all rational
coefficient strings match in their original order.

The six candidate bridge theorems prove the full row equality, source-set
equality, two cap identities, density identity on all ambient points, and the
actual integral identity. They do not take a source/cap/integral match as an
assumption. The row equality is definitional (`rfl`), so the previous large
bidirectional positive-multiple search from `SeedRefinements` is unnecessary.

## Reproduce the extraction

Run from the repository root:

```bash
python verification/part2/extract_winner9_original_full87_definitions.py --check
```

Omitting `--check` regenerates this source-only archive. This checks source
movement and reproducibility; it does not run Lean. The handwritten bridge
candidate is `ImbalancedChen/P2Winner9OriginalFull87Bridge.lean`.

## Single ownership of each declaration

**The original modules and their definition cores must never both declare the
same name in a loaded module graph.** Moving definitions into an additional
module without removing them from the former owners would be an invalid
integration, even if the small isolated bridge compiled.

`original-modules-refactor.patch` performs exactly the corresponding movement:
each old owner imports its core and removes the extracted declarations. It
covers all 13 original owner modules. Four of these were already active at the
pinned baseline; their complete refactored candidates are also available under
`refactored/ImbalancedChen/`:

- `OriginalDescendingFifteenLiteralAffineRows.lean`
- `OriginalAscendingThirteenLiteralAffineRows.lean`
- `P2OriginalDescendingEighthLogSemantics.lean`
- `P2OriginalThirdMinorantLogDictionary.lean`

No active file was changed when preparing this archive. Promotion must install
these four refactors together with the new cores. Before any archived original
owner is activated later, apply its matching refactor as well. For the two
previously absent original files, restore the exact reference bytes at the
receipt's original path before applying that portion of the patch.

All retained declarations in a refactored original module keep their text;
the changes consist only of the added core import and removed moved
declarations. Public constant names and bodies remain unchanged. A source
check confirms that each of the four active candidates contains no duplicate
of any moved declaration and imports its core exactly once.

The combined import check is `verification/OwnerCompatibility.lean`. It
imports the four original owners and the bridge in one environment, displays
the fully qualified integral equality, and prints its transitive axioms.
The corresponding current project import graph has 247 modules, all with
available local source. Of those, the owner movement invalidates eight
existing modules and their object signatures: the four owners, the two
`Original*CellOwnership` modules, `P4ASlot17DescendingChargedFrontier`, and
`P4ASlot19ChargedFrontier`. Reuse the other exact-source objects when available;
do not reuse old objects for these eight modules after the movement.

In an isolated verification worktree with these cores and the four owner
refactors installed, first build the five root modules above with the
signature-aware cloud runner, then use its object directory in `LEAN_PATH`
to compile the probe, for example:

```bash
lean -DwarningAsError=true -DmaxRecDepth=20000 \
  docs/source-only/20261124-p2-winner9-original-full87/verification/OwnerCompatibility.lean
```

The source-only large historical owners require their own matching patch
before any future build that imports them; this probe intentionally tests the
four already-active owners only.

## Pending acceptance

The isolated verification target is
`ImbalancedChen.P2Winner9OriginalFull87Bridge`. Its project closure consists of
the 12 candidates, existing `VariableEnvelope`, and the existing Winner9
terminal closure; it avoids the unrelated historical 803-module proof tree.

The isolated bridge and definition cores have passed strict Lean compilation,
independent kernel replay, expanded target/type inspection, and complete
transitive axiom review in the private environment. Integration still requires
checking the four active owner refactors together against their actual native
dependency objects. Even acceptance of this
identity would not establish the missing complete numerical Winner9 family,
same-rho balance supplier, or remaining original H247 endpoint comparisons.
