# Saving19 Archive cell-00 parsing diagnostic candidate

## Scope and status

This candidate extracts the original loader/text/parser prefix of
`P2OriginalSaving19Archive` and adds exactly two closed cell-00 proof goals.
It is **uncompiled diagnostic source**, with no claim that the complete Archive,
cell shapes, row shapes, geometry, moments, Q96 binding, or other cells have passed.
No remote compilation, parser execution, loader execution, or data rewrite was
performed while creating this candidate. The production Archive was not changed.

## Files

- `ImbalancedChen/P2OriginalSaving19ArchiveCore.lean`: the original prefix through
  `geometry` and `moments`, with the original namespace and definition bodies.
- `ImbalancedChen/P2OriginalSaving19ArchiveParse00.lean`: imports only Core and
  defines `geometry_parse_00` and `moment_parse_00`, each with `by decide`.
- `candidate.patch`: two additive files only; no production-file mutation.
- `SOURCE_MANIFEST.json`: exact source commit/path/hash and slice provenance.
- `STATIC_AUDIT.json`: checks actually performed and diagnostics not performed.
- `build_candidate.py`: deterministic extraction from the specified P1 snapshot;
  it never invokes Lean or a remote service.

## Exact source slice

Source commit: `298670f119d24874b719facb3ef756f1e01223a1`.
Source path: `/workspace/p26-p1-reference/ImbalancedChen/P2OriginalSaving19Archive.lean`.
Source Git blob: `45220db20a3d99a759f875d2c7d5f1bd72a6cdf7`.
Source SHA-256: `b8821bbc996d6fdbc19fd359b1be9dd4be181064f7fe1b2f36b8b5a27996a9b6`.

The first **8171 bytes**, source lines **1–202**, are copied
byte-for-byte. The slice ends after the complete `def moments` and its following
blank line. The next source text is the comment introducing the original general
parse-success guards, which is excluded.

Slice SHA-256: `6077aac40dadfa7f6df3770d6be457862c94e2177a69ed06e695c02faa14f406`.

Core retains exactly the original imports:

```lean
import ImbalancedChen.P2OriginalSaving19MomentFloorConsumer
import ImbalancedChen.P2OriginalSaving19SourceJson
```

The original loader elaborators, both thirteen-entry String dictionaries,
`parseInteger`, rational decoders, all record structures and decoders,
`geometryParse`, `momentParse`, `geometry`, and `moments` are unchanged.
The original namespace `ImbalancedChen.P2OriginalSaving19Archive` is preserved.
The only appended Core content is a diagnostic comment and the closing namespace.

## The two intended kernel goals

```lean
theorem geometry_parse_00 :
    geometryParse (0 : Fin 13) = .ok (geometry 0) := by decide

theorem moment_parse_00 :
    momentParse (0 : Fin 13) = .ok (moments 0) := by decide
```

There are no hypotheses. The corresponding `#print axioms` commands are included
for the later compilation transcript. No output from those commands is claimed
here. The diagnostic file sets `maxRecDepth` to the same original 1,000,000 and
adds no heartbeat override.

## Resource measurement boundary

Only the two closed parse proofs are restricted to cell 00. Core still contains
**all thirteen geometry loader calls and all thirteen moment loader calls**.
Consequently its elaboration still reads and embeds all 26 original String
literals. This preserves the requested data representation; it does not turn the
Core loader into a two-file loader.

The unchanged loaders resolve their original paths relative to the compilation
working directory, including the sibling `../goldbach-research/` directory.
Cell 00 uses the original files:

- `eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`
- `eighth-third-moment-refinement-20261009-a23-low-00.witness.json`

All other original entries must remain available for Core's unchanged loader.
The diagnostic imports Core rather than the production Archive; those two files
contain the same public definitions and must not be imported together into one
Lean environment. Integrating a permanent production split is outside this
candidate and has not been performed.
