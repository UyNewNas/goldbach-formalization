# P2.5: original Cell01 decoder certificates

This package continues `work/p2-5-saving16-20261125` from
`ed8d9c028b8656f01ca9788c4aa96ea305ed5c10`. It fills the previously absent
**Cell01 scalar, field, simplex and complete record decoder proof bodies**.
It does not repeat Cell00's accepted calculations or change the original
decoder, input witness, candidate record, geometry or numerical target.

The generated files retain their source-authoring `UNCOMPILED` markers.
Those markers are not verification receipts. Actual normal compilation,
independent kernel replay and complete declaration-audit results are recorded
separately, with exact source hashes. Only such results confer acceptance;
Python generation, this README and the source review do not.

## Exact source boundary

The existing candidate is
`../20261126-p2-5-cell01-parser-typed/ImbalancedChen/P2Saving16Cell01TypedPayload.lean`,
SHA256 `1ddf5f99c579ef2fedcf197c7b7a5f642262e905a1ad9bdec2b6f44229cc9d99`.
Its original witness remains 344,873 bytes with SHA256
`d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f`.
The original candidate and its input manifest are unchanged.

All 17 root fields, 35 vertices and 81 ordered simplex records are retained.
Every simplex keeps its ten original JSON fields, including both stored
floor fields. The raw face ledger, active-eight data and all minima are
carried through without omission or replacement.

| New owners | Scope |
| --- | --- |
| `Cell01ScalarDecodePart00` through `Part11` | 1,250 rational and 162 integer decoder equations, at most 128 per module |
| `Cell01ScalarDecode` | Imports the twelve parts; adds no declaration |
| `Cell01FieldSimp` | Three existing monad equations, 84 actual natural-number literal equations, and 1,412 scalar literal aliases, all scoped |
| `Cell01FieldBase` | Seventeen root lookups, basic field decoders, 35 vertex decoders and the ordered vertex array |
| `Cell01Simplex00Decode` through `Simplex80Decode` | Ten exact field lookups and one original `decodeSimplex` result for each row |
| `P2OriginalSaving16DecoderRecordCompose` | Public extraction of the already written symbolic Cell00 composition proof |
| `Cell01FieldDecode` | Ordered array composition and the closed equality `decodeCell rawRoot = .ok cell01Payload` |
| `Cell01PayloadBinding`, `Cell01Decoded` | Exact whole-AST equality and the original decoder at the existing parser's `rootValue` |
| `P2OriginalSaving16ArchiveCompose`, `Cell01OriginalParse` | Existing symbolic parse/bind/default-elimination transports instantiated at original index 1 |

The scalar proofs directly reference 23 existing Cell00 proofs whose parser,
original string and rational definition are identical. Other scalar equations
use the unchanged character-list representation lemmas and ordinary kernel
reflexivity. The symbolic composition supplies every premise using the concrete
field certificates. No numerical or analytic endpoint is supplied as a premise.

## Reproduction and review

Run from this package, or invoke the scripts by path:

```sh
python3 -B generate_scalar_decode.py --check
python3 -B generate_fields.py
python3 -B generate_transports.py
python3 -B test_field_package.py
```

All three generators pin their existing inputs. Existing generated outputs
must match the intended bytes; regeneration does not silently overwrite an
independent edit. The scalar writer checks the entire output set before any
write. The field tests require the exact ordered `(row index, key)` sequence,
not merely the same set of keys. Negative fixtures cover altered existing
output, reordered keys and a lookup from a different row.

`SCALAR_MANIFEST.json`, `FIELD_MANIFEST.json` and `TRANSPORT_MANIFEST.json`
bind all 102 new Lean sources. `REVIEW.json` records an independent structural
comparison of the complete original candidate AST, every one of the 810
simplex fields, all 35 vertices, all 2,496 scalar occurrences, the 23 reused
proofs and the public extraction of the four symbolic proof commands.
The review does not replace Lean execution.

## Formal scope and remaining work

The typed-record decoder chain up to `Cell01FieldDecode` depends only on the
existing decoder interfaces and the typed candidate. It can be checked without
reading an original witness file. Connecting that chain to `originalText 1`
additionally requires the existing canonical Cell01 character equality,
DirectParse, SegmentedParse and OriginalJson owners. Their absence must remain
an explicit dependency blocker; a raw-root decoder equality is not a proof
that the original text parses.

Even acceptance of every module here does **not** prove Cell01's 81 geometric
Jensen identities, independent Q96 floors, 96-row membership or pulling
ownership. It does not prove the remaining twelve cells, the all-fourteen
aggregate, the source-region integral lower bound, or the common-parameter
quantitative PP estimate. P2.5 remains unfinished until those existing
manuscript obligations and their actual verification gates are discharged.
