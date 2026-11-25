# Exact complete cell00 original-reader result

**Both active modules passed strict compilation, independent `leanchecker`
replay, and the complete owned-declaration audit.** This package proves the
entire original cell00 JSON value and exact trailing CRLF. It does not prove
typed decoding, the other thirteen cells, finite arithmetic, Q96, or P2.5.

The initial package name records a proposed segmented-parser fallback. A new
reader-only diagnostic isolated the observed large allocation to the combined
reader/decoder computation. The complete original reader's value could then be
certified directly within 4 GiB, making the recursive fallback unnecessary.
The fallback remains isolated, inactive, ungenerated, and uncompiled.

## Active interfaces

Namespace: `ImbalancedChen.P2Saving16Cell00Segments`.

```lean
def rootValue : P2OriginalSaving19Archive.SourceJson

theorem cell00_value371 :
    SourceJson.value 371 P2Saving16StringCharBinding00.chars00 =
      .ok (rootValue, ['\r', '\n'])

theorem chars00_length :
    P2Saving16StringCharBinding00.chars00.length = 53305

theorem cell00_value :
    SourceJson.value 53306 P2Saving16StringCharBinding00.chars00 =
      .ok (rootValue, ['\r', '\n'])
```

`P2Saving16Cell00DirectParse` owns `rootValue` and `cell00_value371`.
`P2Saving16Cell00SegmentedParse` imports that accepted owner unchanged and owns
only the length theorem and original-fuel result. The latter applies the
separately verified `SourceJson.value_success_of_le`; it does not re-run the
complete parser or assert that a smaller fuel is the original definition.

The complete JSON payload contains all seventeen original top-level fields,
every nested value in original order, and the original trailing CRLF. Its
expected AST is candidate data quoted using the preserved donor's `lean_node`.
The equality with the actual imported character input is proved by Lean's
ordinary kernel conversion. The reflexivity tactic constructs the term with
its preliminary Meta check disabled; normal kernel checking, strict trust
level zero, independent replay and complete owned auditing remain enabled.

The character owner is the already accepted original raw cell00 owner. Binding
that input to canonical `originalText (0 : Fin 14)` is a separate accepted
supplier. The final canonical parse/decode consumer is outside this package.

## Exact input and reuse

Input: `eighth-prefix-family-20261009-cell-00.witness.json`, 53,305 ASCII bytes,
SHA-256 `360a9ef6bbe76fe38fc8146a16e821f43ade93e9e41911bc3a2dfd8b49067ee6`.
The root JSON object ends at offset 53,303; two original CRLF characters remain.

The preserved donor is:

```text
commit bd7185d2cb1319b58084dcbfa228a22fc4d7d8c3
docs/verification/20261125-p26/archive-segment-generator/generate.py
SHA256 3114c68369ad3a6e3f7e3171aedadb40830917cf1592cc09e99932afdf71703d
```

`generate_direct.py` executes only these unchanged donor definitions:
`Node`, `Field`, `RawPlanner`, `quote_char`, `quote_list`, and `lean_node`.
It checks the raw input and donor hashes, quotes the full candidate value, and
requires byte identity if the generated source already exists. The donor's
top-level script and remote paths are never executed. Its candidate sufficient
fuel is 371; only the actual original-reader equality certifies that choice.

The active project closure has five modules: the unchanged `SourceJson`,
the accepted generic `SourceJsonFuel` companion, the accepted raw cell00
String/Char owner, the direct value certificate, and the thin fuel wrapper.
No Mathlib import is needed for this parser-only closure.

## Observed verification

All stages were serialized. Each process retained a 180-second limit and an
external 4 GiB RSS limit. Normal/audit flags included `-t0 -j1 -M4096`,
`warningAsError=true`, `maxRecDepth=50000`, and `maxHeartbeats=40000000`.
Both source files retain local `maxRecDepth=1000000`, `Elab.async=false`, and
`stderrAsMessages=false`; these local options are explicit in the sources.

| Module / stage | Exit | Seconds | Peak sampled RSS bytes |
| --- | ---: | ---: | ---: |
| DirectParse strict | 0 | 19.944 | 2774302720 |
| DirectParse replay | 0 | 11.648 | 2227171328 |
| DirectParse complete owned audit | 0 | 2.089 | 1640857600 |
| SegmentedParse strict | 0 | 7.696 | 2230693888 |
| SegmentedParse replay | 0 | 3.414 | 1868017664 |
| SegmentedParse complete owned audit | 0 | 2.209 | 1640939520 |

The direct owner has exactly two serialized/environment-owned declarations;
the thin wrapper has exactly two. All are safe, total, and nonaxiom. Direct
`rootValue` and `chars00_length` have empty axiom sets; `cell00_value371` uses
only `propext`; `cell00_value` uses only `propext` and `Quot.sound`.

The exact unchanged production audit template was instantiated solely by
replacing its target module name. It compares complete serialized and
environment inventories and audits every owned declaration, without exclusions.
Source/object hashes, commands, dependency snapshots, full audit inputs and
logs are retained in `RESULT.json` and `verification/`.

The accepted source/object identities are:

| Module | Source SHA-256 | Object SHA-256 |
| --- | --- | --- |
| `P2Saving16Cell00DirectParse` | `fa1c92a5fd127b913958a6a10373e8a041433ac74a4a8c36ab06da709356956c` | `52cf731b62270e0fdfee8468d813aacfe373853e51035b88c669dd8713393f2a` |
| `P2Saving16Cell00SegmentedParse` | `a08f64469fc99999bfdec271b700cd9b566dbc897eaf2a4dc6ee1f95ea88e680` | `a24cfc8ab4abd43bfb422e6d0b40dc19a43315eba90a96101523150a44715106` |

## Inactive fallback boundary

`inactive-fallback/generate.py` and its continuation helper are unfinished
source-only preparation for recursive symbolic-fuel certificates. They have
not been run or compiled and are outside the active import closure. No claim
is made about the fallback's correctness or performance. It writes only into
its isolated directory and cannot overwrite the accepted active owners.

No production source, parser, decoder, finite guard, source map, git index,
commit, or remote branch was changed by this package. No cloud job was submitted.
