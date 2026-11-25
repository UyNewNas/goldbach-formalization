# Actual geometry00 character-input diagnostics

## Current outcome

The new exact-character data owner passes normal compilation. Its closed
195134-character length guard passes normal and independent leanchecker.
The first actual `dimension` field now also has normal and independent kernel
proofs, including a closed transition equation on the complete original input.

Whole pure-parser success is still unproved. After an import-layout repair,
its first guard exceeded 4 GiB; an independently recorded proof-only variant
substituted the already proved length, reached a flushed post-rewrite marker,
and also exceeded 4 GiB. No whole-parser independent replay was attempted.

| Stage | Result | Seconds | Peak RSS (bytes) |
|---|---|---:|---:|
| data / normal | succeeded | 7.043164 | 1842888704 |
| length / normal | succeeded | 10.669812 | 3347017728 |
| length / kernel | succeeded | 12.508183 | 3121446912 |
| parse / normal | failed | 0.448925 | 533975040 |
| parse / normal / fixed imports | memory_limit | 15.910745 | 4298690560 |
| parse / normal / length lemma | memory_limit | 12.979594 | 4296347648 |
| dimension / normal | succeeded | 5.182718 | 1620123648 |
| dimension / kernel | succeeded | 1.085272 | 1400291328 |

Every step retained the 4294967296-byte sampled process-tree RSS cap,
180-second wall cap, one thread, normal maxRecDepth=1000000, and
maxHeartbeats=0. No higher-budget retry was made. Original files and all reused
objects were fingerprinted before and after each relevant run. No foundation
reader/helper was rebuilt, no production source was edited, and no P1 or other
remote job was submitted.

## Exact raw input and new representation

The sole actual input is
`/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`,
195134 ASCII bytes, SHA256
`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`.
It uses CRLF. The original Lean IO reader preserves both characters. The
mechanically quoted data and its kernel-checked length include them.

```lean
noncomputable def geometryChars00 : List Char := originalGeometryChars00%
noncomputable def geometryText00 : String := String.ofList geometryChars00
```

This is explicitly a new data representation. No equality to a previous Core
String-literal definition is assumed or proved. The loader performs only
`IO.FS.readFile` followed by `toExpr s.toList`; it does not interpret JSON or
perform numerical mathematics. Host hashes and counts establish provenance,
not a substitute proof of an older `htext`.

The data object is 6361008 bytes, SHA256
`e8d785d76de156581dc5ae2c986d98bc7cc44387695ebb31f10110d0ea2719d9`.
The length object is 7312 bytes, SHA256
`4dcfa678dad2b10c69798981a79d40d2408c26671b4957b6882b459adea5e498`.
The length theorem's printed axiom set is empty. The data owner received normal
checking only; length and dimension owners received their explicit independent
replays. This is not a full owned-closure acceptance claim.

## Small real-field certificate that passed

The exact first prefix is `{\r\n  "dimension": 8,`, **20** ASCII characters,
including the comma. An earlier human-readable preview normalized CRLF; the
19-character estimate was corrected before any prefix candidate was generated
or compiled. The actual-data owner and its length theorem were unaffected.

`generate_dimension_prefix.py` reads raw bytes, preserves CRLF, emits only the
small prefix and expected key/number data, and records offsets and hashes. It
never invokes a host JSON parser. The emitted expectations are candidates until
the original Lean reader equality certifies them.

The module proves these four exact statements:

```lean
geometryChars00.take 20 = dimensionPrefixChars00

∀ fuel tail,
  SourceJson.value (fuel + 12) (dimensionPrefixChars00 ++ tail) =
    SourceJson.object (fuel + 10) (SourceJson.white tail)
      [(dimensionKey00, dimensionValue00)]

geometryChars00 = dimensionPrefixChars00 ++ geometryChars00.drop 20

SourceJson.value 195135 geometryChars00 =
  SourceJson.object 195133 (SourceJson.white (geometryChars00.drop 20))
    [(dimensionKey00, dimensionValue00)]
```

The first two proofs are `rfl`. The input split uses the checked first theorem
and the library's `List.take_append_drop`. The final closed equality instantiates
the generic reader transition and composes it with the exact complete-input
split. The tail is an expression using the original character data; it is not a
newly quoted copy of all remaining bytes.

The original `value`, `object`, `white`, `quoted`, and integer-token rules are
unchanged. The delimiter and whitespace are retained, and the original
empty-accumulator duplicate-key check is part of the `rfl` reduction. This
proves a first-field transition, **not success of the remaining object**.

Axiom sets are empty for prefix binding and input split, and `[propext]` for the
generic and concrete reader transition. The passed source SHA256 is
`d64263d9c3e35fe05bd998cdaf5f523ea7ae2db933bcd41ca31f9033f5b162aa`.
Its 73776-byte olean SHA256 is
`2792ba91cb949245fefb1cd11b21990399a6eb7e44359f9d95b95d4c28784304`.

## Whole-parser attempts retained as failures

The first parser command failed at import resolution because Lean's first
`ImbalancedChen` package root shadowed the later object directory. The exact
old source/log/result remain intact. Under Root's explicit environment-repair
authorization, all three foundational objects were copied byte-for-byte into
this candidate's own object root. No auxiliary `.olean.private`, `.olean.server`,
or IR sibling files were present. `IMPORT_LAYOUT_FIX.json` records source,
copy, and post-copy SHA equality.

The repaired original guard reached `before_parseChars_success_guard` and then
exceeded memory. A separately frozen proof-only variant unfolded exactly
`SourceJson.parseChars` and `CharInputBridge.parseChars`, rewrote
`geometryChars00_length`, and emitted
`after_length_rewrite_before_reader_guard` before `decide +kernel`. That marker
was observed before its memory failure. Thus the latter failure belongs to the
remaining original-reader success guard after the length rewrite; no finer
hotspot is claimed without profiling.

Both variants retain the same closed statement and the same subsequent
`parse_ofList` transport theorem. Neither generated an olean. No typed decoder,
payload equality, remaining cell, or numerical row was checked. There is no
formal parser-success credit from these failed sources.

## Evidence and remaining scope

`RESULT.json` contains every stage. `DIMENSION_PREFIX_RESULT.json` contains the
successful normal/kernel records and exact axiom audit. Immutable manifests,
all commands and logs, the old-failure snapshot directory, and the proof-only
diff preserve unsuccessful attempts separately. `FINAL_STATIC_AUDIT.json`
checks forbidden proof escapes and the unchanged whole-parser theorem headers.
`SEGMENTATION_DESIGN.md` gives the next exact interfaces, explicitly as a design,
not additional proved declarations.

No further field or whole-parser run was performed after the dimension check.
This candidate does not establish complete geometry00 parse success, typed
archive decoding, original-String equality, or scalability to thirteen cells.
