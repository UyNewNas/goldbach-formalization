# Actual geometry00 character-input diagnostic

## Outcome and exact scope

The new character-data owner passed normal compilation. The closed theorem
`geometryChars00.length = 195134` passed both normal compilation and independent
leanchecker replay, and its printed axiom set is empty.

The pure parser stage did **not enter parser computation**. It failed while
resolving an import: the first `ImbalancedChen` directory in LEAN_PATH shadows
the second library root, where the already checked SourceJson companion object
exists. No parser performance result or parser-success proof is claimed.
The authorized stop-on-first-failure rule was followed; no retry was issued.

| Stage | Exit | Seconds | Peak RSS (bytes) | Object |
|---|---:|---:|---:|---|
| data / normal | 0 | 7.043164 | 1842888704 | yes |
| length / normal | 0 | 10.669812 | 3347017728 | yes |
| length / kernel | 0 | 12.508183 | 3121446912 | yes |
| parse / normal | 1 | 0.448925 | 533975040 | no |

Every step used one thread, a 4294967296-byte sampled process-tree RSS cap,
a 180-second wall cap, normal maxRecDepth=1000000 and maxHeartbeats=0.
The geometry fixture and three reused foundational objects were fingerprinted
before and after every step and remained unchanged. No reader/helper was
recompiled, no production source was modified, and no remote job was submitted.

## New representation, explicitly declared

The data owner mechanically executes `IO.FS.readFile` on the exact original
geometry00 file, then emits `toExpr s.toList` as transparent noncomputable data:

```lean
noncomputable def geometryChars00 : List Char := originalGeometryChars00%
noncomputable def geometryText00 : String := String.ofList geometryChars00
```

This is an explicitly new input representation. It is not a proof of equality
with a previous String-literal declaration. No such `htext` is assumed or
claimed. The loader neither interprets JSON nor runs numerical mathematics.

The input was
`/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`,
195134 ASCII bytes, SHA256
`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`.
Host ASCII/count checks describe the preparation only. The actual new character
length is separately established by the closed kernel-checked guard.

The data object is 6361008 bytes, SHA256
`e8d785d76de156581dc5ae2c986d98bc7cc44387695ebb31f10110d0ea2719d9`.
The length object is 7312 bytes, SHA256
`4dcfa678dad2b10c69798981a79d40d2408c26671b4957b6882b459adea5e498`.
The data owner received normal checking only; the length owner received the
explicit independent replay. No full owned closure acceptance is claimed.

## Prepared pure-parser owner

The third source retains the original SourceJson functions and uses only its
existing companion `parseChars`. The intended closed guard is:

```lean
(SourceJson.parseChars geometryChars00).toOption.isSome = true
```

Its second theorem transports that result through the already proved
`SourceJson.parse_ofList` to `SourceJson.parse geometryText00`. These goals
remain uncompiled beyond import resolution; their presence in the file is not
proof credit. No typed decoder, record equality, other cell, or numerical row
is imported or tested here.

## Import-layout failure evidence

The exact diagnostic names:

```
object file '.../archive-character-core/objects/ImbalancedChen/P2OriginalSaving19SourceJsonCharInput.olean'
of module ImbalancedChen.P2OriginalSaving19SourceJsonCharInput does not exist
```

The saved existing object was in
`.../archive-char-input/local/lib/lean/ImbalancedChen/`, with SHA256
`2c823b172c17ff01681210825ff1caaab371660331e90f5fd29eb17b01797150`.
Same-pin `Lean/Util/Path.lean:61–65` confirms that search first chooses a root
containing the package directory, then forms the requested module path; it does
not fall through to a later root when that particular file is missing.

A concrete environment-only remedy would place symlinks or byte-identical copies
of the three already checked foundational oleans in this candidate's own object
root. This would not require source changes or recompilation. No repaired run
has been performed under this record.

## Evidence files

`MANIFEST.json` freezes all source and input fingerprints and the planned stages.
`STATIC_AUDIT.json` checks forbidden escapes, exact new representation, the
single raw-file read, closed length guard, and intended parser transport.
`RESULT.json` and `logs/*-result.json` record the outcomes; the logs preserve the
flush markers, exact empty axiom set, kernel replay, and import error.
`run_stage.py` prevents a repeated attempt or proceeding after a failed stage.

This is one geometry file and one new length guard. It establishes neither
Archive completion nor scalability to thirteen cells, and adds no acceptance
credit to the older original-String parse targets.
