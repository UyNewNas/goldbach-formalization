# Cell 00: complete original pure JSON reader certificate

**Observed result:** all 156 new owners passed normal compilation and independent `leanchecker`; the exact project import closure contains 164 modules including 8 previously accepted, unchanged suppliers. This is local validation, not P1 or production acceptance.

## Closed statements

The namespace is `ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic`. The final theorem source is `ImbalancedChen/P2OriginalSaving19WholeParse00.lean`, SHA256 `e40d1d70b32d15926a0b79117c27eb3061ffc838d1085bc3df696146e0159443`.

```lean
geometryChars00_whole_value :
  SourceJson.value 195135 geometryChars00 =
    .ok (originalGeometryJson00, geometryChars00.drop 195132)

geometryChars00_white_tail :
  SourceJson.white (geometryChars00.drop 195132) = []

geometryChars00_parseChars :
  SourceJson.parseChars geometryChars00 = .ok originalGeometryJson00

geometryText00_parse :
  SourceJson.parse geometryText00 = .ok originalGeometryJson00
```

`geometryText00` is `String.ofList geometryChars00`. The original ASCII file has 195134 bytes, SHA256 `87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`; its original CRLF bytes are preserved. The root value ends at byte 195132, and the two remaining bytes are exactly CRLF. All raw string tokens, fields, metadata, original duplicate-key checks, separators, accumulator order and exact remaining input are retained.

## Complete field coverage

| Original field | Value byte span | Array items |
|---|---:|---:|
| `dimension` | [18, 19) | — |
| `physical_jacobian` | [45, 46) | — |
| `facet_original_indices` | [77, 178) | 11 |
| `positive_normal_balance` | [210, 358) | 11 |
| `normal_rank` | [378, 379) | — |
| `active8_enumeration` | [407, 40597) | 165 |
| `vertices` | [40614, 46974) | 28 |
| `vertex_values` | [46996, 60448) | 28 |
| `all_original_constraint_minima` | [60487, 62654) | 97 |
| `facet_vertices` | [62677, 65220) | 11 |
| `face_ledger` | [65240, 100415) | 39 |
| `simplices` | [100433, 194776) | 56 |
| `physical_volume` | [194800, 194941) | — |
| `integral_gap` | [194962, 195129) | — |

## Validation and resource evidence

- Fixed per-owner limits: 4 GiB sampled process-tree RSS, 180 seconds, one thread; no resource budget was increased.
- Final WholeParse normal: 20.778 s, peak 3,814,432,768 B; independent kernel: 12.139 s, peak 3,282,837,504 B.
- All 1747 new theorem declarations have corresponding `#print axioms` output. The union is only `propext`, `Classical.choice`, `Quot.sound`; source scans reject sorry/admit/native_decide/unsafe and new axiom declarations.
- The largest successful sampled observation is SimplicesArrayBlock01200 normal: 22.379 s and 4,241,305,600 B.
- Every receipt pins source, object, log, runtime and imported source/object invariants. Previously accepted objects were copied byte-for-byte into the private object root and never recompiled.
- Host parsing only planned candidate spans and data. Every emitted parse claim is an equality for the original Lean reader; no host decision or whole-file `decide` was used as a parsing proof.

## Preserved failure history

Five failed attempts remain in `logs/`, with exact old source/manifest snapshots in `revisions/`: one Active8 parent continuation resource failure, two small ParseFromValue API/exposure failures, one final simplex input-slice resource failure, and one final implicit-argument API error. None emitted an accepted object. Each repaired owner passed a separate normal/kernel attempt.

The Active8 continuation repair moved the remaining-input branch into a theorem for arbitrary tail, preventing unintended reduction of the whole concrete suffix. The final simplex repair isolated the exact original `(drop 188334).take 6442` equality in a one-import raw-slice owner, then used opaque transitivity; the revised parser block fell from a 4 GiB limit failure to a 2.126 GB normal peak. The final WholeParse change only names the implicit argument in `List.drop_length (l := geometryChars00)`. All exact diffs and failure receipts are retained.

## Stable delivery files

- `SOURCE_MANIFEST.json`: all 164 project sources, source hashes, topological import order, scope and representation boundary.
- `SOURCE_INPUTS.json`: source/object closure and per-new-owner normal/kernel receipt fingerprints.
- `VALIDATION.json`: complete field inventory, statement scope, fixed limits, peak observation, full failed-attempt inventory and axiom audit.
- `PROGRESS.json`: final per-owner success checkpoint.
- `collect_delivery.py`: read-only consistency collector; it refuses partial whole-parse state.
- `METHOD.md`: source-generation method and expression-repair rationale.

## Remaining boundary and next representation bridge

This certificate concerns the explicit CharacterCoreDiagnostic input. It does not yet identify that list with production `Archive.geometryPacked00.toList` or the earlier production string literal. It proves no typed Geometry decoder, geometric validity, numerical moment/floor, other cell file or final theorem. Those are separate obligations.

A read-only scan found 186 already proved exact prefix spans covering every byte of `[0,195134)` with no gaps, including every header, comma and final CRLF. The next bridge can prove the same compact-input slices, then assemble full list equality with `List.take_append_drop` and the empty final tail. This reuses the complete existing parser proof; no parser owner needs to be recompiled.
