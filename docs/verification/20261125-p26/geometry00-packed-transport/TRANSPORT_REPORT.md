# Geometry cell 00: production compact input equality and parser transport

**Complete local result:** all 40 owners in this transport stage passed normal compilation and independent `leanchecker`. The full project source/object closure contains 206 modules. The 166 accepted suppliers—including the entire previous parser closure and the accepted packed representation/loader—were copied byte-for-byte and never recompiled. The original parser was not rerun.

## Closed final statements

The final module is `ImbalancedChen.P2OriginalSaving19GeometryPackedParseTransport00`, source SHA256 `45fe4bebeced2ec965e8e6ade00bfa191d2ded4ef11f876f1a1aa4651e93d324`, object SHA256 `6693940df0f4ffa6f1e5b49e8f766a78db0ebc8b3d34f6411cdcc5486f9e4254` (44200 bytes).

The theorem namespace is `ImbalancedChen.P2OriginalSaving19GeometryPackedTransport`. Here `geometryChars00` and `originalGeometryJson00` are the already verified values in `ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic`, and `geometryPacked00` is the production FQN `ImbalancedChen.P2OriginalSaving19Archive.geometryPacked00`.

```lean
geometryChars00_eq_geometryPacked00 :
  geometryChars00 = geometryPacked00.toList

geometryPacked00_whole_value :
  SourceJson.value 195135 geometryPacked00.toList =
    .ok (originalGeometryJson00, geometryPacked00.toList.drop 195132)

geometryPacked00_parseChars :
  SourceJson.parseChars geometryPacked00.toList = .ok originalGeometryJson00

geometryPacked00_original_parse :
  SourceJson.parse (String.ofList geometryPacked00.toList) =
    .ok originalGeometryJson00
```

All four statements are closed, with no premises. The JSON value is the same full 14-field value established by the original-reader certificate, preserving metadata, duplicate-key checks, complete raw values and the original CRLF tail. These statements are ready to combine with a separately proved `decodeGeometry originalGeometryJson00 = .ok concreteGeometry00` using an opaque `Except` bind interface.

## Why the representation equality is complete

The previous parser package already contained 186 exact prefix theorems whose spans concatenate to `[0,195134)`. This stage proves the corresponding compact-input slice equality for each span. Headers, commas, brackets and the terminal CRLF are included, and no byte range is skipped. The largest individual span is 10530 characters.

The compact rest is `(geometryPacked00.drop n).toList`; the accepted `Tree.toList_drop` theorem connects it to list drop. Small proofs based on `List.take_append_drop` reconstruct each interval from its common finite prefix and the following tail. The final proof starts from both empty tails at byte 195134 and applies the 37 group reassembly theorems in reverse order. All intermediate tail-equality hypotheses are discharged. The resulting full-list equality then transports the existing opaque value and parser theorems via `congrArg`; no whole-file parser evaluation or whole-file decision procedure is used.

## Exact input provenance

The unchanged v4 GeometryData00 source has SHA256 `89a3c1bb21c715408eedd9b6264ae9d6d35a3f1ccf939e785a46bb92b95d9ab9`. It retains the original relative path `../goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json` and the production FQN. The actual local Lean working directory is `/workspace/p26-recovery-candidates/geometry-packed-transport/project`; that path resolves to `/workspace/p26-recovery-candidates/geometry-packed-transport/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`.

The private mirror is byte-identical to the original 195134-byte ASCII/CRLF file, SHA256 `87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`. The accepted ArchivePackedLoader object is reused, not rebuilt. Its exact source/object identity and the PackedChars supplier are pinned in `FROZEN_SUPPLIERS.json`; `BOOTSTRAP.json` records the original and mirror file hashes and source hashes.

## Checks and resources

| Stage | Normal | Independent kernel |
|---|---:|---:|
| Final equality and parser transport | 1.191 s; 1,648,336,896 B | 0.990 s; 1,424,904,192 B |
| Maximum individual 10530-character interval (group 020) | 54.541 s; 2,828,533,760 B | 34.361 s; 2,152,689,664 B |

The fixed per-owner limits remain 4 GiB sampled process-tree RSS, 180 seconds and one thread. All 606 new theorem declarations have corresponding `#print axioms` output. The union is only `propext`, `Quot.sound`, `Classical.choice`. Source scans reject `sorry`, `admit`, `native_decide`, `unsafe`, and new axiom declarations. Each receipt checks exact source/object/import/raw-input fingerprints before and after the process.

One initial input-interface attempt failed on Lean-only syntax (`Type*` and the reserved binder `prefix`); its exact source and log are retained. The minimal correction uses `Type` and the local binder `part`. This is an expression/API repair. No mathematical estimate, reader rule or data change was needed, and no resource budget was increased.

## Stable artifacts

- `SOURCE_MANIFEST.json`: exact 206-source topological closure, current generator/runner fingerprints and representation boundary.
- `SOURCE_INPUTS.json`: complete source/object closure and all new-owner normal/kernel receipts.
- `VALIDATION.json`: final four-statement scope, 186 span / 37 group coverage, theorem/axiom checks, failures and peak resources.
- `SPAN_PLAN.json`: complete original-theorem-to-compact-span mapping; the plan itself is not treated as a proof.
- `BOOTSTRAP.json`: unchanged v4 source and actual local relative-path resolution.
- `PROGRESS.json`: all 40 current owners accepted; `whole_transport_verified` is true.
- `METHOD.md`: proof architecture and scope.
- `EXPORT_FILELIST.txt`: source/evidence packaging range excluding objects, Python caches and the duplicate private raw-input mirror; the already archived original raw artifact supplies the input.

## Remaining boundary

This is local normal plus independent-kernel validation, not P1 or production-runner acceptance. It closes the old-character-list to production-packed-list equality and the complete original pure parser result. Typed Geometry decoding, geometric validity, moment/floor checks, other geometry files and equivalence to the earlier production String literal are separate claims. The typed decode owner can reuse this exact parsed JSON and terminal object; the parser proof need not be repeated.
