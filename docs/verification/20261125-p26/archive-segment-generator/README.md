# One-field original-reader segment generator

This package adds one candidate Lean owner for the fourth field of the exact
cell 00 geometry witness. It also mechanically reproduces the previously
accepted dimension owner byte for byte, without recompiling that owner.

The new target is
`ImbalancedChen.P2OriginalSaving19PositiveBalanceSegments00`. Its concluding
theorem is the following transition on the complete original character input:

```lean
theorem geometryChars00_through_positive_balance :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195130
        (SourceJson.white (geometryChars00.drop 359)) positiveBalanceAcc00
```

The remaining object call is part of the conclusion. This is not a theorem
that the entire JSON document parses successfully, a typed archive decoding
theorem, or an equality with the previous String-literal representation.

## Exact inputs and ownership

The only raw fixture read is
`/workspace/p26-original-inputs/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`:
195134 bytes, ASCII, SHA-256
`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`.
The generator uses `read_bytes()` and explicit ASCII decoding, preserving
original CRLF. In this fixture a byte offset is exactly a Lean Char offset.
The tokenizer stops after the fourth field's comma at byte 359. It does not
parse the remaining 194775-byte suffix.

The original `SourceJson` source has SHA-256
`ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424`.
The generator imports its original `value`, `array`, `object`, `quoted`,
`white` and integer-token behavior through accepted dependencies. It does not
install a replacement Lean reader.

The manuscript agent owns the accepted dimension, physical_jacobian and
facet_original_indices proofs. This package reuses its
`geometryChars00_through_facet_indices` theorem and `facetIndicesAcc00`.
All accepted source and object fingerprints are pinned in
`SOURCE_MANIFEST.json`; the local runner verifies them before and after each
new-owner diagnostic. It copies existing `.olean` files byte for byte into
one local package root to avoid Lean package-root shadowing. It never
recompiles an accepted dependency.

The project-module import closure has six owners:

| Owner | Imports in the project closure | Action |
|---|---|---|
| SourceJson | none | Reuse accepted object |
| CharacterCore00 | none | Reuse accepted object |
| CharacterLength00 | CharacterCore00 | Reuse accepted object |
| DimensionPrefix00 | CharacterLength00, SourceJson | Reuse accepted object |
| FirstThreeFields00 | DimensionPrefix00 | Reuse accepted object |
| PositiveBalanceSegments00 | FirstThreeFields00 | New owner only |

The first two owners also import the standard Lean library. No Mathlib
rebuild, production edit or remote compile submission is part of this package.

## Dimension reproduction

`templates/DimensionPrefix00.lean.tmpl` preserves the accepted proof's source
shape. The generator computes its quoted prefix, key, number, offsets and
fuel from the pinned bytes. It renders them into
`reproduced/P2OriginalSaving19DimensionPrefix00.lean` and requires byte
equality with the accepted source:

`d64263d9c3e35fe05bd998cdaf5f523ea7ae2db933bcd41ca31f9033f5b162aa`.

The computed binding plan is prefix `[0,20)`, key content `[6,15)`, numeric
token `[18,19)`, generic root-value offset 12 and object offset 10. The actual
reader fuel is 195135 → 195133. This source reproduction is a static check;
it is not a second compilation of the accepted dimension owner.

## Fourth-field spans and fuel

`positive_normal_balance` has key content length 23 and eleven string values:
`1`, `1`, `19/26`, `1`, `176/39`, `385/312`, `7/26`, `17/39`, `11/13`,
`5/13`, `22/13`.

| Part | Exact raw span | Original reader | Selected fuel offset |
|---|---|---|---|
| Object header | `[179,210)` | object → value | 25 → 24 |
| Whole array value | `[210,358)` | value → array | 19 → 18 |
| Items 0–3 | `[211,255)` | array → array | 18 → 14 |
| Items 4–7 | `[255,313)` | array → array | 14 → 10 |
| Items 8–10 and closing bracket | `[313,358)` | array → `.ok` | 10 |
| Field plus comma | `[179,359)` | object → object | 25 → 24 |

The first two array chunks contain their final commas. The final array chunk
contains the closing bracket. Its result leaves the arbitrary following
`tail` completely intact. The field composition then supplies `',' :: tail`
as that following input, checks the original object separator branch, and
returns the original continuation on `white tail`.

Fuel is a structural recursion bound, not a byte counter or a residual fuel
returned by a child parse. In `array (f+1)` and `object (f+1)`, the current
child and the comma continuation both use the same `f`. The Lean statements
use explicit offsets 18, 14, 10, 19, 25 and 24; they do not use truncated Nat
subtraction to hide a boundary condition.

The host planner uses these candidate sufficient bounds:

- Integer, boolean and null value: 1.
- Quoted string: one per decoded character, one for the closing quote; the
  outer value adds one. A supported two-byte escape is one quoted recursion
  step.
- Nonempty array outer value: `max_i (i + 2 + need(value_i))`.
- Nonempty object outer value:
  `max_i (i + 2 + max(needQuoted(key_i), need(value_i)))`.
- Empty array/object outer value: 2.

These host calculations are untrusted planning results. The generated
original-reader equations, including their actual numerical offsets, are the
Lean obligations. No general fuel-monotonicity theorem is assumed.

## Compositional proof interfaces

For a nonfinal array chunk the generated theorem has the shape:

```lean
SourceJson.array (fuel + beforeOffset)
    (SourceJson.white (chunkChars ++ tail)) exactReverseAccBefore =
  SourceJson.array (fuel + afterOffset)
    (SourceJson.white tail) exactReverseAccAfter
```

The final chunk instead proves `.ok (.arr fullForwardItems, tail)`. Both
accumulators are explicit original reader states, and the final reverse is
performed exactly once. This pilot generates three small `rfl` proofs of
these equations and then uses the resulting theorems opaquely in a `calc`
composition. The final value theorem is plugged into an object-header
`Except.bind` equality. The original duplicate-key test is reduced against
the three real prior keys by the header's `rfl`; no distinctness hypothesis
replaces that check.

`ValueCertificateRef` in `generate.py` is the child-owner interface. An
external certificate must supply this original reader type:

```lean
∀ (fuel : Nat) (tail : List Char),
  SourceJson.value (fuel + suppliedOffset) (suppliedChars ++ tail) =
    .ok (suppliedValue, tail)
```

The optional `--child-certificate` JSON records module, theorem, character
data name, value name, offset, exact span and source fingerprint. The emitter
imports that module, checks local span data and result data by `rfl`, and uses
the supplied equality opaquely. Fingerprint/host checks do not replace Lean
type checking. This external-child branch is implemented but not exercised
by the present pilot; the local runner rejects it until its dependency
closure is separately reviewed.

The arbitrary append-tail interface is restricted to self-delimiting values.
An integer token cannot use it: appending a digit would change the token.
A future integer child certificate must retain an explicit fixed non-digit
delimiter and let the parent verify the delimiter is a legal JSON separator.
Whitespace is also not distributed across append: `white tail` is retained
exactly at each original continuation. The special empty-array branch does
not apply to any chunk here because its first nonwhite character is a quote.

The tokenizer can represent nested arrays and objects, and the certificate
interface supports child reuse. The only validated emitter instance here is
this one fourth-field owner. Generic large nested-object splitting, separate
per-chunk owner emission and full-document composition remain future work
for root to schedule. No claim of all 26 inputs or all 28918 archive rows is
made.

## Reproduction and local diagnostic

The generated source is immutable unless an explicit reviewed revision is
requested. `--revise` archives every changed generated artifact under its
old SHA-256 before replacement. `--check` is read only.

```bash
python3 /workspace/p26-recovery-candidates/archive-segment-generator/generate.py --check
python3 /workspace/p26-recovery-candidates/archive-segment-generator/run_local.py normal
python3 /workspace/p26-recovery-candidates/archive-segment-generator/run_local.py kernel
```

The last two commands are single-attempt diagnostics and refuse replay or
overwriting an object. Kernel mode requires a successful matching normal
receipt. They use the existing Lean 4.33.0-rc1 runtime, commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`, and retain the archive diagnostic
baseline: one thread, externally monitored 4 GiB RSS and 180-second wall
limits, maxRecDepth 1000000 and maxHeartbeats 0. These are local diagnostic
receipts, not P1 production acceptance.

Each receipt contains exact source/runtime/object hashes, command, input and
dependency invariants before and after, elapsed time, sampled peak RSS and
log hash. `#print axioms` covers all eleven new theorem declarations.
`VALIDATION.json` records the observed results without changing the source
manifest or the original command receipts.
