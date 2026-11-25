# Original geometry00: first three fields, exact reader composition

## Observed result

`P2OriginalSaving19FirstThreeFields00` passed normal compilation and independent
leanchecker on its first attempt. This extends the already checked dimension
field with exactly `physical_jacobian: 1` and the eleven-number
`facet_original_indices` array. No whole-parser success goal was rerun.

| Check | Exit | Seconds | Peak sampled RSS |
|---|---:|---:|---:|
| normal | 0 | 4.376213 | 1644900352 bytes |
| independent kernel | 0 | 1.212289 | 1404039168 bytes |

The budget remains 4 GiB / 180 seconds per step, with one thread,
maxRecDepth=1000000 and diagnostic maxHeartbeats=0 for normal elaboration.
The existing raw-character data, length, dimension, and original-reader objects
were reused without recompilation. Their source/copy/object hashes and the
original fixture hash were checked before and after the runs.

## Exact statement now closed

```lean
theorem geometryChars00_through_facet_indices :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195131
        (SourceJson.white (geometryChars00.drop 179))
        facetIndicesAcc00
```

There are no hypotheses. The accumulator is in the original parser's reverse
field order: the eleven-element facet array, physical_jacobian 1, then dimension
8. The remaining original `object` call is retained. The theorem does not
assert that the remaining object parses successfully.

## Raw character bindings

All slicing uses `read_bytes()` and ASCII decoding, preserving CRLF exactly.
The original geometry00 is 195134 bytes, SHA256
`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`.

| Slice | Byte/character interval | Length |
|---|---|---:|
| physical field with initial CRLF and final comma | [20,47) | 27 |
| facet field with initial CRLF and final comma | [47,179) | 132 |
| complete array value, including both brackets | [77,178) | 101 |

The candidate array contains the exact tokens
`7, 8, 9, 14, 18, 19, 34, 39, 61, 75, 82` in their original order.
The generator only quotes raw slices and digit-token candidates; it never calls
a host JSON parser. The original-reader equations certify these candidate data.

The physical and facet prefix bindings are closed `rfl` proofs of the relevant
`take` on the actual `drop` suffix. The complete suffix equalities then use
`List.take_append_drop` and `List.drop_drop`. No complete remaining suffix is
regenerated or copied into a new character-list literal.

## Composition and preserved rules

The physical-field lemma is generic in remaining fuel and tail, with the
already checked dimension accumulator retained. Its `rfl` proof runs the
original quoted-key, colon, integer-token, nonempty-accumulator duplicate-key,
whitespace, and comma branches.

The eleven-element array has its own value theorem, generic in fuel and tail:

```lean
SourceJson.value (fuel + 13) (facetIndicesArrayChars00 ++ tail) =
  .ok (facetIndicesValue00, tail)
```

The closing bracket is inside the checked prefix; therefore the arbitrary tail
cannot be consumed as part of the last number. The original array reversal
fixes the output item order.

A separate facet-header equality binds the original object reader to its
post-value continuation, retaining the two existing fields and checking the new
key against both. The quoted continuation keeps all original closing-brace,
comma, and separator-error branches, including the final object reversal.
The facet-field proof reuses the proved array-value theorem with the actual
comma prepended to its tail. It does not perform another whole array parse as
a closed `decide` guard.

Fuel matches the original calls exactly. The complete chain is
195135 (root value) → 195133 (after dimension) → 195132 (after physical) →
195131 (after facets). The eleven array items use their internal fuel in the
proved value equality; this does not decrement the enclosing object's
continuation fuel by the number of bytes or array items.

An independent read-only review by the existing-audit subagent found no missing
fuel, rest, accumulator, duplicate-key, separator, or digit-boundary obligation
in this source. That review supplements the normal/kernel evidence.

## Axioms and artifacts

All eleven printed theorem axiom sets were checked. The two direct prefix
bindings have no axioms; the remaining printed theorems use only `propext`,
inherited through the original reader/list proof interfaces. No new axiom or
forbidden proof escape was introduced.

Source: `ImbalancedChen/P2OriginalSaving19FirstThreeFields00.lean`

Source SHA256:
`917489d7281d18b9bdd25027ff6fd4b58e65a16d98465dff7c6ecee0bb3e68a0`

Object: 574288 bytes, SHA256
`1c49efaa3ffa5fac22e9906a8413036f7087e3ca74a979d08d123a2c8f337a79`.

`FIRST_THREE_FIELDS_MANIFEST.json` freezes data spans, dependencies, and source.
`FIRST_THREE_FIELDS_RESULT.json` records both runs, exact axiom sets, and the
closed target. `FIRST_THREE_FIELDS_STATIC_AUDIT.json` records static gates.
`generate_first_three_fields.py` is the deterministic candidate generator;
`run_first_three_fields.py` preserves the resource limits and original log.

The previously frozen dimension REPORT/RESULT/design checkpoint is unchanged;
this report is an additive checkpoint. There is still no whole geometry00
parse-success, typed-decoder, old-Core-String equality, or thirteen-cell
acceptance claim. No production source or P1 environment was changed.
