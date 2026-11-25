# Exact original-reader segmentation: boundary and interfaces

## Proved starting point

`P2OriginalSaving19DimensionPrefix00` has passed normal and independent
leanchecker. Its final closed theorem is:

```lean
SourceJson.value 195135 geometryChars00 =
  SourceJson.object 195133 (SourceJson.white (geometryChars00.drop 20))
    [(dimensionKey00, dimensionValue00)]
```

The first 20 characters are exactly `{\r\n  "dimension": 8,`. A closed `rfl`
lemma binds `geometryChars00.take 20` to that prefix, and
`List.take_append_drop` supplies the complete-input split. The suffix is not a
copied character list. The intermediate data uses `String.ofList` of small raw
character lists; its reader relationship is proved rather than trusted from a
host parser.

This is one local transition. Complete object success and typed decoding remain
unproved. It does not assert equality with the old Core String-literal input.

## Minimal interfaces for further composition (design only)

These are the original parser's exact state transitions, not proposed new
parsing rules. No new generic declarations listed below are claimed checked.

### A nonempty array item

Given the original `value` equality

```lean
value fuel input = .ok (v, rest)
```

and a checked comma boundary

```lean
white rest = ',' :: tail
```

the original nonempty-item branch advances

```lean
array (fuel + 1) input acc =
  array fuel (white tail) (v :: acc)
```

A generic proof must also handle or exclude the separate empty-array branch
(`input = ']' :: tail` and `acc = []`); for a quoted actual nonempty value prefix,
its first character gives the exclusion directly. `acc` should remain a
parameter, so an item certificate does not repeatedly expand all prior items.
At a closing bracket the exact result is `.arr ((v :: acc).reverse)`. The order
and reversal cannot be discarded.

### An object field

For the exact original input shape `'"' :: xs`, the component obligations are:

```lean
quoted fuel xs [] = .ok (key, rest)
white rest = ':' :: body
value fuel body = .ok (v, tail)
acc.any (fun kv => kv.1 == key) = false
white tail = ',' :: ending
```

They yield the original branch equation

```lean
object (fuel + 1) ('"' :: xs) acc =
  object fuel (white ending) ((key, v) :: acc)
```

At `}` the exact result is `.obj (((key, v) :: acc).reverse)`. The duplicate-key
check is mandatory. For the first few real fields it may reduce over the
already certified concrete accumulator. A general interface must retain its
closed check or an explicit proved premise; it must not silently replace it by
an assumption that all generated keys are distinct.

### Values with generalized tails

A leaf/subtree certificate should keep the remainder abstract:

```lean
value fuel (prefix ++ tail) = .ok (expected, tail)
```

For numbers, a non-digit delimiter must be present at the boundary; otherwise
the original scanner can consume the first characters of `tail`. The dimension
certificate includes the actual comma. Quoted strings include their closing
quote, and parent object/array certificates retain separator and whitespace
checks. Fuel is the original function argument, not a new count of consumed
bytes: `quoted` does not return remaining fuel, and parent object/array
continuations use the exact predecessor passed by their own original branch.

## Binding a segment to the unchanged complete character data

For a candidate prefix of length `n` at an already bound suffix `s`, establish
` s.take n = prefix ` by a closed proof. Then use the existing list identity
`s.take n ++ s.drop n = s`. Composition should transport these equalities through
the original `value`, `object`, or `array` calls with `congrArg` and transitivity.
This avoids `decide` on equality of two complete remaining suffix lists.

Every offset must be measured on raw bytes/ASCII characters, preserving both CR
and LF. The single canonical fixture and its checked new character-data owner
remain the source of every suffix. Candidate AST quotation or mechanical
segmentation can generate data, but only the original-reader Lean equality
certifies it. The root parser equation and all typed-decoder obligations remain.

Repeated `drop` from a very large offset and copying every explicit suffix are
potential scaling problems. The current one-field result establishes neither
that such a scheme scales to all fields nor that a balanced representation is
needed. Reuse the existing data and length objects, keep tails symbolic, and
introduce bounded checkpoint data only with exact original-reader bindings.

## Current observed cost boundary

The whole-reader proof still exceeded 4 GiB after both front-end definitions had
been unfolded and the checked length theorem rewritten; the explicit marker
before the remaining reader guard was observed. A single dimension transition
on an abstract tail and then the complete input passed within the same budget.
This supports testing exact segmented composition. It is not a profile proving
which internal reader function allocates most memory.

Static additional repeated work includes `integerToken` using the digit-list
length for both leading-zero checking and dropping the consumed digits, and
objects repeatedly checking prior key names. The latter is required semantics;
any cached result must itself be proved. No rule was removed and no resource
budget was raised in these diagnostics.
