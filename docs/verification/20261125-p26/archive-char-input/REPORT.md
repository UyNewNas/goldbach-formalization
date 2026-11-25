# Saving19 character-input bridge: bounded local result

## What is proved

`ImbalancedChen/P2OriginalSaving19CharInputBridge.lean` imports only `Lean` and
proves a representation identity for an arbitrary parser engine:

```lean
parseString reader white unconsumed (String.ofList cs) =
  parseChars reader white unconsumed cs
```

Both front ends pass exactly the same character list and the same fuel. They
also run exactly the same unconsumed-tail check. Consequently the theorem
preserves the complete `Except` value, including failure messages and successful
payloads. Its proof uses the pinned `String.length_ofList` and
`String.toList_ofList` theorems; it does not evaluate a witness or assume that
parsing succeeds. No `DecidableEq Value` hypothesis is required.

The module also provides two explicit bindings to an existing String `s`:

```lean
parseString_eq_parseChars_of_chars_eq
  ... (s : String) (cs : List Char) (hchars : cs = s.toList)

parseString_eq_parseChars_of_ofList_eq
  ... (s : String) (cs : List Char) (htext : String.ofList cs = s)
```

`success_of_chars_success` transports a full successful parse result through
the first theorem. It does not supply the required successful parse proof.

Local normal compilation and independent `leanchecker --verbose` replay both
passed: 4.436 seconds and 1.879 seconds respectively. All four theorem axiom
reports contain exactly `propext`, `Classical.choice`, and `Quot.sound`; no new
axiom is declared. The complete commands, source/object/log hashes, exact Lean
version, read-only cache marker, and explicit no-archive-credit flags are in
`local/DIAGNOSTIC.json`. The only source import is `Lean`; the environment's
Mathlib pin was checked but no Mathlib module was compiled.

## Actual SourceJson companion

`ImbalancedChen/P2OriginalSaving19SourceJsonCharInput.lean` is a locally checked
companion candidate. It imports the unchanged original `SourceJson` and the
checked generic bridge, defines `SourceJson.parseChars`, and supplies:

| Interface | Exact purpose |
| --- | --- |
| `parse_ofList` | `parse (String.ofList cs) = parseChars cs` |
| `parseChars_eq_parse_ofList` | The symmetric representation identity |
| `parse_eq_parseChars_of_chars_eq` | Bind an old String using `cs = s.toList` |
| `parse_eq_parseChars_of_ofList_eq` | Bind an old String using `String.ofList cs = s` |
| `parse_bind_eq_parseChars_bind_of_ofList_eq` | Transport the identity through any unchanged typed decoder |

The companion passed normal compilation (0.919 seconds), independent kernel
replay (1.680 seconds), and an explicit types/axioms audit (0.917 seconds). All
five interface theorems use exactly the standard three axioms; the `parseChars`
definition uses only `propext`. The required original reader was compiled only
in the independent candidate directory (2.020 seconds), then replayed by
leanchecker (1.719 seconds). The already checked generic bridge object was
reused unchanged; it was not recompiled. The complete record is
`local/COMPANION_DIAGNOSTIC.json`. The original parser source was read and
compared byte for byte with commit
`508d757913ea9c536c0d4f95abb35c090b940a29`, path
`ImbalancedChen/P2OriginalSaving19SourceJson.lean`: 6,035 bytes, SHA-256
`ae38e3ed3f11d8bc3350b9d35d1fed164a4494210ed993b2b99e8cd709f93424`.
`SOURCE_ORIGIN.json` records that check. The production SourceJson and Archive
sources and accepted ArchiveCore were not modified. ArchiveCore was not
imported or compiled; the only necessary reader compilation used the exact
6,035-byte copy under `local/reader-source`.

## Why this targets a measured cost

The sibling's frozen `parser-diagnostic/STRING_LENGTH_RESULT.json` records that
the original geometry00 String literal's length alone, with the theorem
`geometry00Text.length = 195134` and `decide +kernel`, exceeded a 6,144 MB limit
after 21.856 seconds, peak 6,154.61 MB. That experiment imported only `Lean`; it
did not run SourceJson or a typed decoder. Its frozen raw input path was
`/workspace/goldbach-research/eighth-third-minorant-extension-20261009-a23-s23_low-00-cell.witness.json`,
195,134 bytes, SHA-256
`87e3c3da5a86a3ea16c1dcae3a5735ea8b0dc7db05d42b5f5cc3aae66cd54691`.
The encoding-only host preflight found ASCII. These are reported measurements,
not a Lean proof of a mathematical certificate.

In the pinned runtime, `String.length` is defined as `s.toList.length`. The
character front end removes the large old-String-to-list computation from the
closed parser guard after a kernel-checked representation rewrite. It still
computes a list length and runs the original total parser. It does not establish
that those remaining computations fit a memory or time budget.

## Required binding to the accepted Core

Keeping the accepted Core unchanged is possible only after a real Lean proof
binds the new characters to its existing `geometryText` / `momentText` String
declarations. Equality of source paths, byte counts, or SHA-256 hashes is useful
provenance and is not that mathematical equality proof.

The smallest proposed path is:

1. Read the exact existing original file with the same loader path. The host
   step may encode its characters into a Lean literal; it must not parse JSON,
   decode rationals, choose numerical witnesses, or replace any mathematical
   check.
2. Prove `String.ofList cs = oldText` in Lean, directly or by kernel-checked
   chunk equalities. The sibling is separately measuring this obligation;
   this task does not claim it has passed. The separately measured 128 KiB
   direct `rfl` attempt reached a 2 GiB budget and produced no accepted object.
3. Rewrite the existing parser/decoder expression with the companion's
   `parse_bind_eq_parseChars_bind_of_ofList_eq`. The original parser, record
   decoder, Q80 bounds, and target theorem statement remain in force.
4. Prove the success-tag guard using the rewritten expression, then use the
   already prepared generic Except constructor-elimination lemma to recover
   the original full parse equation. Preserve normal/kernel/full-owned audit
   gates and all 26 before/after fixture bindings.

The pinned Meta implementation has specific support for constraints of the
form a String literal equal to `String.ofList cs`:
`Lean/Meta/ExprDefEq.lean`, `isDefEqStringLit`. The root agent identified it and
the sibling is testing the complete kernel cost. Meta support alone is not
evidence that a large concrete equality is cheap or already certified.

## Existing mechanisms checked before proposing this bridge

The materialized production, verification, and current P2.6 documentation trees
were searched for `mkCharLit`, `mkListLit`, `parseChars`, `toList_ofList`,
`ofList_toList`, raw-character loader names, and character-tree names. No
existing ready-to-use original-JSON Char-list loader or parser front-end bridge
was found in that scope. This is a bounded search result, not a claim about
unmaterialized historical objects.

Two relevant mechanisms already exist:

- `P4AOriginalNewFifthArchiveReader.lean` has the direct original-byte loader
  `include_new_fifth_pair%` and a balanced `Words` representation, with
  `Words.prepend_eq`, `Words.length_list`, `Words.sum_list`, and `Words.all_spec`.
  It encodes entire original headers and raw fields without performing the
  formal mathematical checks in the host loader. This is a reusable design
  precedent for bounded raw encodings. It is not a theorem binding Saving19's
  old String literals to a new Char-list representation.
- `P1OriginalFourthPackedTableDecoder.lean` supplies `decodeHexChars`, its
  structural `decodeHexChars_cons` equation, and `decodePackedHex`. The latter
  still calls `payload.toList`. It is not an existing solution to the measured
  large String front-end cost.

## Fuel remains a separate possible bottleneck

The original front end uses fuel `cs.length + 1`; the bridge intentionally
preserves that fuel. Every recursive zero-fuel branch in `quoted`, `value`,
`array`, and `object` is an error. A small-fuel success can in principle be
transported to greater fuel, but the required theorem must preserve the exact
successful payload and remaining tail, not merely an acceptance bit.

The precise proof obligations are success monotonicity for `quoted`, followed
by simultaneous success monotonicity for `value`, `array`, and `object`.
`quoted` can be handled by induction on the smaller fuel; the mutual parser
requires the corresponding joint induction, with the already proved quoted
result used in its String/object branches. No branch condition depends on
fuel except the zero guards and recursive fuel arguments, so successful
branches are the relevant ones. Failure monotonicity is not claimed: a fuel
error can become success at larger fuel.

Those parser-specific monotonicity theorems have not been proved here, and no
small fuel is asserted sufficient for any original witness. Adding a
hypothesis that the parser is fuel-monotone would only expose a new obligation;
it would not discharge it. The existing large-fuel parser proof must therefore
remain the target until such actual lemmas and a concrete small-fuel success
proof are supplied.

## Scope of the delivered result

The data-independent generic bridge and actual SourceJson companion have both
passed local normal compilation and independent kernel replay; the actual
companion also passed the explicit interface types/axioms audit. Its single
required reader dependency was compiled from the pinned, unchanged source.
`TRANSPARENCY_AUDIT.md` gives the source-based review of old-literal binding.
No original fixture was loaded locally, no archive theorem was proved, no P1
job was submitted, and no production source or accepted object was changed. `archive_complete` and `only_cell00_proved`
remain false.
