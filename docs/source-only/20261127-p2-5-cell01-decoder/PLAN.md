# Cell01 original decoder continuation

> **For agentic workers:** Follow the existing P2.5 execution plan and use
> `superpowers:executing-plans`; retain the user's no-duplicate-work rule.

**Goal:** Supply the missing original-decoder equalities for the existing
Cell01 candidate, preserving all 17 fields and 81 ordered simplex records.

**Architecture:** Reuse the published Cell00 scalar/field composition pattern
and exact generic DecoderChars/DecoderCompose. Read the unchanged Cell01 typed
candidate and manifest. Generate bounded scalar owners, one owner per simplex,
root-field certificates, and an opaque symbolic composition. Do not regenerate
input, parser, payload, finite arithmetic, or any existing Cell00 owner.

**Tech stack:** Pinned Lean 4.33.0-rc1 / mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; Python standard library.

**Spec:** The frozen 1106 manuscript's eighth-prefix-family certificate and
`../20261126-p2-5-cell01-parser-typed/README.md`.

## Constraints and decisions

- Baseline publication: `ed8d9c028b8656f01ca9788c4aa96ea305ed5c10`.
- The existing Cell01 raw witness hash remains
  `d7215c408203fd149155ec34af91c0d3af45a49d4dc64e23b508917d176a5c2f`.
- Retain literal numerator/denominator spelling, array order and every raw field.
- Already accepted scalar equations with identical strings are reused directly.
- Expose the existing symbolic record-composition proof through one public
  helper, so subsequent cells can use it without copying a private proof.
  This is an API extraction, not a new mathematical estimate.
- No new axioms, sorry/admit, native_decide, unsafe or partial declarations.
- Host generation and consistency checks grant no Lean acceptance.
- The four supplied cloud interfaces were unavailable at initial inspection.
  P2 subsequently became available and accepted the original parser and the
  24 decoder rows that required its memory budget. Reuse only verified objects;
  do not repeat accepted gates when transferring them between contexts.
- No P2.5 completion, Q96 or geometric guard follows from a decoder equality.

## Tasks

- [x] Record a failing completeness check for the absent new package.
- [x] Generate scalar and scoped-simp owners from the pinned existing manifest.
- [x] Generate 17 root lookups, 35 vertex decoders and 81 complete row decoders.
- [x] Extract the existing symbolic composition and instantiate it at Cell01.
- [x] Check source identity, exact row/key coverage and immutable regeneration.
- [x] Compile only new owners for which exact accepted dependencies are available;
      retain actual logs and record every unavailable prerequisite explicitly.
- [x] Independently review source/evidence, publish the bounded changes, and
      retain P2.5's unfinished status until all actual mathematical gates pass.

## Review focus

- Wrong input candidate or altered manifest must fail before output writes.
- A missing, duplicate or reordered simplex/key must fail the host check.
- The typed candidate and original decoder must remain unchanged.
- Scoped simplification must not leak into other cells or hide a fallback parse.
- Reused evidence, new source, normal compilation and full acceptance must
  remain separate in the handoff.
