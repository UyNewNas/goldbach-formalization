# Inverse-mean height dependency API repair

**SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.** This successor changes two
proof expressions in the exact older height dependencies selected by the
inverse-mean review. Compiled modules: **0**. Kernel-verified modules: **0**.
Independent source review and any full pinned build remain outstanding.

## Source selection and anchors

The input review is
`r14_05/inverse-mean-review/INVERSE_MEAN_ALLOWLIST.json`, SHA256
`65933b1b43e07078f8858cccc5dae1366a068832c1be3fdadd50e262354b9d9c`.
Its exact comparison tree is `680fc11a47a9fb081fbf108cd007820e45656ab2`.
All 12 `checked_preexisting_tree_anchors` were read as `commit:path`, their Git
blob hashes recomputed from raw UTF-8 bytes and checked against the allowlist.
Their paths, bytes, SHA256 hashes and original Git blobs are retained in
`SOURCE_PINS_AND_STATIC_CHECKS.json`. No main-branch same-name source was used.

The two necessary originals are:

| Path at `680fc11a` | Git blob | Bytes | SHA256 |
| --- | --- | ---: | --- |
| `ImbalancedChen/Part3Gamma0ActualHighCuspTail.lean` | `cfc868b2bfca02d72ff8e0cfcf2657ac091971fa` | 10758 | `953f0c6dad2ef77632a500ecba68ad31e4132ffab014030372aba0c9b119ab9c` |
| `ImbalancedChen/Part3SmallHeightReducedMatrixBounds.lean` | `026feddd88cc6b7575e83896d0eb2b4df8a6a673` | 6374 | `1672d8ecca1bf0dfb1d88d96100e8a1fa0a741e57df15d4e468cae7ffd4b99cf` |

## Confirmed fixed-API mismatch

The review pins mathlib commit
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Its source is available locally in
`goldbach-variable-envelope/.lake/ntfs-source-backups/mathlib`; the relevant
declarations were read from the exact commit's Git objects, independently of
the working files. The two pinned source-file hashes are in the source pins.

At `Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:70`, the global declaration is:

```lean
theorem mul_le_mul_right [MulLeftMono α] {b c : α}
    (bc : b ≤ c) (a : α) : a * b ≤ a * c := ...
```

It takes an inequality and then a multiplier, and returns a multiplied
inequality. It is not a positivity-parameterized equivalence with `.mp`.

At `Mathlib/Algebra/Order/GroupWithZero/Defs.lean:303`, the required declaration is:

```lean
theorem mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflectLE α]
    (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c := ...
```

The same file's line 309 aliases it as `mul_le_mul_iff_of_pos_right`. Thus its
`.mp` removes the common **right-hand positive factor**. The explicit formula
determines the direction; the `left₀` name must not be read as putting that
factor on the left.

The original `(mul_le_mul_right z.im_pos).mp` and
`(mul_le_mul_right w.im_pos).mp` therefore do not match the fixed global API.
This is a confirmed static declaration mismatch, not a reported compiler run.
The similarly named theorem in the separate `Units` namespace is not the
positive-real-factor equivalence needed here.

## Two proof-expression replacements

At `Part3Gamma0ActualHighCuspTail.lean:60`, inside
`im_smul_mul_im_le_one`, replace only:

```lean
apply (mul_le_mul_right z.im_pos).mp
```

with:

```lean
apply (mul_le_mul_iff_left₀ z.im_pos).mp
```

The unchanged target is `(g • z).im * z.im ≤ 1`. The new application asks for
`((g • z).im * z.im) * z.im ≤ 1 * z.im`. The existing hypothesis is
`hsq : (g • z).im * z.im^2 ≤ z.im`; the unchanged final
`simpa only [pow_two, mul_assoc, one_mul] using hsq` supplies exactly that
inequality. The same genuine `SL(2,ℤ)` action and its Möbius denominator are
retained, including the nonzero lower-left hypothesis and integer square bound.

At `Part3SmallHeightReducedMatrixBounds.lean:71`, inside
`reduced_nonzero_lowerLeft_bounds`'s local `hcy` proof, replace only:

```lean
apply (mul_le_mul_right w.im_pos).mp
```

with:

```lean
apply (mul_le_mul_iff_left₀ w.im_pos).mp
```

The unchanged target is `t*c^2*w.im ≤ 1`. The new application asks for
`(t*c^2*w.im)*w.im ≤ 1*w.im`. The original `hmain` is
`t*(c*w.im)^2 ≤ w.im`; the original following `nlinarith` compares precisely
these polynomial expressions. The positive factor is the existing
`w.im_pos`, so no new premise is introduced. All reduced fundamental-domain,
height-band, `SL(2,ℤ)`, numerical and bottom-row interfaces are unchanged.

Both replacements reuse the exact positive-right-factor pattern already in
the independently reviewed eight inverse-mean sources:
`Part3OriginalInversePairBallCount.lean:46` and
`Part3OriginalInversePairDisplacement.lean:92`. These are source-level
precedents; no accepted compiled dependency is inferred. No same-path
published successor repair was found in the local Git history or local output
source search before making this minimal pair of replacements.

## Static scope and delivery

The unified diff `TWO_HEIGHT_API_PROOF_ONLY.patch` contains two single-line
changes. Exact original-text replacement reproduces each postimage. The 19
high-cusp and 6 reduced-matrix top-level declaration headers are byte-identical.
The extraction splits at each top-level declaration and stops before `:=`,
`where`, or its first equation branch; it is a static text check.

The repaired high-cusp source is 10764 bytes, SHA256
`33c5d1de29bb054912a89632da5a6d0e994eb32333f4db032d0d0de3c543aa80`.
The repaired reduced-matrix source is 6380 bytes, SHA256
`c490e339daa77b44d4d69b314681399ca9d699ade254713322d2283d7ac8c70d`.
All statements, definitions, hypotheses, imports and original objects remain
unchanged. No target hypothesis, `sorry`, `admit`, axiom or opaque target is
introduced. The two sites are formal API-expression issues; no new mathematical
argument or omitted mathematical premise is needed for these two repairs.

Only this successor directory was written. The prior P2 freeze, original source,
other code freezes, protected continuation HEAD/index/worktree were untouched.
No Git/GitHub mutation, dispatch, quota check, local Lean/Lake/LSP, environment
setup, project helper, fixture, proofguard, runtime or certificate execution was
performed. All evidence above is source/static/JSON/hash/read-only Git evidence.
