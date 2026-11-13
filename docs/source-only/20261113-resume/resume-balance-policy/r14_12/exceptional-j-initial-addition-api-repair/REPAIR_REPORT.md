# Initial exceptional-J average: canonical additive API repair

**SOURCE ONLY / UNCOMPILED.** Compiled modules: **0**; kernel-verified modules:
**0**. This successor replaces one proof expression and no other source bytes.

The canonical original is publication
`49a6978d28dabbb7eacaa73c872bb15238e7b4af`, path
`docs/source-only/20261113-resume/resume-balance-policy/r14_09/avgj-next/Part3OriginalExceptionalJInitialAverage.lean`.
Its Git blob is `d3b96d8b765d0167ae125accd5d20e67da8569a2`, 6540 bytes, SHA256
`c11c2181a446a90f971f58651aec383e4f0fffe1b760b701e181800fa2747339`.
The exact object at latest source commit
`484d8ffc8f79e7c213b33ae86a8d960cd4da6de4` is byte-identical to that original.

The frozen source-index snapshot used immediately before 484's publication
records this same path, original 49 commit, blob, size and hash. Its recorded
branch head is 23fa; the current 484 Git object was checked separately. The
original `avgj-initial-pair-publication/SOURCE_SELECTION.json` also records the
same blob/hash, and the original author freeze agrees. Pins and exact receipt
rows are retained in `SOURCE_PINS_AND_STATIC_CHECKS.json`. No same-basename old
copy was substituted. Git history for this published path only showed the 49
publication, and the bounded local source search found no existing corrected
`add_le_add le_rfl hratio` variant before this successor was written.

At original line 105, in `initial_average`'s local `base` proof, the original
inequality is:

```lean
hratio : M / (z.val : ℝ) ≤ M / Q
```

The original `signed_row` bound has the factor `1 + M / (z.val : ℝ)`, while the
local target has `1 + M / Q`. The first summand must stay exactly 1, and the
second is bounded using the existing `hratio`. Replace only:

```lean
(add_le_add_left hratio 1)
```

with:

```lean
(add_le_add le_rfl hratio)
```

The fixed mathlib revision is
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. In
`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:202–205`, the explicit
`@[to_additive ... add_le_add]` on `mul_le_mul'` generates the additive theorem
with signature `(h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d`.
The exact host source blob and SHA256 are recorded in the pins. Thus `le_rfl`
occupies the unchanged first-summand position, and `hratio` occupies the second;
the resulting inequality is precisely `1 + M/z ≤ 1 + M/Q`, with the source's
actual coercions. This also follows the already independently reviewed T04
cosine-profile additive API repair pattern, without reusing that unrelated file.

The same outer `mul_le_mul_of_nonneg_left ... cn`, cardinality estimate, final
`mul_le_mul`, positivity facts and `h.trans` remain byte-for-byte unchanged.
All three named declaration headers, all imports, the local instance, theorem
parameters/hypotheses, scales, constants, original infinity frame, native
Fourier coefficients, phase, finite sums and original weight range remain
unchanged. No extra premise, target hypothesis, axiom, opaque target, `sorry`
or `admit` is introduced. This is a formal additive-API expression issue;
no new mathematics or substantive gap is asserted. The original initial-range
theorem remains an initial-range theorem; no full AvgJ or 7/32 credit is claimed.

The repaired source is still 6540 bytes, SHA256
`374c8fc1a95de5f32fe20c19ae4ffd66406cb4c60f2adc98d47bebdc87b6c9d9`.
Exact replacement of the one expression reconstructs the entire postimage.
The original 49 freeze, latest published source, all prior repair freezes,
09's dependency selections and protected dirty continuation were not modified.
Only this separate successor directory was written.

No local Lean/Lake/LSP, setup/environment, project helper, producer, guard,
fixture, runtime/certificate, Git/GitHub mutation, CI, quota check or agent
spawn occurred. All checks are static source/hash/JSON/read-only Git checks.
Independent 05 review must precede any downstream dependency update.
