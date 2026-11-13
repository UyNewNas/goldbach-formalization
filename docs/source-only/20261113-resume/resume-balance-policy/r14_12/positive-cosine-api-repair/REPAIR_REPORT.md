# Canonical positive cosine profile: additive API repair

**SOURCE ONLY / UNCOMPILED.** Compiled modules: **0**; kernel-verified modules:
**0**. This package changes one proof expression in `hyperbolicProfile`.

The exact canonical source is a6 commit
`a6aec20e831aa7f905533bec69fd0f86cd2bf9b1`, path
`docs/source-only/20261112-resume/t04/positive-test-api-selection/ImbalancedChen/Part3ActualPositiveCosineProfile.lean`,
Git blob `337f168b4194fd0f0aa79bd79705c9ad703b84a3`, 7377 bytes, SHA256
`d4866d43e1493b3356ee1b9d143a3d4c0c1f12a2d2f2f2e637101370d576b92c`.
The exact same tree's `positive-test-api-selection/SELECTION.json` explicitly
selects that postimage. Its SHA256 is
`126c0b0f893b36f3ae564cd255cd0d28a84293bd7e285a2542ccc577c6035f9f`.
The older 7273-byte blob `1d8fc4fdc7bd73ee9681e573dba35f5d70d98b67` is not used.
The earlier canonical division-API repair remains intact.

At source line 123, the existing proof has the shape:

```lean
(norm_add_le _ _).trans (add_le_add_left h _)
```

Here `h` is the unchanged nested `by` proof, using `hs : |sinh u| ≤ cosh u`, of
the bound on the **second** summand's norm. The preceding original jet is
`A (cosh u) + (sinh u : ℂ) * B (cosh u)`. Thus the required intermediate is:

```lean
‖A (Real.cosh u)‖ + ‖(Real.sinh u : ℂ) * B (Real.cosh u)‖ ≤
  ‖A (Real.cosh u)‖ + Real.cosh u * ‖B (Real.cosh u)‖
```

The fixed-host operation is checked from mathlib commit
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, exact Git object
`Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean`, blob
`8879ea063dc1d4d7972dcc289ec56c5eef90fc8d`, SHA256
`5e294a0e96698d3537095d94dda4ccf3bc7304ad8772f39e25d712a390281337`.
Lines 202–205 explicitly generate the additive theorem:

```lean
@[to_additive (attr := gcongr high) add_le_add]
theorem mul_le_mul' [MulLeftMono α] [MulRightMono α]
    {a b c d : α} (h₁ : a ≤ b) (h₂ : c ≤ d) :
    a * c ≤ b * d := ...
```

Consequently `add_le_add` takes inequalities in the two original summand
positions and produces `a + c ≤ b + d`. The repaired expression is:

```lean
(norm_add_le _ _).trans (add_le_add le_rfl h)
```

`le_rfl` preserves the first norm, while the original `h` bounds the second.
There is no reliance on summand commutation or inference of a different fixed
addend. The actual nested `h` spans several source lines, so the minimal diff
changes the opening and closing wrapper lines of this **one proof expression**;
all bytes inside `h` and all other source bytes remain unchanged.

The 18 declaration headers, including attributed/private declarations, are
byte-identical. Imports, function formulas, parameters, hypotheses, numerical
constants, seminorms, Schwartz objects, cosine/Fourier normalization and the
original derivative argument are retained. No hypothesis, axiom, opaque
target, `sorry` or `admit` is introduced. This is a formal additive-API
expression repair, with no new mathematics or substantive gap identified.

The postimage remains 7377 bytes, SHA256
`6e52e161c7541790b082d2df8d9643c58b35241238dd7a97b5ce2910c6231611`.
The exact wrapper substitution reconstructs the whole file. Pins and the
minimal diff are frozen with this report for independent 05 source review.

Only this new directory was written. No canonical original, old same-basename
copy, earlier freeze, production source or protected dirty continuation was
modified. The P2 two-module successor is a separate freeze. No local
Lean/Lake/LSP, setup/environment, project helper, proofguard, fixture,
runtime/certificate, Git/GitHub mutation, CI, quota check or agent spawn was
performed. These are static source/hash/read-only Git checks, not compilation
or kernel verification.
