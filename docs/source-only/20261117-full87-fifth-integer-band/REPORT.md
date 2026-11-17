# P1.4 — original fifth-exclusive frozen integer exponent band

Baseline: `b55a247512ae79c98aae9345b08abb86568321a7`, verified identical with previous P1.4 branch before fork. Independent branch: `chatgpt/p1-full87-fifth-integer-band-20261117-2110`.
Lean: `P4AOriginalFull87FifthIntegerBand.lean`; created at `cba9887007e466e434ac24955405d176266f4f62`, arithmetic monotonicity side goals made explicit at `7bddcdef3b27e1ede4deb3b4d7f07370f46d4dc7`.
Source git blob: `d8be09df26243740f715f85b985cf45ba434a984`.

## New manuscript-side mathematical step

The previous actual-source theorem gives, for a genuine fifthExclusive occurrence of the original `actualFifthSixthWithoutBoth` in its original shared-rank-four parent, and for arbitrary original-policy evaluation R:

```
sixthPositiveContinuation R ... fifth.selectedAfter ... != 0
  ==> X^5 < (N^epsilon)^5 * b5^6.
```

This packet **now proves the previously only paper-calculated frozen exponent payment** (as a candidate Lean proof):

```
N > 1, epsilon <= 1/500, X >= N^(3/5),
X^5 < (N^epsilon)^5 * b5^6
  ==> N^299 < b5^600.
```

The proof is not a mere re-expression of a sum or a new filtered list. It uses both quantitative frozen inequalities:
- `N^3 <= X^5`, by raising `X >= N^(3/5)` to the fifth power.
- `(N^epsilon)^500 <= N`, by `500 epsilon <= 1` and monotonicity of `N^t` for `N>1`.

Raise the previous large-fifth power necessity to the 100th power, obtaining `N^300 < (N^epsilon)^500 * b5^600 <= N*b5^600`; cancel the strictly positive N. No beta sign, occurrence, cap, or fourth-parent history is discarded. This is exactly the strict real exponent lower band `b5>N^(299/600)`, expressed with NATURAL exponents to avoid fractional-power ambiguity.

`actual_fifth_exclusive_nonzero_requires_integer_band` instantiates the arithmetic lemma with the actual fifth-exclusive event, original Rosser attachment and unchanged sixth-positive continuation. It is a *necessary support band*, NOT a positive saving: the interval above the strict cutoff may retain arbitrary signed mass.

## Verification and boundary

SOURCE_ONLY / UNEVALUATED / UNCOMPILED. Local `lean --version`, `lake --version`, and `elan --version` each returned exit 127 (`command not found`). No pinned dependency checkout or compile; theorem tactics may not elaborate. Static text scan of the 127-line source found no forbidden proof escapes; this does not replace Lean validation. No kernel replay, transitive axiom audit, real archive replay or independent review.

Only task proof-packet files changed; no main/master, merge, force push, CI, Codex, user machine or toolchain upgrade. Frozen manuscript `9731290e8f53cffda44129906cde6a965eaa869b`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; Lean 4 v4.33.0-rc1; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `09b97db5764ade1246bfb77206baa1b124760958`; c=`49044063/25000000` and K=`8452171/1250000` unchanged.

## Next exact proof obligation

Quantify the actual signed same-rho contribution of genuine fifthExclusive histories with `N^299 < b5^600`, inside the available physical modulus range, without applying a PP bound to high-q moduli outside its own level. In parallel, handle direct `sixthFromBoth` sixth-even full a*b6 terminals, which are not subject to this fifth-exclusive event theorem. Preserve outside/producer/licensed-outside invoices exactly once. P1.4 remains YELLOW.
