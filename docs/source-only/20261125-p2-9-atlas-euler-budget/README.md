# Fixed causal atlas times the original Gamma5 profile

**Status: SOURCE_ONLY_UNCOMPILED. Formal, kernel, endpoint and new native credit: 0.**

This package supplies the missing global smoothness and mixed Euler budget for a fixed original causal atlas weight on the separate old-prime coordinates, multiplied by the unchanged Gamma5 physical profile. It constructs no smooth realization of an arbitrary discrete selected-history set.

## The actual function

For fixed old and tail ranks `k,r`, the physical coordinate order remains
`Fin (k + (2 + r))`: all old slots, two fresh slots, then the complete rough tail. Write `old(i)=Fin.castAdd (2+r) i`. The new function is

\[
 \Phi(v)=\operatorname{finPhysicalProfile}(\log Q,N,h,b)(v)\,
 \operatorname{readout}(P,A)
 \left(i\mapsto\frac{\log(\operatorname{positiveArg}(b/2,v_{\rm old(i)}))}{\log N}\right).
\]

Here `P`, `readout`, its finite atom code and the positive argument are the existing original definitions. No primality, coprimality, discrete selected-history indicator or additional arithmetic filter is inserted.

For `b>0`, `contDiff_atlasProfile` proves global `ContDiff ℝ ∞` on the entire real coordinate space. The public theorem `atlasProfile_eq_original_weight` proves, at every real point,

\[
 \Phi(v)=\operatorname{finPhysicalProfile}(\log Q,N,h,b)(v)\,
 \operatorname{readout}(P,A)
 \left(i\mapsto\frac{\log v_{\rm old(i)}}{\log N}\right).
\]

This is an equality of products. It does not assert that an unclamped logarithm is smooth at zero. At a zero profile both products vanish. At a nonzero profile the existing support theorem gives every coordinate strictly above `b/2`, so the existing clamp is exactly the original coordinate. The new function is nonnegative and its nonzero support is contained in the original profile support.

## Uniformity actually proved

For fixed `P`, finite rank ceiling `K`, positive physical width `h` and derivative order `m`, the source proves

\[
 \exists C\ge0\;\forall k,r,\ k+2+r\le K\;
 \forall N\ge2\;\forall\log Q\;\forall b>0\;
 \forall A,w,v,\quad
 |w|\le m\Longrightarrow |\operatorname{eulerWord}_w\Phi(v)|\le C.
\]

The constant precedes the target, total level, floor, accepted atom subset, Euler word and physical point. It is uniform in every accepted subset of the fixed finite atlas. It need not be uniform as the atlas or the fixed width changes.

The public targets are:

- `contDiff_atlasProfile` and `atlasProfile_eq_original_weight`: global smooth extension and exact original-weight product.
- `atlasProfile_nonneg` and `atlasProfile_nonzero_original`: positivity and inherited support.
- `atlasProfile_chart_tensor_budget`: all real multiplicative-flow bases and all mixed Fréchet tensors at each fixed order.
- `atlasProfile_mixedEuler_budget`: the unchanged original list-fold Euler operators.
- `atlasProfile_boundedRank_mixedEuler_budget`: one constant for the fixed finite collection of old/tail splits.
- `atlasProfile_family_mixedEuler_budget`: natural `C>0` and logarithmic exponent `B=0` in the original `Family.mixedEuler` convention, on integer targets `N≥2`.

The last result is a supplier for that derivative field. It is not a new `Family` instance, and it does not replace the existing sparse-rank or low-target zero construction.

## Why the global derivative estimate is valid

The proof uses the existing analytic estimates, with only finite combinations and coordinate identities added.

1. Each fixed original atlas mask is globally smooth and compactly supported. Its compact support supplies two finite exterior intervals on which it is zero. The existing `plateau_bound` then gives all scalar derivative bounds. Smoothness alone is never used as a global bound.
2. On a positive multiplicative flow, the old coordinates become
   \((\log v_i+u_i)/\log N\). For `N≥2`, the slope is at most `1/log 2`. The existing generic `affine` and `prod` bounds supply every fixed atom.
3. Each atom is either retained or replaced by zero. The source explicitly takes the finite sum over all atoms using the existing `add` bound. This is what makes the constant uniform in `accept`. Rank `k=0` retains its unique empty-coordinate atom.
4. The existing generic `mul` estimate combines that readout budget with the existing Gamma5 `finPhysicalProfile_chart_tensor_budget`. The old Gamma9–21 `common_chart_budget` is not applied to Gamma5.
5. If any base coordinate is zero or negative, it remains nonpositive along its whole multiplicative flow. The original Gamma5 floor support makes the entire product identically zero there, including derivative order zero. The global result is therefore not restricted to positive points.
6. The original `norm_bound_at_zero` converts chart tensors to the original Euler words. Finite sums over orders and over `k,r≤K` are chosen before the moving parameters. The natural constant conversion follows the existing geometric-family convention.

No new Buchstab, prime-distribution, chain-rule estimate, general derivative-product theorem, or general extension mechanism is introduced.

## Exact sources and ownership

The complete source bindings are in `REGISTRY.json`. The principal original suppliers are:

| Supplier | Exact Git blob |
|---|---|
| Joint query readout | `d3141bf52bb42f486d8d4f1c0e4924fe0ab480ad` |
| Causal smooth atlas | `eecf0a5c76e32e5bde733e55011f3a62686b0509` |
| Generic classical Euler bounds postimage | `d4159eea6e96427bca0ad79a9865d4ccc6e247d2` |
| Existing Gamma5 Euler word budget | `37f17bea5ff8988f0b3853d1da45acf9560f490d` |
| Current accepted AllRank Euler budget | `4197fc1c985f55643418ac0ca0837d2951d9f998` |
| Current original Family core | `51c9ec8b44acfd77d2c40a75c1792d90bea5e464` |

The current original Family full-owner postimage is `a32b53fa19810f21d6e3e990d59ab113202d7ec3`, read at root's published commit `a1c18579e5702ce224076e7cd86ffe74d2b47d96`. This current postimage must take priority over all older versions of the full owner; the old owner must not redeclare the extracted structure. The existing scalar/Euler owner postimages must likewise be selected coherently when their original heavy owners are reachable.

No existing source is modified. No extraction or owner migration is performed here. The full receiving closure of the old atlas/history owners together with the thin accepted cores has not been reconstructed or qualified by this package. Accepted supplier bytes do not confer acceptance on this new consumer or its entire import closure.

## Manuscript scope and remaining work

The source implements the bounded geometric derivative part of positive smooth approximation in the frozen 1106 manuscript: `argument.tex`, lines 359–374 and 400–407, together with the retained old coordinates/common level in `sieve-appendix.tex`, lines 494–513, and the order of fixing finite queries before increasing `N` at lines 1090–1101.

The missing step addressed here is finite analytic and coordinate glue. It is a formal elaboration of those fixed-geometry statements, not a new manuscript hypothesis.

The separate remaining questions include identifying the fixed atlas readouts with the intended actual selected-history masks, retaining the simultaneous causal/query semantics, transporting the required weighted ordinary-mass approximation, and supplying the later distribution/PP and original-J licences. The previously proved arbitrary-`B` raw mass comparison supplies none of those smooth realizability statements by itself.

The 29 H247/native-Wu binder endpoints remain a separate open sufficient-condition/compatibility branch. Their necessity for the manuscript's actual enhanced finite-family conclusion has not been established; they are not listed as 29 mandatory mainline obligations.

## Validation in this increment

The source was checked for the prohibited shortcuts and reviewed in full independently by `/root/p29_review`. Both root and the independent reviewer read the complete source and found no mathematical blocker in clamp removal, nonpositive-flow vanishing, the explicit finite-atom bound, rank zero, or quantifier order. This is source review only.

No Lean compilation, object reuse, kernel replay, owned-declaration audit, cloud job, branch/ref update or active-tree installation was performed. Only exact source/document Git blobs were created for root to integrate.
