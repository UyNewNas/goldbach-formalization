# A fixed causal atlas in the original Gamma5 Family

**Status: SOURCE_ONLY_UNCOMPILED. Formal, kernel, endpoint and new native credit: 0.**

This package constructs an instance of the unchanged original
`P5Z.AdmissibleAllRankIntegerGeometricFamily.Family K` by multiplying the existing Gamma5 geometric ambient by the preceding fixed-atlas readout. It completes the all-target Family assembly for that particular multiplier. It does not identify an arbitrary discrete selected-history set with a smooth weight.

## Exact constructor

The new constructor is

`atlasFamily P K k r a width logQ accept ha hw hw1 hkr : Family K`,

where `P : Plan` is fixed, `logQ : ℕ → ℝ`,
`accept : (T : ℕ) → ((Fin k → Code P) → Prop)`,
`0<a`, `0<width≤1`, and `k+2+r≤K`.

The accepted atom subset may vary with the natural target. The derivative estimate already holds uniformly over every accepted subset of the fixed finite atlas, so the same constant works before the complete function `accept` is supplied. This parameter uniformity is not a statement that an arbitrary arithmetic or discrete history selection is an admitted fixed geometric mask.

The constructor starts from the existing

`A := P2FiniteMarkedGamma5GeometricFamily.geometricFamily K k r a width logQ ...`

and uses a record update. Its unchanged scalar fields are therefore exactly

\[
 a_* = a,\qquad \mathrm{lower}=\tfrac12,\qquad
 \mathrm{upper}=\exp(1).
\]

## Minimal new ambient

The source defines

\[
 \mathrm{atlasAmbient}(T,d,v)
 =\mathrm{oldAmbient}(T,d,v)\,M(T,d,v).
\]

At `d=k+(2+r)`, `M` is the preceding original readout on the separate old coordinates, transported along that rank equality. At every other rank, `M=1`. The multiplier contains **no scale gate**. The old ambient remains solely responsible for the original rank and low-scale zero branches.

The public function equality `atlasAmbient_at_rank`, and its Family-facing counterpart `atlasFamily_at_rank`, state that at the active rank and above the original `scaleThreshold a`, the entire real function is exactly

`atlasProfile P (accept T) (logQ T) (T : ℝ) width ((T : ℝ)^a)`.

This is equality of functions on the whole real coordinate space, not only equality at positive or prime tuples. The previous global clamp result and Euler budget apply without changing the old, fresh or tail slots.

## Fields reused rather than reproved

- **Support:** nonzero new ambient implies nonzero old ambient by the first factor of a nonzero product. The constructor directly calls `A.support`. The floor and complete-product proofs are not reconstructed.
- **Finite prime support:** the new prime support is a subset of the exact old finite prime support. The constructor directly applies `(A.finitePrimeSupport T d).subset`.
- **Low-scale and inactive-rank zeros:** the source invokes the existing `ambient_zero_below_threshold` and `ambient_zero_of_rank_ne` and multiplies by zero. It does not define a replacement sparse-rank or scale truncation.
- **All-target smoothness:** the active large-target branch uses the preceding global `contDiff_atlasProfile`. The inherited zero branches are constant functions.
- **Mixed Euler field:** one natural constant is taken from `atlasProfile_family_mixedEuler_budget` before `a, logQ, k, r, accept, T, d, w, v`. At the active natural target, the old threshold theorem gives `1<(T:ℝ)`, hence `2≤T`, so that preceding budget applies. The inherited zero branches use the existing `eulerWord_zero_eq`. The original logarithmic exponent is `B=0`.

In particular, `T=0` and the corresponding `b=0^a` are handled by the old zero gate. No smoothness of the isolated clamp factor at zero floor is asserted or required. Empty old coordinates, an empty tail, repeated prime values and all inactive Family ranks remain allowed.

The source also provides `atlasAmbient_nonneg` and `atlasFamily_nonneg` for every real point and every target.

## Exact inputs and owner selection

| Input | Exact Git blob |
|---|---|
| Existing accepted geometric Family | `b86d39095e77a18f23598c45466aa32c89aa7f98` |
| Preceding source-only Atlas Euler budget | `51dfcfd07e9ce447a3e79ba25d34627a61f47de0` |
| Existing original Family core | `51c9ec8b44acfd77d2c40a75c1792d90bea5e464` |
| Existing AllRank / zero-Euler supplier | `4197fc1c985f55643418ac0ca0837d2951d9f998` |

The inherited precise source map is the preceding atlas-budget REGISTRY,
blob `cbeccf170c1e729e2a4b0ada1fcdf66a885d7632`. The full Family owner must select the current postimage
`a32b53fa19810f21d6e3e990d59ab113202d7ec3` in preference to every earlier full-owner version. The existing scalar/Euler postimages specified there remain required if reachable.

This package changes no existing source, performs no new extraction and selects no TupleCount source. It does not give acceptance credit to the previous atlas consumer or to the full mixed import closure merely because the base geometric Family was accepted.

## Manuscript scope

This is the finite Family assembly associated with the frozen 1106 manuscript's fixed positive geometric family in `argument.tex`, lines 359–374, and smooth outer approximation at lines 400–407. The retained individual coordinates/common level and the order of choosing a finite family before increasing `N` are in `sieve-appendix.tex`, lines 494–513 and 1090–1101.

The new work is a concrete record-and-coordinate assembly. No new analytic estimate or manuscript hypothesis is added. The target rank hypothesis is the same fixed split admission used by the existing constructor; this package does not assert a new actual-history rank theorem.

The actual selected-history mask identification, simultaneous causal/query semantics, ordinary-mass transport for those masks, original-J and distribution/PP licences remain separate. Neither arbitrary-`B` mass comparison nor uniformity over the finite atlas's accepted subsets supplies those conclusions.

The 29 H247/native-Wu binder endpoints remain a separate sufficient-condition/compatibility branch whose necessity for the actual enhanced finite-family manuscript conclusion has not been established.

## Validation

The author and `/root/p29_review` independently read the complete final 205-line source and found no mathematical blocker in support inclusion, dependent rank transport, preservation of the original scale gate, all natural targets, or the order of the uniform constants. The fixed Mathlib source was also read to use the actual `Fin.cast_eq_self` API; this proof-only correction changed no statement. Compilation is still required for Lean API and elaboration checks.

No compilation, kernel replay, owned audit, cloud job, existing-object modification, active installation, commit or ref update was performed. Only Git blobs were created for root's source-only integration.
