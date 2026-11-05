# P3.6 — original Point mixed derivative to complex Frechet Fourier

**State:** SOURCE_ONLY, UNCOMPILED, KERNEL-UNVERIFIED. P3.6 remains YELLOW.

## Exact recovery

- Working branch: `chatgpt/p3-internal-original-w-20261105`.
- Verified starting branch HEAD: `09375f70f6dd688c82428c773bb6bed1cd95ddcb`.
- Previous packet: `docs/source-only/20261105-p3-fourier-point-coordinate-bridge/`.
- Manuscript pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/modules/distribution-prime-product-completion-20261010.txt` §4 (F) and `paper/source/manuscript-body.tex`.
- Fixed mathlib pin: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Neither toolchain nor dependencies changed.

## Genuine internal mathematical increment

The previously identified `Point d` real-valued `mixed (doubled S)` was not yet the complex-valued function used in the genuine Fourier theorem. `P3FourierRealComplex.lean` now defines `complexChartLift` by the **real-linear** continuous map `Complex.ofRealCLM` after the existing exact `chartLift`. The pinned mathlib theorem `ContinuousLinearMap.iteratedFDeriv_comp_left` gives the actual equality

```
iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ chartLift w) x
  = Complex.ofRealCLM.compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (chartLift w) x)
```

under ordinary finite-order `ContDiff`. This is differentiation over ℝ, **not** an unjustified holomorphic derivative. The evaluated derivative is the complex cast of the actual real derivative. It is then paired with the older exact ordered-coordinate bridge, retaining both appearances of every coordinate in `doubled S`.

The packet adds `actualMixedFamily_eq_complexFrechet` and its function-level version; therefore, on this explicit smoothness domain, the actual original mixed-derivative integrand **is** the complex Frechet directional integrand. `actualD_eq_complexFrechet_D` identifies their finite L1 derivative sums on exactly the same Euclidean Fourier measure. It does **not** conflate this with the independent `Point d` measure used in originalWD.

Finally `actualMixed_fourier_frechet` applies the existing *pinned genuine* `subset_frechet_fourier` theorem to the actual original mixed function. It assumes only real finite-order `ContDiff` and integrability of the complex-valued iterated Frechet derivatives; it does **not** use a premise equivalent to the Fourier-IBP identity, target PP discrepancy, or a new axiom. This is still conditional on real analytic admission of the physical W_T families.

## Real verification, with trust boundary

- Compared prior `P3FourierPointCoordinateBridge`, `P3FourierFrechetIBP`, `P3FourierDPointwise`, and the pinned manuscript §4.
- Read pinned mathlib `Mathlib/Analysis/Calculus/ContDiff/Basic.lean` to confirm `ContinuousLinearMap.iteratedFDeriv_comp_left`, and `Mathlib/Analysis/Complex/Basic.lean` to confirm `Complex.ofRealCLM_apply`.
- Corrected the candidate after an additional source lookup: `ContinuousLinearMap.compContinuousMultilinearMap_coe`, not the nonexistent `compContinuousMultilinearMap_apply`, is the pinned simplification lemma. The amended source blob SHA is in `REGISTRY.json`.
- Local deterministic Python finite-monomial tests: **735/735**, for dimensions 1–3 and ordered derivative lengths 0–6, checking ordinary repeated partial differentiation and exact real-to-complex value embedding. These do NOT validate Lean elaboration.
- Source escape-token and delimiter scan passed. Neither Lean/Lake, kernel replay, CI, transitive axiom audit, Codex nor heavy numerical producer was run. `VERIFY.lean` is not an execution receipt.

## Remaining manuscript-internal obligations

1. Combine the genuine Fourier formula above with the already drafted signed 2S frequency product, checking every minus sign and 2π factor, to discharge `CoordinateFourierIBP` without assuming it.
2. Prove the measure normalization between `EuclideanSpace` and `Point d` and identify the actual `originalWD` integral. Same-space D above does not suffice.
3. Verify real `W_T` families have the required uniform smoothness/integrability in the permitted logarithmic mixed-Euler class.
4. Pay full Fourier L1 and quantitative H-box tail, including T-uniformity, and feed it into the same-ρ signed modulus sum.
5. Pay full arithmetic modulus mass and product=T exception separately, then causal, HB full-source, empty Gamma mother word, high-rank/enhanced PP obligations.

**External M** remains recorded only in `EXTERNAL_INPUTS.json`, not implemented or promoted to an axiom. No changes to the excluded 87-domain parent node, production modules, manuscript, PRs, other automations or toolchain.
