# Chen Part 5 — LargeSieve LogPowerBounds leaf acceptance

## Result

`MathlibNt.AnalyticNumberTheory.LargeSieve.LogPowerBounds` is accepted as one independent leaf of the real Liu–Pan/S1 supplier chain. It is distinct from the previously accepted `MathlibNt.Analysis.LogPowerBounds`. Fixed source SHA256: `b4bc854d004b1fc4385b96794ba5643780494201d506925c07506fa91798200d`. Strictly compiled object SHA256: `d52f560c960a917755a67bd10549ccb324c5d97f8296e8519c6b995685899a96`.

The official frontend strict compile passed in 6.505 s; stock `leanchecker` replay passed in 4.967 s; the complete defining-module audit passed in 61.001 s. The compiler enumerated two theorem declarations: the requested public theorem plus one generated/private proof declaration. There are no unsafe or own axiom declarations and the transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Compiler-confirmed type

```lean
AnalyticNumberTheory.LargeSieve.log_pow_le_sqrt_eventually :
∀ (k : ℕ), ∀ᶠ (N : ℕ) in Filter.atTop, Real.log ↑N ^ k ≤ √↑N
```

This is the actual eventual payment `(Real.log N)^k ≤ Real.sqrt N` for every fixed natural exponent `k`. It is used by the pointwise Siegel–Walfisz and standard Bombieri–Vinogradov branches feeding the low-conductor endpoint. It supplies no distribution estimate by itself.

The three direct imports are fixed mathlib objects and were reused only after exact source/object hashing; they were not recompiled, replayed, or re-audited here. No proof source was patched and no production file was changed.

## Supply status

One shortest actual path to the current first-term target is

`LargeSieve.LogPowerBounds → DirichLTwistedNonquadraticPointwiseSiegelWalfisz → LandauSiegelToLowSWSource → LandauSiegelToStandardBVCanonicalSmoothing → FourFactorUnconditionalEndpoints → PanWangDingLowPrimePrefix → PanWangDingLowMovingPrefix → PanWangDingLowEndpoint → Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly → S1BetaGeometry → S1BetaPaidLower`.

This batch does not accept those downstream modules. The smallest remaining ready leaf in the current closure is `MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFoundation`, source SHA256 `ab7d737510d353e6f7791ed24a8d77be7a6ec80beaec617dcf6dd21da2bc0787`.

`CurrentChenInitialMean`, the complete eleven-term mean, and `hLower` remain open; `(33/4) * Real.log 3` remains only an independent first-term candidate. The final weight scale remains `4c = 49044063/6250000 = 7.84705008` because `W_N ≤ 4*D12(N)+error`.

Evidence is under `verification/parts/p5/round8/largesievelogpowerbounds/`. Root CI is tracked separately. Receiving parts: P5 and P0.
