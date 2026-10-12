# Chen Part 5 — DirichletLFoundation leaf acceptance

## Result

`MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLFoundation` is accepted as one independent leaf of the real Liu–Pan/S1 supplier chain. Fixed source SHA256: `ab7d737510d353e6f7791ed24a8d77be7a6ec80beaec617dcf6dd21da2bc0787`. Strictly compiled object SHA256: `c7d4fe0a8609c6520fdd680233ce56655808643530648164ec7dbd19ed688215`.

The official frontend strict compile passed in 65.363 s; stock `leanchecker` replay passed in 5.727 s; the complete defining-module audit passed in 73.129 s. The compiler enumerated exactly four theorem declarations, all requested public theorems. There are no private/generated declarations, unsafe declarations, or own axiom declarations. The transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Compiler-confirmed types

```lean
DirichletCharacter.lFunction_entire_of_ne_one :
∀ {q : ℕ} [inst : NeZero q] {χ : DirichletCharacter ℂ q}, χ ≠ 1 → Differentiable ℂ (DirichletCharacter.LFunction χ)
```

```lean
DirichletCharacter.completedLFunction_entire_of_ne_one :
∀ {q : ℕ} [inst : NeZero q] {χ : DirichletCharacter ℂ q},
  χ ≠ 1 → Differentiable ℂ (DirichletCharacter.completedLFunction χ)
```

```lean
DirichletCharacter.LSeries_twist_vonMangoldt_eq_neg_logDeriv_LFunction :
∀ {q : ℕ} [inst : NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
  1 < s.re →
    LSeries ((fun n => χ ↑n) * fun n => ↑(ArithmeticFunction.vonMangoldt n)) s =
      -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
```

```lean
DirichletCharacter.continuousOn_neg_logDeriv_LFunction :
∀ {q : ℕ} [inst : NeZero q] {χ : DirichletCharacter ℂ q},
  χ ≠ 1 →
    ContinuousOn (fun s => -deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)
      {s | DirichletCharacter.LFunction χ s ≠ 0}
```

These are types extracted from the elaborated compiler environment, not source-only signatures. They establish the nonprincipal entire L-functions, the von-Mangoldt twist/logarithmic-derivative identity on `1 < s.re`, and continuity on the actual nonzero locus.

The unique direct import is `Mathlib.NumberTheory.LSeries.Nonvanishing`. Its fixed source and object were reused only after exact hashing; it was not recompiled, replayed, or re-audited in this batch. No proof source was patched and no production file was changed.

## Supply status

One actual path from this leaf to the current first-term target is

`DirichletLFoundation → Chen1973Lemma6Equations16And17 → Chen1973Lemma6Equation19 → Chen1973Lemma6Equation19MomentTransport → Chen1973Lemma6Equation19UniformMoments → ChenLiuCoprimeProducerShort → ChenLiuCoprimeProducerHalfStepContour → ChenLiuCoprimeProducerPerronAssembly → ChenLiuCoprimeProducerHighAggregate → Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly → S1BetaGeometry → S1BetaPaidLower`.

This batch does not accept those downstream modules. After installing this object, the actual Liu–Pan closure was recomputed as 314 modules, with 282 missing objects and 20 ready leaves. Its smallest remaining ready leaf is the **uncompiled candidate** `MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedPointwiseSWPaymentCore`, source SHA256 `3798b1a9798e1a7390ba5d3ba879287e6c1a466b4f91f39a434f3f1bc41b65d2`; it has 20 source lines and depends on the already accepted `LargeSieve.LogPowerBounds` leaf.

`CurrentChenInitialMean`, the complete eleven-term mean, and `hLower` remain open; `(33/4) * Real.log 3` remains only an independent first-term candidate. The final weight scale remains `4c = 49044063/6250000 = 7.84705008` because `W_N ≤ 4*D12(N)+error`.

Evidence is under `verification/parts/p5/round9/dirichletlfoundation/`. Root CI is tracked separately and was not run for this single-module checkpoint. Receiving parts: P5 and P0.
