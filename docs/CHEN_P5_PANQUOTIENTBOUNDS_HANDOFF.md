# Chen Part 5 — PanQuotientBounds leaf acceptance

## Result

`MathlibNt.AnalyticNumberTheory.LargeSieve.PanQuotientBounds` is accepted as one independent leaf of the real `S1BetaGeometry → LiuPanPrimitiveLedgerAssembly` supplier chain. Fixed source SHA256: `3ba941bd1dc462ef9c535aafd6e8ad795a370ec1f69389f11201df45c84afa65`. Strictly compiled object SHA256: `15aec41bf8e92a2c7b7a840e56b224f69dc7704d27dbf378f26c895ceae69219`.

The official frontend strict compile passed in 211.867 s; stock `leanchecker` replay passed in 4.486 s; the complete defining-module audit passed in 86.413 s. The compiler enumerated three theorem declarations: the two requested public theorems plus one generated/private proof declaration. There are no unsafe or own axiom declarations and the transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Compiler-confirmed types

```lean
AnalyticNumberTheory.LargeSieve.PanQuotientBounds.eventually_nat_div_quarter :
∀ᶠ (N : ℕ) in Filter.atTop, ∀ (a : ℕ), 1 ≤ a → ↑a ≤ ↑N ^ (2 / 3) → ↑N ^ (1 / 4) ≤ ↑(N / a)

AnalyticNumberTheory.LargeSieve.PanQuotientBounds.eventually_quotient_parameters :
∀ (b : ℝ) (M : ℕ),
  ∀ᶠ (N : ℕ) in Filter.atTop,
    ∀ (a : ℕ),
      1 ≤ a →
        ↑a ≤ ↑N ^ (2 / 3) →
          M ≤ N / a ∧
            0 < Real.log ↑N ∧ 0 < Real.log ↑(N / a) ∧ Real.log ↑N ≤ 4 * Real.log ↑(N / a) ∧ 4 ^ b ≤ Real.log ↑(N / a)
```

These theorems establish the actual eventual quotient-size and logarithmic conditions for every natural `a` with `1 ≤ a` and `(a : ℝ) ≤ (N : ℝ)^(2/3)`: the integer quotient dominates `N^(1/4)` and every fixed `M`; both required logarithms are positive; `log N ≤ 4*log(N/a)`; and `(4 : ℝ)^b ≤ log(N/a)`. The consumer is `PanWangDingLowMovingPrefix`.

The two direct imports are fixed mathlib objects and were reused only after exact source/object hashing; they were not recompiled, replayed, or re-audited here. No proof source was patched and no production file was changed.

## Supply status

This removes one genuine leaf from the path

`PanQuotientBounds → PanWangDingLowMovingPrefix → PanWangDingLowEndpoint → Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly → LiuPanPrimitiveLedgerAssembly → S1BetaGeometry → S1BetaPaidLower`.

It does not accept the remaining Liu–Pan ledger DAG, `S1BetaGeometry`, or `S1BetaPaidLower`. The next batch must choose another ready leaf from the actual DAG. `CurrentChenInitialMean`, the complete eleven-term mean, and `hLower` remain open; `(33/4) * Real.log 3` is still only an independent first-term candidate. The final weight scale remains `4c = 49044063/6250000 = 7.84705008` because `W_N ≤ 4*D12(N)+error`.

Evidence is under `verification/parts/p5/round7/panquotientbounds/`. Root CI is tracked separately. Receiving parts: P5 and P0.
