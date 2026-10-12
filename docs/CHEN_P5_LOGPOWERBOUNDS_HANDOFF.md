# Chen Part 5 — LogPowerBounds leaf acceptance

## Result

`MathlibNt.Analysis.LogPowerBounds` is accepted as one independent leaf of the real `S1BetaGeometry → LiuPanPrimitiveLedgerAssembly` supplier chain. Fixed source SHA256: `b1f24d0f70f59fa85c05c56ce51e15bb830f615d81fe6f490fcc650d2d8e3e1a`. Strictly compiled object SHA256: `5c6800c66edd0f0c0a3a46aef6d71e9925f6be0c4123e7d793d9a763fb316dd9`.

The official frontend strict compile passed in 15.775 s; stock `leanchecker` replay passed in 3.666 s; the complete defining-module audit passed in 67.633 s. The compiler enumerated three theorem declarations: the requested public theorem plus two generated/private proof declarations. There are no unsafe or own axiom declarations and the transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Compiler-confirmed type

```lean
MathlibNt.Analysis.eventually_nat_log_rpow_le_rpow :
∀ (b d : ℝ), 0 < d → ∀ᶠ (N : ℕ) in Filter.atTop, Real.log ↑N ^ b ≤ ↑N ^ d
```

This pays only the elementary asymptotic fact that every positive power of `N` eventually dominates any fixed real power of `log N`. The actual consumer `LiuPanPrimitiveLedgerAssembly` uses it in `eventually_pan_log_rpow_le_rpow` and the eventual conductor bounds.

The two direct imports are fixed mathlib objects and were reused only after exact source/object hashing; they were not recompiled, replayed, or re-audited here. No proof source was patched and no production file was changed.

## Supply status

This removes one genuine leaf from the path

`LogPowerBounds → Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly → LiuPanPrimitiveLedgerAssembly → S1BetaGeometry → S1BetaPaidLower`.

It does not accept the remaining Liu–Pan ledger DAG, `S1BetaGeometry`, or `S1BetaPaidLower`. The next batch must choose another ready leaf from the actual DAG. `CurrentChenInitialMean`, the complete eleven-term mean, and `hLower` remain open; `(33/4) * Real.log 3` is still only an independent first-term candidate. The final weight scale remains `4c = 49044063/6250000 = 7.84705008` because `W_N ≤ 4*D12(N)+error`.

Evidence is under `verification/parts/p5/round6/logpowerbounds/`. Root CI is tracked separately. Receiving parts: P5 and P0.
