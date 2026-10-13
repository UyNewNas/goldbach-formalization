# Chen Part 5 — Pointwise SW payment core leaf acceptance

## Result

`MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedPointwiseSWPaymentCore` is accepted as one independent leaf of the real Liu–Pan/S1 supplier chain. Fixed source SHA256: `3798b1a9798e1a7390ba5d3ba879287e6c1a466b4f91f39a434f3f1bc41b65d2`. Strictly compiled object SHA256: `990f38b862e64d8f93150322e2344c46e6d4683be2efcc202adc36f832906cf4`.

The official frontend strict compile passed in 7.577 s; the unmodified stock `leanchecker` binary replay passed in 1.76 s; the complete defining-module audit passed in 34.27 s. The compiler enumerated exactly one theorem declaration. There are no private/generated declarations, unsafe declarations, or own axiom declarations. Its transitive axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Compiler-confirmed type

```lean
AnalyticNumberTheory.LargeSieve.pointwiseSW_horizontal_le_tail :
∀ {X ε T Q L : ℝ}, 0 ≤ X → 0 < ε → 0 < T → Q ≤ T → Q * X / (ε * (1 + T ^ 2)) ≤ X * (1 + L ^ 2) / (ε * T)
```

This is the actual horizontal-contour-error payment. It is directly used by the nonquadratic and quadratic pointwise Siegel–Walfisz modules, with `L := d⁻¹` and `L := δ⁻¹` respectively. It does not itself prove either pointwise Siegel–Walfisz theorem.

The unique direct import is the already accepted `MathlibNt.AnalyticNumberTheory.LargeSieve.LogPowerBounds`, restored from its deterministic round8 transport with exact object SHA256 `d52f560c960a917755a67bd10549ccb324c5d97f8296e8519c6b995685899a96`. It was not recompiled, replayed, or re-audited here. No proof source was patched and no production proof file was changed.

## Sandbox runtime compatibility

This fresh sandbox exposed `/proc/self/exe` but not `/proc/<namespace-pid>/exe`, which the fixed Lean runtime uses to locate its executable. The Lean binaries remain byte-for-byte identical to the fixed toolchain. A separately hashed preload shim only retries a failed `readlink` of `/proc/<pid>/exe` as `/proc/self/exe`; it changes no Lean option, declaration, proof term, object, kernel rule, or audit result. Its source, binary transport, and hashes are archived with this receipt.

## Supply status

One actual path from this leaf to the current first-term target is

`PointwiseSWPaymentCore → DirichLTwistedNonquadraticPointwiseSiegelWalfisz → LandauSiegelToLowSWSource → LandauSiegelToStandardBVCanonicalSmoothing → FourFactorUnconditionalEndpoints → PanWangDingLowPrimePrefix → PanWangDingLowMovingPrefix → PanWangDingLowEndpoint → Distribution.LiuPan.LiuPanPrimitiveLedgerAssembly → S1BetaGeometry → S1BetaPaidLower`.

This batch does not accept those downstream modules. In the fresh workspace, all six available P5 object transports were restored exactly, while unrelated transient shared-cache objects were not assumed. The recomputed closure has 314 source modules, 309 missing objects, and 19 ready leaves. The smallest remaining ready leaf is the **uncompiled candidate** `MathlibNt.Analysis.MovingIntervalIntegral`, source SHA256 `9905992e4664d4f689ad3a24c8bf5d3591a4d2de88ddf1df14a4016873741fb2`, with 47 source lines.

`CurrentChenInitialMean`, the complete eleven-term mean, and `hLower` remain open; `(33/4) * Real.log 3` remains only an independent first-term candidate. The final weight scale remains `4c = 49044063/6250000 = 7.84705008` because `W_N ≤ 4*D12(N)+error`.

## Root CI

For parent checkpoint `85cd681432d85b880b82add771e81456e66c53d1`, Variable envelope verification succeeded. Lean core verification built the full project successfully in 5 seconds, then the root `leanchecker` step hit its configured 25-minute timeout and the root axiom-audit step hit its configured 10-minute timeout. This is reported separately from the passing single-module gates; CI configuration and thresholds were not changed.

Evidence is under `verification/parts/p5/round10/pointwiseswpaymentcore/`. Receiving parts: P5 and P0.
