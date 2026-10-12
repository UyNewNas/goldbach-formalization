# Chen Part 5 — S1MainMass independent acceptance

## Result

`MathlibNt.SieveTheory.LiLiuGoldbachS1MainMass` is accepted as a single supplier node at the enclosing published commit. Its fixed upstream source SHA256 is `4fdcdd6001278a1c7636a40ba8f2e2e6c685a20331a4b0c803c0146f516a4533` and its strictly compiled object SHA256 is `fb8bf3a7c264da9e81f18bc15889386406c55d89f30580beea65b46a94d36d2b`.

The target passed strict official-frontend compilation (`trustLevel=0`, `warningAsError=true`, 6.618 s), stock `leanchecker` replay (5.6 s), and a defining-module audit (192.293 s). The compiler enumerated 6 declarations: six theorems, consisting of the requested public theorem and five generated/private proof declarations. No unsafe or own axiom declaration was found. The complete transitive axiom union is exactly `propext`, `Classical.choice`, and `Quot.sound`.

The unique direct compatibility import `MathlibNt.SieveTheory.BombieriVinogradov` was absent from the live cache and was strictly recompiled in this batch (8.724 s), reproducing its previously recorded object SHA256 `bcfdf76d4b503094d0040a0c3e99371b1b769014947f0a4cc0e16ad078243e02`. To provide its local namespace closure, 95 byte-identical objects were restored into the P5-owned output directory only after matching the prior S1Carrier source hashes, object hashes, successful trust-zero certificates, and all recorded sidecars. They were not described as recompiled, replayed, or re-audited here. Three pre-acceptance missing-object diagnostics are retained under `raw/`.

## Compiler-confirmed theorem type

```lean
MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig.goldbachS1_strictEndpoint_mainMass_lower :
∀ (ε η : ℝ),
  0 < ε →
    ε < 1 →
      0 < η →
        ∃ N₀,
          2 ≤ N₀ ∧
            ∀ (N : ℕ),
              N₀ ≤ N →
                have m := ⌈(1 - ε) * ↑N⌉₊ - 1;
                2 ≤ m ∧
                  m ≤ N ∧
                    (1 - ε - η) * (↑N / Real.log ↑N) ≤
                      MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral ↑m
```

Thus for `0 < ε < 1` and `0 < η`, sufficiently large `N` has the strict endpoint `m = Nat.ceil ((1-ε)*N)-1` with `2 ≤ m ≤ N`, and `(1-ε-η)*(N/log N) ≤ trueLogarithmicIntegral m`. There is no evenness hypothesis. This theorem does not itself contain a sieve product, Rosser weight, AP-error payment, singular normalization, or an `N/log² N` conclusion.

## Supply-chain status

This acceptance removes the strict-endpoint/true-logarithmic-integral main-mass input used by `S1MainScale`, and the endpoint/nonnegativity use downstream of `S1BetaPaidLower` and `S1BetaFixedNormalizedLower`. It does **not** close the beta product scale: that still depends on `goldbachS1_beta_mainMass_mul_product_lower` and its own supplier chain.

The next small candidate is `MathlibNt.SieveTheory.LiLiuGoldbachS1BetaPaidLower`, subject to an actual direct-dependency check. `CurrentChenInitialMean`, the complete eleven-term signed mean, and `hLower` remain open. In particular, `(33/4) * Real.log 3` remains an independent first-term candidate and is not the manuscript-adopted `L1`. The final scale remains `W_N ≤ 4*D12(N)+error`, hence the weight target remains `4c = 49044063/6250000 = 7.84705008`.

## Evidence

- `receipt.json`: identities, object hashes, gates, and audit summary.
- `commands-and-results.json` and `raw/`: actual commands, exit codes, elapsed times, and complete logs.
- `declarations.json` and `declaration-axioms.jsonl`: all defining-module declarations, including generated/private declarations.
- `public-theorem-types.json` and `compiler-types.txt`: compiler-confirmed type, distinct from source extraction.
- `restoration.json` and `restoration-manifest.json`: exact cache-reuse proof.
- `source/`, `runtime/`, and `objects/`: source/driver snapshots and a round-tripped transport copy of the accepted target object.

Root CI was not run for this as-yet unpublished checkpoint; its state is separate from this single-module acceptance. No CI configuration or threshold was changed. Receiving parts: P5 and P0.
