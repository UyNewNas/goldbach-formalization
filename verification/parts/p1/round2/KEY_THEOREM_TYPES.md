# Part 1 round 2: complete source theorem types

**Status: UNCOMPILED CANDIDATE.** These are source declarations from the
two new round-2 modules. No successful compilation, kernel replay,
defining-module census, or match against an actual Lean audit output is
claimed for this source snapshot. The actual audit types have not yet
been obtained. A later verified delivery must bind its records to the
then-current source bytes before replacing this status.

The working proof baseline remains
`1a80c1bcce67886f699d097fc37fd245cd3620bf`. These new candidate leaves
extend the previously published P1 mathematical sources, whose current
branch checkpoint is `7f894bfb57b7aa561360e335c6d610b7c30614e0`.
The source hashes below identify uncommitted round-2 candidate bytes;
that checkpoint is not presented as their source commit or receipt.

## Extraction scope

This document contains all 22 public theorem declaration types in the
two modules and the complete defining expressions of the six requested
core definitions. Every parameter, hypothesis, arithmetic carrier,
indicator, filter, strict endpoint, and target filter is preserved.
Each heading gives the full namespace; the code block preserves the
source declaration spelling in that namespace. Theorem proof bodies
are omitted without inserting a placeholder proof. These blocks are
source excerpts, not output from `#print` or a compiled interface.

Private declarations and compiler-generated declarations are outside
this public-type inventory. They must still be included in the actual
defining-module safety and axiom audit; this document is not that audit.

| Source | Source SHA256 | Public theorem types | Core definitions |
| --- | --- | ---: | ---: |
| `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean` | `0d54b930393ef01dbc9c44fbec5f356bf6be9a645a1a537064179fc12799424b` | 9 | 1 |
| `ImbalancedChen/ActualHistoricalFifthCellIntegral.lean` | `550602f634e27641bf1f0b811e5e201130f48587bd0760192d032b75c0c405de` | 13 | 5 |

## Mathematical scope

The geometric interface identifies a fifth-candidate cell of the actual
third-capped rank-four parent. Its first cube uses the original level;
its third cube uses the effective third ancestor cell. The old fifth
residual uses the effective fourth ancestor, and the two own-cube gates
remain separate. The integral module supplies actual prime-tuple cell
identities, exact fallback, finite common-cell composition, and genuine
Ico-cell integral limits, with the literal ceil enumeration corollary.

The separately reported full inherited-fifth candidate remains
**SOURCE_PENDING**. These candidate declarations do not claim receipt
of that source, a new retained-polynomial density Tendsto, the complete
adopted manuscript construction, a numerical K/c certificate, or a
physical distribution/factorization theorem.

## `ImbalancedChen/HistoricalUpperFiveCellGeometry.lean`

### `ImbalancedChen.HistoricalPrefixCapData.fifthParentGateBounds`

**Source-only declaration; actual audit match pending.**

```lean
def fifthParentGateBounds (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : Fin 6 → ℝ :=
  ![0, 0, 0, 0, (D.old : ℝ),
    (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)]
```

### `ImbalancedChen.HistoricalPrefixCapData.mem_fifthParentGateRegion`

**Source-only declaration; actual audit match pending.**

```lean
theorem mem_fifthParentGateRegion (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) (t : Fin 5 → ℝ) :
    t ∈ primeAffineGateRegion ordinaryUpperFiveGateForms
        (D.fifthParentGateBounds j) ↔
      StrictAnti t ∧ 3 * t 0 < (D.old : ℝ) ∧
        t 0 + t 1 + 3 * t 2 <
          (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)
```

### `ImbalancedChen.HistoricalPrefixCapData.level3_on_fifth_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem level3_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 N (rosserAncestor 3 history) =
      N ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)
```

### `ImbalancedChen.HistoricalPrefixCapData.level4_on_fifth_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem level4_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ) (hlen : history.length = 5)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level4 N (rosserAncestor 4 history) = N ^ (D.old5 j : ℝ)
```

### `ImbalancedChen.HistoricalPrefixCapData.level5_on_fifth_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem level5_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ)
    (j : Fin 5 → Fin (D.m + 1))
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = N ^ (D.cell5 j : ℝ)
```

### `ImbalancedChen.HistoricalPrefixCapData.level5_on_selected_fifth_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem level5_on_selected_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℝ) (history : List ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (ht : primeHistoryLogCoordinates N 5 history ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level5 N history = N ^ (D.cap5 j : ℝ)
```

### `ImbalancedChen.HistoricalPrefixCapData.level3_tuple_on_fifth_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem level3_tuple_on_fifth_cell (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N : ℕ) (p : Fin 5 → ℕ) (j : Fin 5 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.level3 (N : ℝ) [p 2, p 1, p 0] =
      (N : ℝ) ^ (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)
```

### `ImbalancedChen.historicalUpperFive_cube_tests_iff_log`

**Source-only declaration; actual audit match pending.**

```lean
theorem historicalUpperFive_cube_tests_iff_log {N : ℕ} (hN : 1 < N)
    (old third : ℝ) (p : Fin 5 → ℕ) (hpos : ∀ i, 0 < p i) :
    ((p 0 : ℝ) ^ 3 < (N : ℝ) ^ old ∧
      (p 0 : ℝ) * p 1 * (p 2 : ℝ) ^ 3 < (N : ℝ) ^ third) ↔
      3 * actualPrimeTupleLog N p 0 < old ∧
        actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
          3 * actualPrimeTupleLog N p 2 < third
```

### `ImbalancedChen.mem_historicalUpperFiveFrontierTuples_iff_log_on_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem mem_historicalUpperFiveFrontierTuples_iff_log_on_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (p : Fin 5 → ℕ) (j : Fin 5 → Fin (D.m + 1))
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
        (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))) ↔
      StrictAnti p ∧
        (∀ i, Nat.Prime (p i) ∧ ¬p i ∣ N ∧
          0 ≤ (p i : ℝ) ∧ (p i : ℝ) < (N : ℝ) ^ (D.b : ℝ)) ∧
        3 * actualPrimeTupleLog N p 0 < (D.old : ℝ) ∧
          actualPrimeTupleLog N p 0 + actualPrimeTupleLog N p 1 +
            3 * actualPrimeTupleLog N p 2 <
              (D.cell3 (historicalPrefixProject (by omega : 3 ≤ 5) j) : ℝ)
```

### `ImbalancedChen.historicalUpperFiveFrontierTuples_cell_filter`

**Source-only declaration; actual audit match pending.**

```lean
theorem historicalUpperFiveFrontierTuples_cell_filter
    (D : HistoricalPrefixCapData) (hab : D.a < D.b)
    (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) :
    (firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ)))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) =
      (actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ))
        (fun _ => (D.b : ℝ))).filter
        (fun p => actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
            primeAffineGateRegion ordinaryUpperFiveGateForms
              (D.fifthParentGateBounds j))
```


## `ImbalancedChen/ActualHistoricalFifthCellIntegral.lean`

### `ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference`

**Source-only declaration; actual audit match pending.**

```lean
def fifthTupleOwnCubeDifference (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ) : ℝ :=
  actualPrimeTupleOwnCubeMinus N cap
      (D.exponent5 (actualPrimeTupleLog N p) : ℝ) p -
    actualPrimeTupleOwnCubeMinus N cap
      (D.exponent4 (historicalPrefixProject (by omega : 4 ≤ 5)
        (actualPrimeTupleLog N p)) : ℝ) p
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection`

**Source-only declaration; actual audit match pending.**

```lean
def fifthCellPrimeCorrection (D : HistoricalPrefixCapData)
    (N cap : ℕ) (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) *
      (if actualPrimeTupleLog N p ∈
          logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
        then D.fifthTupleOwnCubeDifference N cap p else 0)
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthPrimeCorrection`

**Source-only declaration; actual audit match pending.**

```lean
def fifthPrimeCorrection (D : HistoricalPrefixCapData) (N cap : ℕ) : ℝ :=
  ∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
    (∏ i, 1 / ((p i : ℝ) - 1)) * D.fifthTupleOwnCubeDifference N cap p
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_on_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthTupleOwnCubeDifference_on_cell (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5)
    (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fifthTupleOwnCubeDifference N cap p =
      actualPrimeTupleOwnCubeMinus N cap (D.cap5 j : ℝ) p -
        actualPrimeTupleOwnCubeMinus N cap (D.old5 j : ℝ) p
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_on_unselected_cell`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthTupleOwnCubeDifference_on_unselected_cell
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5)
    (p : Fin 5 → ℕ)
    (ht : actualPrimeTupleLog N p ∈
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fifthTupleOwnCubeDifference N cap p = 0
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_outside`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthTupleOwnCubeDifference_outside (D : HistoricalPrefixCapData)
    (N cap : ℕ) (p : Fin 5 → ℕ)
    (hout : ∀ j ∈ D.cells5, actualPrimeTupleLog N p ∉
      logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j) :
    D.fifthTupleOwnCubeDifference N cap p = 0
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection_eq_zero_of_not_mem`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthCellPrimeCorrection_eq_zero_of_not_mem
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b) (N cap : ℕ)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∉ D.cells5) :
    D.fifthCellPrimeCorrection N cap j = 0
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthTupleOwnCubeDifference_eq_cell_indicators`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthTupleOwnCubeDifference_eq_cell_indicators
    (D : HistoricalPrefixCapData) (hab : D.a ≤ D.b)
    (N cap : ℕ) (p : Fin 5 → ℕ) :
    D.fifthTupleOwnCubeDifference N cap p =
      ∑ j ∈ D.cells5,
        if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j
          then D.fifthTupleOwnCubeDifference N cap p else 0
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthPrimeCorrection_eq_cells`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthPrimeCorrection_eq_cells (D : HistoricalPrefixCapData)
    (hab : D.a ≤ D.b) (N cap : ℕ) :
    D.fifthPrimeCorrection N cap =
      ∑ j ∈ D.cells5, D.fifthCellPrimeCorrection N cap j
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthFrontier_cell_weighted_sum`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthFrontier_cell_weighted_sum (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) (f : (Fin 5 → ℕ) → ℝ) :
    (∑ p ∈ firstExitFrontierTuples 4 (D.upperThirdPolicy (N : ℝ))
      (roughPrimeUniverse N cap 0 ((N : ℝ) ^ (D.b : ℝ))),
      (∏ i, 1 / ((p i : ℝ) - 1)) *
        (if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j then f p else 0)) =
      ∑ p ∈ actualPrimeBoxTuples N (fun _ : Fin 5 => (D.a : ℝ))
          (fun _ => (D.b : ℝ)),
        (∏ i, 1 / ((p i : ℝ) - 1)) *
          (if actualPrimeTupleLog N p ∈
            logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
              primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
            then f p else 0)
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCellPrimeCorrection_eq_residual_sums`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthCellPrimeCorrection_eq_residual_sums (D : HistoricalPrefixCapData)
    (hab : D.a < D.b) (hold : 0 < D.old) (hcheck : D.levelCheck = true)
    (N cap : ℕ) (hN : 1 < N)
    (hcap : (N : ℝ) ^ (D.b : ℝ) ≤ (cap : ℝ))
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) :
    D.fifthCellPrimeCorrection N cap j =
      actualPrimeBoxOwnCubeMinusSum 4 N cap (D.a : ℝ) (D.b : ℝ) (D.cap5 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)) -
      actualPrimeBoxOwnCubeMinusSum 4 N cap (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ)
        (logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j))
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCellIntegral`

**Source-only declaration; actual audit match pending.**

```lean
def fifthCellIntegral (D : HistoricalPrefixCapData)
    (j : Fin 5 → Fin (D.m + 1)) : ℝ :=
  primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) (D.cap5 j : ℝ) D.m j
      ordinaryUpperFiveGateForms (D.fifthParentGateBounds j) -
    primeOwnCubeIcoIntegral (D.a : ℝ) (D.b : ℝ) (D.old5 j : ℝ) D.m j
      ordinaryUpperFiveGateForms (D.fifthParentGateBounds j)
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCorrectionIntegral`

**Source-only declaration; actual audit match pending.**

```lean
def fifthCorrectionIntegral (D : HistoricalPrefixCapData) : ℝ :=
  ∑ j ∈ D.cells5, D.fifthCellIntegral j
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCellIntegral_eq_integral`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthCellIntegral_eq_integral (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (j : Fin 5 → Fin (D.m + 1)) :
    D.fifthCellIntegral j =
      ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
        primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
        (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
          primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i
```

### `ImbalancedChen.HistoricalPrefixCapData.fifthCorrectionIntegral_eq_integrals`

**Source-only declaration; actual audit match pending.**

```lean
theorem fifthCorrectionIntegral_eq_integrals (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) :
    D.fifthCorrectionIntegral =
      ∑ j ∈ D.cells5,
        ∫ t in logPrimeMeshCell (D.a : ℝ) (D.b : ℝ) D.m j ∩
          primeAffineGateRegion ordinaryUpperFiveGateForms (D.fifthParentGateBounds j),
          (primeOwnCubeGatedProfile (D.cap5 j : ℝ) t -
            primeOwnCubeGatedProfile (D.old5 j : ℝ) t) * ∏ i, 1 / t i
```

### `ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthCellPrimeCorrection`

**Source-only declaration; actual audit match pending.**

```lean
theorem tendsto_fifthCellPrimeCorrection (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true)
    (j : Fin 5 → Fin (D.m + 1)) (hj : j ∈ D.cells5) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fifthCellPrimeCorrection N (cap N) j)
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 (D.fifthCellIntegral j))
```

### `ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection`

**Source-only declaration; actual audit match pending.**

```lean
theorem tendsto_fifthPrimeCorrection (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) (cap : ℕ → ℕ)
    (hcap : ∀ᶠ N : ℕ in atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N},
      (N : ℝ) ^ (D.b : ℝ) ≤ (cap N : ℝ)) :
    Tendsto (fun N : ℕ => D.fifthPrimeCorrection N (cap N))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```

### `ImbalancedChen.HistoricalPrefixCapData.tendsto_fifthPrimeCorrection_ceil`

**Source-only declaration; actual audit match pending.**

```lean
theorem tendsto_fifthPrimeCorrection_ceil (D : HistoricalPrefixCapData)
    (ha : 0 < D.a) (hab : D.a < D.b) (hold : 0 < D.old)
    (hcheck : D.levelCheck = true) :
    Tendsto (fun N : ℕ =>
      D.fifthPrimeCorrection N (Nat.ceil ((N : ℝ) ^ (D.b : ℝ))))
      (atTop ⊓ Filter.principal {N : ℕ | 0 < N ∧ Even N})
      (𝓝 D.fifthCorrectionIntegral)
```
