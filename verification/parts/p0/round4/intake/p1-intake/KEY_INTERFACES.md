# Fixed P1 stored-cap complete interfaces

Source: `744316efd1887f21c91dd4b63c218fa27704c931`. Source declaration heads and original compiler records are separate. Actual compiler formatting is default `Meta.ppExpr`, not `pp.all`; all 14 production records and all 36 including probes have no elision markers.

## ImbalancedChen.storedBoxCapCheck

Source declaration head:

```lean
def storedBoxCapCheck {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ) : Bool
```

Original compiler type:

```lean
{n : ℕ} → Finset (Fin n) → ℚ → ℚ → (Fin n → ℚ) → (Fin n → ℚ) → ℚ → Bool
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedBoxCapCheck_iff

Source declaration head:

```lean
theorem storedBoxCapCheck_iff {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ) :
    storedBoxCapCheck I old nu lo hi cap = true ↔
      selectedCapLower I old hi < cap ∧ cap < selectedCapUpper I nu lo hi
```

Original compiler type:

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true ↔
    ImbalancedChen.selectedCapLower I old hi < cap ∧ cap < ImbalancedChen.selectedCapUpper I nu lo hi
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedBoxCapCheck_old_lt

Source declaration head:

```lean
theorem storedBoxCapCheck_old_lt {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true) : old < cap
```

Original compiler type:

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true → old < cap
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedBoxCapCheck_midpoint

Source declaration head:

```lean
theorem storedBoxCapCheck_midpoint {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (hc : selectedBoxCapCheck I old nu lo hi = true) :
    storedBoxCapCheck I old nu lo hi (selectedBoxCap I old nu lo hi) = true
```

Original compiler type:

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ),
  ImbalancedChen.selectedBoxCapCheck I old nu lo hi = true →
    ImbalancedChen.storedBoxCapCheck I old nu lo hi (ImbalancedChen.selectedBoxCap I old nu lo hi) = true
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedBoxCapCheck_sound

Source declaration head:

```lean
theorem storedBoxCapCheck_sound {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ)
    (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true)
    (t : Fin n → ℝ) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ)) :
    (old : ℝ) < cap ∧ (cap : ℝ) < nu ∧ (1 / 2 : ℝ) < cap ∧
      (∀ j, prefixSquareExpr t j < cap) ∧
      (∀ j ∉ I, selectedSquareExpr I t j < cap) ∧
      (cap : ℝ) < v (∑ i ∈ I, t i)
```

Original compiler type:

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true →
    ∀ (t : Fin n → ℝ),
      (∀ (i : Fin n), ↑(lo i) ≤ t i) →
        (∀ (i : Fin n), t i ≤ ↑(hi i)) →
          ↑old < ↑cap ∧
            ↑cap < ↑nu ∧
              1 / 2 < ↑cap ∧
                (∀ (j : Fin n), ImbalancedChen.prefixSquareExpr t j < ↑cap) ∧
                  (∀ j ∉ I, ImbalancedChen.selectedSquareExpr I t j < ↑cap) ∧
                    ↑cap < ImbalancedChen.VariableEnvelope.v (∑ i ∈ I, t i)
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedBoxCapCheck_actual_square_gates

Source declaration head:

```lean
theorem storedBoxCapCheck_actual_square_gates {n : ℕ} (I : Finset (Fin n))
    (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ)
    (hc : storedBoxCapCheck I old nu lo hi cap = true)
    (t : Fin n → ℝ) (hl : ∀ i, (lo i : ℝ) ≤ t i) (hu : ∀ i, t i ≤ (hi i : ℝ))
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ j, ((∏ i ∈ Finset.univ.filter (fun i => i < j), p i : ℕ) : ℝ) *
      (p j : ℝ) ^ 2 < N ^ (cap : ℝ)) ∧
    (∀ j ∉ I, ((∏ i ∈ I, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < j ∧ i ∉ I), p i : ℕ) : ℝ) *
        (p j : ℝ) ^ 2 < N ^ (cap : ℝ))
```

Original compiler type:

```lean
∀ {n : ℕ} (I : Finset (Fin n)) (old nu : ℚ) (lo hi : Fin n → ℚ) (cap : ℚ),
  ImbalancedChen.storedBoxCapCheck I old nu lo hi cap = true →
    ∀ (t : Fin n → ℝ),
      (∀ (i : Fin n), ↑(lo i) ≤ t i) →
        (∀ (i : Fin n), t i ≤ ↑(hi i)) →
          ∀ (N : ℝ),
            1 < N →
              ∀ (p : Fin n → ℕ),
                (∀ (i : Fin n), ↑(p i) ≤ N ^ t i) →
                  (∀ (j : Fin n), ↑(∏ i with i < j, p i) * ↑(p j) ^ 2 < N ^ ↑cap) ∧
                    ∀ j ∉ I, ↑(∏ i ∈ I, p i) * ↑(∏ i with i < j ∧ i ∉ I, p i) * ↑(p j) ^ 2 < N ^ ↑cap
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedMeshCapCheck

Source declaration head:

```lean
def storedMeshCapCheck {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ) : Bool
```

Original compiler type:

```lean
{n : ℕ} →
  ℚ →
    ℚ →
      (m : ℕ) →
        Finset (Fin n → Fin (m + 1)) →
          ((Fin n → Fin (m + 1)) → Finset (Fin n)) →
            ((Fin n → Fin (m + 1)) → ℚ) → ((Fin n → Fin (m + 1)) → ℚ) → ((Fin n → Fin (m + 1)) → ℚ) → Bool
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedMeshCapCheck_iff

Source declaration head:

```lean
theorem storedMeshCapCheck_iff {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ) :
    storedMeshCapCheck a b m J I old nu cap = true ↔
      ∀ j ∈ J, storedBoxCapCheck (I j) (old j) (nu j)
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) (cap j) = true
```

Original compiler type:

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true ↔
    ∀ j ∈ J,
      ImbalancedChen.storedBoxCapCheck (I j) (old j) (nu j) (ImbalancedChen.qLogPrimeMeshLo a b m j)
          (ImbalancedChen.qLogPrimeMeshHi a b m j) (cap j) =
        true
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedMeshCapCheck_old_lt

Source declaration head:

```lean
theorem storedMeshCapCheck_old_lt {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true) :
    ∀ j ∈ J, old j < cap j
```

Original compiler type:

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true → ∀ j ∈ J, old j < cap j
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedMeshCapCheck_sound

Source declaration head:

```lean
theorem storedMeshCapCheck_sound {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true)
    (j : Fin n → Fin (m + 1)) (hj : j ∈ J)
    (t : Fin n → ℝ) (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j) :
    (old j : ℝ) < cap j ∧ (cap j : ℝ) < nu j ∧ (1 / 2 : ℝ) < cap j ∧
      (∀ i, prefixSquareExpr t i < cap j) ∧
      (∀ i ∉ I j, selectedSquareExpr (I j) t i < cap j) ∧
      (cap j : ℝ) < v (∑ i ∈ I j, t i)
```

Original compiler type:

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true →
    ∀ j ∈ J,
      ∀ t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j,
        ↑(old j) < ↑(cap j) ∧
          ↑(cap j) < ↑(nu j) ∧
            1 / 2 < ↑(cap j) ∧
              (∀ (i : Fin n), ImbalancedChen.prefixSquareExpr t i < ↑(cap j)) ∧
                (∀ i ∉ I j, ImbalancedChen.selectedSquareExpr (I j) t i < ↑(cap j)) ∧
                  ↑(cap j) < ImbalancedChen.VariableEnvelope.v (∑ i ∈ I j, t i)
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedMeshCapCheck_actual_square_gates

Source declaration head:

```lean
theorem storedMeshCapCheck_actual_square_gates {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu cap : (Fin n → Fin (m + 1)) → ℚ)
    (hc : storedMeshCapCheck a b m J I old nu cap = true)
    (j : Fin n → Fin (m + 1)) (hj : j ∈ J)
    (t : Fin n → ℝ) (ht : t ∈ logPrimeMeshCell (a : ℝ) (b : ℝ) m j)
    (N : ℝ) (hN : 1 < N) (p : Fin n → ℕ) (hp : ∀ i, (p i : ℝ) ≤ N ^ t i) :
    (∀ k, ((∏ i ∈ Finset.univ.filter (fun i => i < k), p i : ℕ) : ℝ) *
      (p k : ℝ) ^ 2 < N ^ (cap j : ℝ)) ∧
    (∀ k ∉ I j, ((∏ i ∈ I j, p i : ℕ) : ℝ) *
      ((∏ i ∈ Finset.univ.filter (fun i => i < k ∧ i ∉ I j), p i : ℕ) : ℝ) *
        (p k : ℝ) ^ 2 < N ^ (cap j : ℝ))
```

Original compiler type:

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu cap : (Fin n → Fin (m + 1)) → ℚ),
  ImbalancedChen.storedMeshCapCheck a b m J I old nu cap = true →
    ∀ j ∈ J,
      ∀ t ∈ ImbalancedChen.logPrimeMeshCell (↑a) (↑b) m j,
        ∀ (N : ℝ),
          1 < N →
            ∀ (p : Fin n → ℕ),
              (∀ (i : Fin n), ↑(p i) ≤ N ^ t i) →
                (∀ (k : Fin n), ↑(∏ i with i < k, p i) * ↑(p k) ^ 2 < N ^ ↑(cap j)) ∧
                  ∀ k ∉ I j, ↑(∏ i ∈ I j, p i) * ↑(∏ i with i < k ∧ i ∉ I j, p i) * ↑(p k) ^ 2 < N ^ ↑(cap j)
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## ImbalancedChen.storedMeshCapCheck_of_selectedBoxCapChecks

Source declaration head:

```lean
theorem storedMeshCapCheck_of_selectedBoxCapChecks {n : ℕ} (a b : ℚ) (m : ℕ)
    (J : Finset (Fin n → Fin (m + 1)))
    (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
    (old nu : (Fin n → Fin (m + 1)) → ℚ)
    (hc : ∀ j ∈ J, selectedBoxCapCheck (I j) (old j) (nu j)
      (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j) = true) :
    storedMeshCapCheck a b m J I old nu
      (fun j => selectedBoxCap (I j) (old j) (nu j)
        (qLogPrimeMeshLo a b m j) (qLogPrimeMeshHi a b m j)) = true
```

Original compiler type:

```lean
∀ {n : ℕ} (a b : ℚ) (m : ℕ) (J : Finset (Fin n → Fin (m + 1))) (I : (Fin n → Fin (m + 1)) → Finset (Fin n))
  (old nu : (Fin n → Fin (m + 1)) → ℚ),
  (∀ j ∈ J,
      ImbalancedChen.selectedBoxCapCheck (I j) (old j) (nu j) (ImbalancedChen.qLogPrimeMeshLo a b m j)
          (ImbalancedChen.qLogPrimeMeshHi a b m j) =
        true) →
    (ImbalancedChen.storedMeshCapCheck a b m J I old nu fun j =>
        ImbalancedChen.selectedBoxCap (I j) (old j) (nu j) (ImbalancedChen.qLogPrimeMeshLo a b m j)
          (ImbalancedChen.qLogPrimeMeshHi a b m j)) =
      true
```

Axioms: `propext`, `Classical.choice`, `Quot.sound`.
