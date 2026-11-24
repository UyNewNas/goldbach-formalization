import ImbalancedChen.Part3E1MediumCaps

/-! A disjoint three-cell cover of the physical smooth q carrier. -/

namespace ImbalancedChen.Part3

open Finset

private theorem mem_factorCarrier_of_bounds {L : ℝ} (hL : 0 ≤ L) {q : ℕ}
    (hlo : L ≤ (q : ℝ)) (hhi : (q : ℝ) ≤ 2 * L) : q ∈ factorCarrier L :=
  mem_Icc.mpr ⟨Nat.ceil_le.mpr hlo, (Nat.le_floor_iff (by positivity)).mpr hhi⟩

/-- Every finite subset of the physical smooth q window splits into exactly
three indexed slices, allowing empty slices and keeping closed cell endpoints. -/
theorem e1SmoothWindow_exists_three_qCells (Q₁ : ℝ) (hQ₁ : 1 ≤ Q₁) (Q : Finset ℕ)
    (hSupport : ∀ q ∈ Q, Q₁ / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ 5 * Q₁ / 2) :
    ∃ (Qs : Fin 3 → Finset ℕ) (q₀ : Fin 3 → ℝ),
      Q = univ.biUnion Qs ∧ Set.PairwiseDisjoint (↑(univ : Finset (Fin 3)) : Set (Fin 3)) Qs ∧
      ∀ i : Fin 3, 1 ≤ q₀ i ∧ Q₁ / 4 ≤ q₀ i ∧ q₀ i ≤ 4 * Q₁ ∧ Qs i ⊆ factorCarrier (q₀ i) := by
  classical
  let cell (q : ℕ) : Fin 3 := if (q : ℝ) ≤ Q₁ then 0 else if (q : ℝ) ≤ 2 * Q₁ then 1 else 2
  let Qs (i : Fin 3) : Finset ℕ := Q.filter fun q => cell q = i
  let q₀ (i : Fin 3) : ℝ := if i = 0 then max 1 (Q₁ / 2) else if i = 1 then Q₁ else 2 * Q₁
  refine ⟨Qs, q₀, ?_, ?_, ?_⟩
  · ext q
    constructor
    · intro hq
      exact mem_biUnion.mpr ⟨cell q, mem_univ _, mem_filter.mpr ⟨hq, rfl⟩⟩
    · intro hq
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hq
      exact (mem_filter.mp hi).1
  · intro i _ j _ hij
    refine disjoint_left.mpr ?_
    intro q hi hj
    exact hij ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
  · intro i
    fin_cases i
    · have hq0 : 1 ≤ max 1 (Q₁ / 2) := le_max_left _ _
      have hq0lo : Q₁ / 4 ≤ max 1 (Q₁ / 2) :=
        (by linarith : Q₁ / 4 ≤ Q₁ / 2).trans (le_max_right _ _)
      have hq0hi : max 1 (Q₁ / 2) ≤ 4 * Q₁ :=
        max_le (by linarith) (by linarith)
      change 1 ≤ max 1 (Q₁ / 2) ∧ Q₁ / 4 ≤ max 1 (Q₁ / 2) ∧
        max 1 (Q₁ / 2) ≤ 4 * Q₁ ∧ Qs 0 ⊆ factorCarrier (max 1 (Q₁ / 2))
      refine ⟨hq0, hq0lo, hq0hi, ?_⟩
      intro q hq
      obtain ⟨hm, hi⟩ := mem_filter.mp hq
      obtain ⟨hlo, _⟩ := hSupport q hm
      have hpos : (0 : ℝ) < q := by linarith
      have hqN : 0 < q := by exact_mod_cast hpos
      have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hqN
      have hupper : (q : ℝ) ≤ Q₁ := by
        by_contra! hbad
        by_cases hm' : (q : ℝ) ≤ 2 * Q₁
        · simp [cell, not_le.mpr hbad, hm'] at hi
        · simp [cell, not_le.mpr hbad, hm'] at hi
      have hmax : Q₁ / 2 ≤ max 1 (Q₁ / 2) := le_max_right _ _
      exact mem_factorCarrier_of_bounds (by positivity) (max_le h1 hlo) (by linarith)
    · change 1 ≤ Q₁ ∧ Q₁ / 4 ≤ Q₁ ∧ Q₁ ≤ 4 * Q₁ ∧ Qs 1 ⊆ factorCarrier Q₁
      refine ⟨hQ₁, by linarith, by linarith, ?_⟩
      intro q hq
      have hi := (mem_filter.mp hq).2
      have hlo : ¬ (q : ℝ) ≤ Q₁ := by
        intro h
        simp [cell, h] at hi
      have hhi : (q : ℝ) ≤ 2 * Q₁ := by
        by_contra! h
        simp [cell, hlo, not_le.mpr h] at hi
      exact mem_factorCarrier_of_bounds (by positivity) (le_of_not_ge hlo) hhi
    · change 1 ≤ 2 * Q₁ ∧ Q₁ / 4 ≤ 2 * Q₁ ∧ 2 * Q₁ ≤ 4 * Q₁ ∧ Qs 2 ⊆ factorCarrier (2 * Q₁)
      refine ⟨by linarith, by linarith, by linarith, ?_⟩
      intro q hq
      obtain ⟨hm, hi⟩ := mem_filter.mp hq
      obtain ⟨_, hhi⟩ := hSupport q hm
      have hlo : 2 * Q₁ ≤ (q : ℝ) := by
        by_contra! hbad
        by_cases hm' : (q : ℝ) ≤ Q₁
        · simp [cell, hm'] at hi
        · simp [cell, hm', hbad.le] at hi
      exact mem_factorCarrier_of_bounds (by positivity) hlo (by linarith)

end ImbalancedChen.Part3
