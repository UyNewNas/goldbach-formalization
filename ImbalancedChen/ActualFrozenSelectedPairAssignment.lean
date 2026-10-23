import ImbalancedChen.ActualFrozenSlotCoefficientRegrouping

/-!
# Finite words for the computed whole-box selected-pair assignments

The word records the same three slot lists already used by the endpoint
targets and signed coefficient regrouping. With original slot labels
distinct and exhaustive, its fibres are precisely those three lists.
Original rough support pays the number of slots, hence a uniform bound
on the number of assignment words before x varies. Partitioning a finite
family by these words leaves each original Cartesian box intact and
retains every signed scalar in its original summand.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

def actualFrozenSelectedPairAssignment {n : ℕ} (D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (p : Fin 3 → Fin n) (tail : List (Fin n)) : Fin n → Fin 3 :=
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  fun i => if i ∈ slots.1 then 0 else if i ∈ slots.2.1 then 1 else 2

/-- Distinct original labels make this word precisely the already
computed three-slot partition, rather than a new allocation. -/
theorem actualFrozenSelectedPairAssignment_fibres {n : ℕ} (D A : ℝ) (yz : Bool)
    (upper : Fin n → ℕ) (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hnodup : (p 0 :: p 1 :: p 2 :: tail).Nodup)
    (hcover : ∀ i, i ∈ p 0 :: p 1 :: p 2 :: tail) (i : Fin n) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    (actualFrozenSelectedPairAssignment D A yz upper p tail i = 0 ↔ i ∈ slots.1) ∧
      (actualFrozenSelectedPairAssignment D A yz upper p tail i = 1 ↔ i ∈ slots.2.1) ∧
      (actualFrozenSelectedPairAssignment D A yz upper p tail i = 2 ↔ i ∈ slots.2.2) := by
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  have hperm := actualFrozenSelectedPairSlots_perm D A yz upper p tail
  have hn : (slots.1 ++ slots.2.1 ++ slots.2.2).Nodup := hperm.nodup_iff.mpr hnodup
  obtain ⟨_, hn23, hne1⟩ := List.nodup_append.mp hn
  obtain ⟨_, _, hne2⟩ := List.nodup_append.mp hn23
  have h12 (h1 : i ∈ slots.1) (h2 : i ∈ slots.2.1) : False :=
    hne1 i h1 i (List.mem_append.mpr (Or.inl h2)) rfl
  have h13 (h1 : i ∈ slots.1) (h3 : i ∈ slots.2.2) : False :=
    hne1 i h1 i (List.mem_append.mpr (Or.inr h3)) rfl
  have h23 (h2 : i ∈ slots.2.1) (h3 : i ∈ slots.2.2) : False := hne2 i h2 i h3 rfl
  have hi : i ∈ slots.1 ∨ i ∈ slots.2.1 ∨ i ∈ slots.2.2 := by
    simpa only [List.mem_append] using hperm.mem_iff.mpr (hcover i)
  rcases hi with h1 | h2 | h3
  · have h2not : i ∉ slots.2.1 := h12 h1
    have h3not : i ∉ slots.2.2 := h13 h1
    simp [actualFrozenSelectedPairAssignment, h1, h2not, h3not]
  · have h1not : i ∉ slots.1 := fun h1 => h12 h1 h2
    have h3not : i ∉ slots.2.2 := h23 h2
    simp [actualFrozenSelectedPairAssignment, h1not, h2, h3not]
  · have h1not : i ∉ slots.1 := fun h1 => h13 h1 h3
    have h2not : i ∉ slots.2.1 := fun h2 => h23 h2 h3
    simp [actualFrozenSelectedPairAssignment, h1not, h2not, h3]

theorem actualFrozenSelectedPairAssignment_card (n : ℕ) :
    Fintype.card (Fin n → Fin 3) = 3 ^ n := by simp

/-- The word budget is uniform in x because its original arity bound is
derived from the original full rough vector, not a chosen remainder. -/
theorem actualFrozenSelectedPairAssignment_uniform_card {n : ℕ} {x ρ level : ℝ}
    (hx : 1 < x) (hρ : 0 < ρ) (hlevel : level ≤ 5 / 8)
    (actual : Fin n → ℕ) (p : Fin 3 → Fin n) (tail : List (Fin n))
    (hslots : (p 0 :: p 1 :: p 2 :: tail).Perm (List.finRange n))
    (hpositive : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, 0 < actual i)
    (hrough : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, x ^ ρ ≤ (actual i : ℝ))
    (hfull : actualDwellSupport (x ^ level) ((p 0 :: p 1 :: p 2 :: tail).map actual)) :
    Fintype.card (Fin n → Fin 3) ≤ 3 ^ actualRoughVectorRankBound ρ := by
  have hlen := actualRoughPrimeVector_length_le hx hρ hlevel
    ((p 0 :: p 1 :: p 2 :: tail).map actual) (by simp)
    (by simpa only [List.forall_mem_map] using hpositive)
    (by simpa only [List.forall_mem_map] using hrough) hfull
  have hn : n ≤ actualRoughVectorRankBound ρ := by
    have hlength := hslots.length_eq
    simp only [List.length_finRange] at hlength
    simpa only [List.length_map, hlength] using hlen
  rw [actualFrozenSelectedPairAssignment_card]
  exact Nat.pow_le_pow_right (by decide : 0 < 3) hn

/-- The finite partition is of original whole boxes. The full signed
coefficient and test value stay in F j, with no coordinate-fibre cut. -/
theorem actualFrozenSelectedPairAssignment_sum_partition {ι M : Type*}
    [DecidableEq ι] [AddCommMonoid M] {n : ℕ} (J : Finset ι)
    (D A : ι → ℝ) (yz : ι → Bool) (upper : ι → Fin n → ℕ)
    (p : ι → Fin 3 → Fin n) (tail : ι → List (Fin n)) (F : ι → M) :
    (∑ word : Fin n → Fin 3,
      ∑ j ∈ J.filter (fun j =>
        actualFrozenSelectedPairAssignment (D j) (A j) (yz j) (upper j) (p j) (tail j) = word), F j) =
      ∑ j ∈ J, F j := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

end

end ImbalancedChen
