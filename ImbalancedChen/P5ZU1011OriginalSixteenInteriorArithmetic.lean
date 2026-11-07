import ImbalancedChen.P5ZU1011OriginalSixteenArithmeticProducts

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Actual sixteen-policy interior levels and selected natural critical interval.
Every true full/selected square, and the separate W guard, enters the finite
maximum before a strict midpoint is chosen. Endpoint eligibility therefore
constructs a legal interior rather than assigning the endpoint as a physical
level. The selected natural product is exactly the original bit-selected
product on the same decreasing four-prime tuple.

These are finite exponent and arithmetic facts. No density estimate,
distribution theorem, H248 soundness or mean/count bound is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenInteriorArithmetic

noncomputable section
open scoped BigOperators
open Classical
open U11Integral U1011OriginalSixteenPolicyBank U1011OriginalSixteenArithmeticProducts
open P5U1011JointOverlap

def gateValues (p : Policy) (v : LogFour) : Finset ℝ :=
  insert (1 / 2) ((Finset.univ.image (fun j : Fin 4 => fullSquare j v)) ∪
    if p.val < 15 then
      ((Finset.univ.filter (fun j : Fin 4 => ¬Selected p j)).image (fun j => selectedSquare p j v))
    else {(1 + v 0) / 2})

theorem gateValues_nonempty (p : Policy) (v : LogFour) : (gateValues p v).Nonempty :=
  ⟨1 / 2, Finset.mem_insert_self _ _⟩

def gate (p : Policy) (v : LogFour) : ℝ := (gateValues p v).max' (gateValues_nonempty p v)
def interior (p : Policy) (v : LogFour) : ℝ := (gate p v + cap p v) / 2

theorem gateValues_lt_cap (p : Policy) (v : LogFour) (he : TypedEligible p v) :
    ∀ a ∈ gateValues p v, a < cap p v := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact he.1
  · rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp ha
      exact he.2.1 j
    · by_cases hp : p.val < 15
      · have hextra : ∀ j : Fin 4, ¬Selected p j → selectedSquare p j v < cap p v := by
          simpa only [if_pos hp] using he.2.2
        have ha' : a ∈ (Finset.univ.filter (fun j : Fin 4 => ¬Selected p j)).image
            (fun j => selectedSquare p j v) := by simpa only [if_pos hp] using ha
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha'
        exact hextra j (Finset.mem_filter.mp hj).2
      · have hextra : (1 + v 0) / 2 < cap p v ∧ v 0 < (25 / 128 : ℝ) := by
          simpa only [if_neg hp] using he.2.2
        have ha' : a = (1 + v 0) / 2 := by simpa only [if_neg hp,Finset.mem_singleton] using ha
        rw [ha']
        exact hextra.1

theorem gate_lt_cap (p : Policy) (v : LogFour) (he : TypedEligible p v) :
    gate p v < cap p v := by
  exact gateValues_lt_cap p v he _ (Finset.max'_mem _ _)

/-- One interior is constructed from ALL required tests. The W x-bound is
preserved separately and is never replaced by a selected-mask square. -/
theorem interior_admissible (p : Policy) (v : LogFour) (he : TypedEligible p v) :
    (1 / 2 : ℝ) < interior p v ∧
      (∀ j : Fin 4, fullSquare j v < interior p v) ∧
      (if p.val < 15 then ∀ j : Fin 4, ¬Selected p j → selectedSquare p j v < interior p v
       else (1 + v 0) / 2 < interior p v ∧ v 0 < (25 / 128 : ℝ)) ∧
      interior p v < cap p v := by
  have hgc := gate_lt_cap p v he
  have hgi : gate p v < interior p v := by unfold interior; linarith
  have hic : interior p v < cap p v := by unfold interior; linarith
  have hbelow (a : ℝ) (ha : a ∈ gateValues p v) : a < interior p v :=
    (Finset.le_max' _ _ ha).trans_lt hgi
  refine ⟨hbelow _ (Finset.mem_insert_self _ _),?_,?_,hic⟩
  · intro j
    apply hbelow
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
  · by_cases hp : p.val < 15
    · simp only [if_pos hp]
      intro j hj
      apply hbelow
      apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_union_right
      simp only [if_pos hp]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
    · simp only [if_neg hp]
      have hextra : (1 + v 0) / 2 < cap p v ∧ v 0 < (25 / 128 : ℝ) := by
        simpa only [if_neg hp] using he.2.2
      refine ⟨hbelow _ ?_,hextra.2⟩
      apply Finset.mem_insert.mpr
      apply Or.inr
      apply Finset.mem_union_right
      simp only [if_neg hp,Finset.mem_singleton]

theorem selectedProduct_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) (p : Policy) :
    (N : ℝ) ^ selectedMass p (coordinates N t) = (selectedProduct p t : ℝ) := by
  have hmass : selectedMass p (coordinates N t) =
      ∑ i ∈ selectedIndices p, coordinates N t i := by
    simp [selectedMass,selectedIndices,Finset.sum_filter]
  rw [hmass]
  exact subproduct_rpow hN ht (selectedIndices p)

/-- The two original selected-subproduct cap tests produce the actual
strict critical interval of the SAME bit-selected natural subproduct.
W is excluded by its actual branch tag, not silently assigned mask16. -/
theorem actual_selected_critical_interval {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (p : Policy) (hp : p.val < 15) {nu : ℝ}
    (hnu : nu < cap p (coordinates N t)) :
    (N : ℝ) ^ (2 * nu - 1) < (selectedProduct p t : ℝ) ∧
      (selectedProduct p t : ℝ) < (N : ℝ) ^ ((19 / 32 : ℝ) - (2 / 3 : ℝ) * nu) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hc : nu < min ((1 + selectedMass p (coordinates N t)) / 2)
      ((57 / 64 : ℝ) - (3 / 2 : ℝ) * selectedMass p (coordinates N t)) := by
    simpa only [cap,if_pos hp] using hnu
  have hleft := hc.trans_le (min_le_left _ _)
  have hright := hc.trans_le (min_le_right _ _)
  simp only [← selectedProduct_rpow hN ht p]
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith),
    Real.rpow_lt_rpow_of_exponent_lt hNr (by linarith)⟩

theorem fullPrefix_rpow {N : ℕ} (hN : 1 < N) {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ jointSelector N E) :
    (N : ℝ) ^ U11SelectedLargest.prefixSum (coordinates N t) = (fullPrefix t : ℝ) := by
  have hsum : U11SelectedLargest.prefixSum (coordinates N t) =
      ∑ i : Fin 4, coordinates N t i := by
    simp [U11SelectedLargest.prefixSum,Fin.sum_univ_succ]
    <;> ring
  rw [hsum]
  exact subproduct_rpow hN ht Finset.univ

/-- Exact physical residual denominator: all four specified primes are
removed once. A selected subproduct cannot replace this full prefix. -/
theorem actual_residual_level {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E) (nu : ℝ) :
    (N : ℝ) ^ (nu - U11SelectedLargest.prefixSum (coordinates N t)) =
      (N : ℝ) ^ nu / (fullPrefix t : ℝ) := by
  rw [Real.rpow_sub (by exact_mod_cast (zero_lt_one.trans hN)),fullPrefix_rpow hN ht]

/-- In particular the constructed actual mask interior, not its endpoint,
has the original critical interval. -/
theorem actual_interior_critical_interval {N : ℕ} (hN : 1 < N)
    {E : ℕ × ℕ → Prop} {t : Four} (ht : t ∈ jointSelector N E)
    (p : Policy) (hp : p.val < 15) (he : TypedEligible p (coordinates N t)) :
    (N : ℝ) ^ (2 * interior p (coordinates N t) - 1) < (selectedProduct p t : ℝ) ∧
      (selectedProduct p t : ℝ) < (N : ℝ) ^
        ((19 / 32 : ℝ) - (2 / 3 : ℝ) * interior p (coordinates N t)) :=
  actual_selected_critical_interval hN ht p hp (interior_admissible p _ he).2.2.2

end
end ImbalancedChen.P5Z.U1011OriginalSixteenInteriorArithmetic
