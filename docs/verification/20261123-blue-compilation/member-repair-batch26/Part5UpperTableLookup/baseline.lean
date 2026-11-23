import ImbalancedChen.Part5OriginalUpsilon5FloorKernel
import ImbalancedChen.Part5AdoptedUpperTableData

/-!
Actual upper-table scalar lookup and clamped root queries. SOURCE ONLY.
Raw H lookup is guarded by [1,5], whereas lower h lookup is guarded by [2,5].
The original upper root queries max(2,s), so the existing [2,5] finite atoms
give exactly that clamped lookup. At a knot H uses the adjacent MINIMUM;
the upper coefficient 1-H consequently uses the adjacent MAXIMUM.
H430 is exposed for U3/U4 only by the concrete adapters in a separate file.
-/

namespace ImbalancedChen.Part5UpperTables

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary

def upperAtomSet : FloorAtom → Set ℝ
  | .inl i => Icc 1 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
  | .inr j => Icc 1 5 ∩ {floorGrid j.val}

theorem measurableSet_upperAtomSet (b : FloorAtom) : MeasurableSet (upperAtomSet b) := by
  cases b with
  | inl i => exact measurableSet_Icc.inter measurableSet_Ioo
  | inr j => exact measurableSet_Icc.inter (measurableSet_singleton _)

def upperFloor (nums : Fin 200 → ℤ) (s : ℝ) : ℝ :=
  ∑ b : FloorAtom, (upperAtomSet b).indicator (fun _ => floorAtomValue nums b) s

theorem measurable_upperFloor (nums : Fin 200 → ℤ) : Measurable (upperFloor nums) := by
  apply Finset.measurable_sum
  intro b _
  exact measurable_const.indicator (measurableSet_upperAtomSet b)

theorem upperFloor_outside (nums : Fin 200 → ℤ) {s : ℝ} (hs : s ∉ Icc (1 : ℝ) 5) :
    upperFloor nums s = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  have hb : s ∉ upperAtomSet b := by cases b <;> exact fun h => hs h.1
  exact indicator_of_notMem hb _

theorem norm_upperFloor_le (nums : Fin 200 → ℤ) (s : ℝ) :
    ‖upperFloor nums s‖ ≤ floorBound nums := by
  unfold upperFloor floorBound
  calc
    ‖∑ b : FloorAtom, (upperAtomSet b).indicator (fun _ => floorAtomValue nums b) s‖ ≤
        ∑ b : FloorAtom, ‖(upperAtomSet b).indicator (fun _ => floorAtomValue nums b) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ b : FloorAtom, ‖floorAtomValue nums b‖ := by
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : s ∈ upperAtomSet b
      · simp only [indicator_of_mem hb]
        exact le_rfl
      · simp only [indicator_of_notMem hb, norm_zero]
        exact norm_nonneg _

theorem upperFloor_eq_lowerFloor_of_two_le (nums : Fin 200 → ℤ) {s : ℝ}
    (hs : 2 ≤ s) : upperFloor nums s = floorStep nums s := by
  unfold upperFloor floorStep
  apply Finset.sum_congr rfl
  intro b _
  have hs1 : 1 ≤ s := by linarith
  cases b <;> simp [upperAtomSet, floorAtomSet, hs, hs1]

def upperRoot (nums : Fin 200 → ℤ) (s : ℝ) : ℝ := upperFloor nums (max 2 s)

theorem upperRoot_eq_floorStep (nums : Fin 200 → ℤ) (s : ℝ) :
    upperRoot nums s = floorStep nums (max 2 s) :=
  upperFloor_eq_lowerFloor_of_two_le nums (le_max_left _ _)

theorem measurable_upperRoot (nums : Fin 200 → ℤ) : Measurable (upperRoot nums) :=
  (measurable_upperFloor nums).comp (measurable_const.max measurable_id)

theorem norm_upperRoot_le (nums : Fin 200 → ℤ) (s : ℝ) :
    ‖upperRoot nums s‖ ≤ floorBound nums := norm_upperFloor_le _ _

/-- This is the true polarity of an H-floor at a seam in an upper cost. -/
theorem upper_cost_min_eq_max (x y L : ℝ) (hL : 0 < L) :
    4 * (1 - min x y) / L = max (4 * (1 - x) / L) (4 * (1 - y) / L) := by
  by_cases hxy : x ≤ y
  · have hc : 4 * (1 - y) / L ≤ 4 * (1 - x) / L :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    rw [min_eq_left hxy, max_eq_left hc]
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hc : 4 * (1 - x) / L ≤ 4 * (1 - y) / L :=
      div_le_div_of_nonneg_right (by linarith) hL.le
    rw [min_eq_right hyx, max_eq_right hc]

def H248 : ℝ → ℝ := upperFloor H248Numerators
def H430 : ℝ → ℝ := upperFloor H430Numerators

theorem measurable_H248 : Measurable H248 := measurable_upperFloor _
theorem measurable_H430 : Measurable H430 := measurable_upperFloor _
theorem norm_H248_le (s : ℝ) : ‖H248 s‖ ≤ floorBound H248Numerators := norm_upperFloor_le _ _
theorem norm_H430_le (s : ℝ) : ‖H430 s‖ ≤ floorBound H430Numerators := norm_upperFloor_le _ _

section FiniteIntegral

variable {X : Type*} [MeasurableSpace X]

def rootAtom (p : X → ℝ) (b : FloorAtom) : Set X :=
  (fun x => max 2 (p x)) ⁻¹' floorAtomSet b

theorem measurableSet_rootAtom {p : X → ℝ} (hp : Measurable p) (b : FloorAtom) :
    MeasurableSet (rootAtom p b) :=
  (measurableSet_floorAtomSet b).preimage (measurable_const.max hp)

theorem upperRoot_mul_eq_finite_sum (nums : Fin 200 → ℤ) (p W : X → ℝ) (x : X) :
    upperRoot nums (p x) * W x =
      ∑ b : FloorAtom, floorAtomValue nums b * (rootAtom p b).indicator W x := by
  rw [upperRoot_eq_floorStep]
  unfold floorStep
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : max 2 (p x) ∈ floorAtomSet b <;> simp [rootAtom, hb]

theorem integrableOn_upperRoot_mul (nums : Fin 200 → ℤ) {p W : X → ℝ}
    (hp : Measurable p) {S : Set X} (hS : MeasurableSet S)
    {μ : Measure X} (hW : IntegrableOn W S μ) :
    IntegrableOn (fun x => upperRoot nums (p x) * W x) S μ := by
  have hi : IntegrableOn (fun x => ∑ b : FloorAtom,
      floorAtomValue nums b * (rootAtom p b).indicator W x) S μ :=
    integrable_finsetSum _ (fun b _ =>
      (hW.indicator (measurableSet_rootAtom hp b)).const_mul _)
  apply hi.congr_fun ?_ hS
  intro x _
  exact (upperRoot_mul_eq_finite_sum nums p W x).symm

/-- Finite-atom exact integral dictionary; signed W and zero-mass pieces are allowed. -/
theorem upperRoot_integral_finite_fubini (nums : Fin 200 → ℤ) {p W : X → ℝ}
    (hp : Measurable p) {S : Set X} (hS : MeasurableSet S)
    {μ : Measure X} (hW : IntegrableOn W S μ) :
    (∫ x in S, upperRoot nums (p x) * W x ∂μ) =
      ∑ b : FloorAtom, floorAtomValue nums b * ∫ x in S ∩ rootAtom p b, W x ∂μ := by
  calc
    _ = ∫ x in S, ∑ b : FloorAtom,
        floorAtomValue nums b * (rootAtom p b).indicator W x ∂μ := by
      apply setIntegral_congr_fun hS
      intro x _
      exact upperRoot_mul_eq_finite_sum nums p W x
    _ = ∑ b : FloorAtom, ∫ x in S,
        floorAtomValue nums b * (rootAtom p b).indicator W x ∂μ :=
      integral_finsetSum _ (fun b _ =>
        (hW.indicator (measurableSet_rootAtom hp b)).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [integral_const_mul, setIntegral_indicator (measurableSet_rootAtom hp b)]

end FiniteIntegral
end

end ImbalancedChen.Part5UpperTables
