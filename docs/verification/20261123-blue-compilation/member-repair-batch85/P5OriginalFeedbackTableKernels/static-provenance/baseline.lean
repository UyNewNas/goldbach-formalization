import ImbalancedChen.Part5RenewalTablePositivity
import ImbalancedChen.P5OriginalActionMassBound

/-!
Actual finite-table feedback integrands and exact closed-cell decomposition.
SOURCE ONLY. lower=true selects h's [2,5] guard; lower=false selects H's
[1,5] guard. No max-two clamp is inserted into W1/W2 child profiles.
All singleton seam atoms are retained after composition; no null pullback
or count-soundness premise is hidden in these exact integral identities.
-/

namespace ImbalancedChen.P5OriginalFeedbackTableKernels

noncomputable section

open Set MeasureTheory
open scoped BigOperators
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open Part5UpperTables.Renewal

def tableAtomSet (lower : Bool) (b : FloorAtom) : Set ℝ :=
  if lower then floorAtomSet b else upperAtomSet b

def tableFunction (lower : Bool) (nums : Fin 200 → ℤ) (s : ℝ) : ℝ :=
  ∑ b : FloorAtom, (tableAtomSet lower b).indicator (fun _ => floorAtomValue nums b) s

theorem tableFunction_lower (nums : Fin 200 → ℤ) : tableFunction true nums = floorStep nums := rfl
theorem tableFunction_upper (nums : Fin 200 → ℤ) : tableFunction false nums = upperFloor nums := rfl

theorem measurableSet_tableAtomSet (lower : Bool) (b : FloorAtom) :
    MeasurableSet (tableAtomSet lower b) := by
  cases lower
  · exact measurableSet_upperAtomSet b
  · exact measurableSet_floorAtomSet b

theorem measurable_tableFunction (lower : Bool) (nums : Fin 200 → ℤ) :
    Measurable (tableFunction lower nums) := by
  cases lower
  · exact measurable_upperFloor nums
  · exact measurable_floorStep nums

theorem floorStep_bounds_of_data {nums : Fin 200 → ℤ} (hn : UnitBoundedData nums) (s : ℝ) :
    0 ≤ floorStep nums s ∧ floorStep nums s ≤ 1 := by
  by_cases hs : s ∈ Icc (2 : ℝ) 5
  · rw [← upperFloor_eq_lowerFloor_of_two_le nums hs.1]
    exact upperFloor_bounds_of_data hn s
  · rw [floorStep_outside nums hs]
    exact ⟨le_rfl, zero_le_one⟩

theorem tableFunction_bounds (lower : Bool) {nums : Fin 200 → ℤ}
    (hn : UnitBoundedData nums) (s : ℝ) :
    0 ≤ tableFunction lower nums s ∧ tableFunction lower nums s ≤ 1 := by
  cases lower
  · exact upperFloor_bounds_of_data hn s
  · exact floorStep_bounds_of_data hn s

section General

variable {X : Type*} [MeasurableSpace X]

def tablePullback (lower : Bool) (p : X → ℝ) (b : FloorAtom) : Set X :=
  p ⁻¹' tableAtomSet lower b

theorem measurableSet_tablePullback (lower : Bool) {p : X → ℝ}
    (hp : Measurable p) (b : FloorAtom) : MeasurableSet (tablePullback lower p b) :=
  (measurableSet_tableAtomSet lower b).preimage hp

def weightedTable (lower : Bool) (nums : Fin 200 → ℤ) (p W : X → ℝ) (x : X) : ℝ :=
  W x * tableFunction lower nums (p x)

theorem measurable_weightedTable (lower : Bool) (nums : Fin 200 → ℤ)
    {p W : X → ℝ} (hp : Measurable p) (hW : Measurable W) :
    Measurable (weightedTable lower nums p W) :=
  hW.mul ((measurable_tableFunction lower nums).comp hp)

/-- Exact finite decomposition keeps the literal profile and every closed-knot value. -/
theorem weightedTable_eq_atom_sum (lower : Bool) (nums : Fin 200 → ℤ)
    (p W : X → ℝ) (x : X) :
    weightedTable lower nums p W x =
      ∑ b : FloorAtom, floorAtomValue nums b * (tablePullback lower p b).indicator W x := by
  unfold weightedTable tableFunction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : p x ∈ tableAtomSet lower b <;> simp [tablePullback, hb, mul_comm]

theorem integrableOn_weightedTable (lower : Bool) (nums : Fin 200 → ℤ)
    {p W : X → ℝ} (hp : Measurable p) {D : Set X} (hD : MeasurableSet D)
    {μ : Measure X} (hW : IntegrableOn W D μ) :
    IntegrableOn (weightedTable lower nums p W) D μ := by
  have hi : IntegrableOn (fun x => ∑ b : FloorAtom,
      floorAtomValue nums b * (tablePullback lower p b).indicator W x) D μ :=
    integrable_finsetSum _ (fun b _ =>
      (hW.indicator (measurableSet_tablePullback lower hp b)).const_mul _)
  apply hi.congr_fun ?_ hD
  intro x _
  exact (weightedTable_eq_atom_sum lower nums p W x).symm

theorem weightedTable_integral_atom_sum (lower : Bool) (nums : Fin 200 → ℤ)
    {p W : X → ℝ} (hp : Measurable p) {D : Set X} (hD : MeasurableSet D)
    {μ : Measure X} (hW : IntegrableOn W D μ) :
    (∫ x in D, weightedTable lower nums p W x ∂μ) =
      ∑ b : FloorAtom, floorAtomValue nums b *
        ∫ x in D ∩ tablePullback lower p b, W x ∂μ := by
  calc
    _ = ∫ x in D, ∑ b : FloorAtom,
        floorAtomValue nums b * (tablePullback lower p b).indicator W x ∂μ := by
      apply setIntegral_congr_fun hD
      intro x _
      exact weightedTable_eq_atom_sum lower nums p W x
    _ = ∑ b : FloorAtom, ∫ x in D,
        floorAtomValue nums b * (tablePullback lower p b).indicator W x ∂μ :=
      integral_finsetSum _ (fun b _ =>
        (hW.indicator (measurableSet_tablePullback lower hp b)).const_mul _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      rw [integral_const_mul, setIntegral_indicator (measurableSet_tablePullback lower hp b)]

theorem weightedTable_bounds (lower : Bool) {nums : Fin 200 → ℤ}
    (hn : UnitBoundedData nums) (p W : X → ℝ) (x : X) (hW : 0 ≤ W x) :
    0 ≤ weightedTable lower nums p W x ∧ weightedTable lower nums p W x ≤ W x := by
  have ht := tableFunction_bounds lower hn (p x)
  exact ⟨mul_nonneg hW ht.1,
    by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hW⟩

end General
end
end ImbalancedChen.P5OriginalFeedbackTableKernels
