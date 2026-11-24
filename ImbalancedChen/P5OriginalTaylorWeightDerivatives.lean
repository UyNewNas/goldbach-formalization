import ImbalancedChen.P5OriginalTaylorAffineRatioDerivatives

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original reciprocal-prime weight has exponent TWO in the fifth slot
and exponent ONE in each other slot. This file identifies the coordinate
curve with the actual weight, proves both derivatives, and supplies the
original wmax, k_i and q_i bounds on the raw parent box.

The complete weighted G Hessian, its five-dimensional midpoint integral,
actual archive branch/range instances, and saved old floor remain open.
-/
namespace ImbalancedChen.P5OriginalTaylorWeightDerivatives
noncomputable section
open scoped Classical BigOperators
open Set
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OriginalTaylorActualSignedKernel

def otherWeight (t : Fin 5 → ℝ) (i : Fin 5) : ℝ :=
  ∏ k ∈ Finset.univ.erase i, 1 / t k

def axisPower (i : Fin 5) : ℝ := if i = 4 then 2 else 1

def axisWeight (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  if i = 4 then 4 * otherWeight t i / x ^ 2
  else 4 * otherWeight t i / (t 4 * x)

def axisWeightSlope (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  -axisPower i * axisWeight t i x / x

def axisWeightCurvature (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  axisPower i * (axisPower i + 1) * axisWeight t i x / x ^ 2

def pilotWMax (raw : FifthWireRow) : ℝ :=
  originalTaylorWeight (fun k => (raw.lower k : ℝ))

def pilotK (raw : FifthWireRow) (i : Fin 5) : ℝ :=
  axisPower i / (raw.lower i : ℝ)

def pilotR (raw : FifthWireRow) (i : Fin 5) : ℝ :=
  axisPower i * (axisPower i + 1) / (raw.lower i : ℝ) ^ 2

theorem axisPower_nonneg (i : Fin 5) : 0 ≤ axisPower i := by
  by_cases hi : i = 4 <;> norm_num [axisPower, hi]

theorem original_weight_on_axis (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) :
    originalTaylorWeight (Function.update t i x) = axisWeight t i x := by
  have hp : (∏ k : Fin 5, 1 / Function.update t i x k) = otherWeight t i * (1 / x) := by
    rw [← Finset.prod_erase_mul Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · unfold otherWeight
      apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [Function.update, hki, Ne.symm hki]
    · simp
  unfold originalTaylorWeight
  rw [hp]
  by_cases hi : i = 4
  · subst i
    simp [axisWeight, div_eq_mul_inv, pow_two, mul_inv_rev] <;> ring
  · simp [axisWeight, Function.update, hi, Ne.symm hi, div_eq_mul_inv, mul_inv_rev]
    <;> ring

theorem axisWeight_at_base (t : Fin 5 → ℝ) (i : Fin 5) :
    axisWeight t i (t i) = originalTaylorWeight t := by
  have h := (original_weight_on_axis t i (t i)).symm
  simpa using h

theorem hasDerivAt_axisWeight (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ)
    (h4 : t 4 ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (axisWeight t i) (axisWeightSlope t i x) x := by
  by_cases hi : i = 4
  · have hd := (hasDerivAt_const x (4 * otherWeight t i)).div
      (hasDerivAt_pow 2 x) (pow_ne_zero 2 hx)
    convert hd using 1
    · funext y
      simp [axisWeight, hi]
    · simp only [axisWeightSlope, axisPower, axisWeight, if_pos hi]
      field_simp [hx]
      <;> ring
  · have hd := (hasDerivAt_const x (4 * otherWeight t i)).div
      ((hasDerivAt_id x).const_mul (t 4)) (mul_ne_zero h4 hx)
    convert hd using 1
    · funext y
      simp [axisWeight, hi]
    · simp only [axisWeightSlope, axisPower, axisWeight, if_neg hi]
      field_simp [h4, hx]
      <;> ring

theorem hasDerivAt_axisWeightSlope (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ)
    (h4 : t 4 ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (axisWeightSlope t i) (axisWeightCurvature t i x) x := by
  have hd := ((hasDerivAt_axisWeight t i x h4 hx).const_mul (-axisPower i)).div
    (hasDerivAt_id x) hx
  convert hd using 1
  · rfl
  · simp only [axisWeightCurvature, axisWeightSlope]
    field_simp [hx]
    <;> ring

theorem original_weight_axis_hasDerivAt (t : Fin 5 → ℝ) (i : Fin 5)
    (ht : ∀ k, 0 < t k) :
    HasDerivAt (fun x => originalTaylorWeight (Function.update t i x))
      (axisWeightSlope t i (t i)) (t i) := by
  simpa only [original_weight_on_axis] using
    hasDerivAt_axisWeight t i (t i) (ht 4).ne' (ht i).ne'

theorem original_weight_le_pilotWMax (raw : FifthWireRow)
    (hl : ∀ k, 0 < (raw.lower k : ℝ))
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) :
    originalTaylorWeight t ≤ pilotWMax raw := by
  have hp : ∀ k, 0 < t k := fun k => (hl k).trans_le (ht k).1
  have hprod : (∏ k : Fin 5, 1 / t k) ≤ ∏ k : Fin 5, 1 / (raw.lower k : ℝ) := by
    apply Finset.prod_le_prod
    · intro k _
      exact one_div_nonneg.mpr (hp k).le
    · intro k _
      exact div_le_div_of_nonneg_left (by norm_num) (hl k) (ht k).1
  have hlast : 4 / t 4 ≤ 4 / (raw.lower 4 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (hl 4) (ht 4).1
  exact mul_le_mul hlast hprod
    (Finset.prod_nonneg (fun k _ => one_div_nonneg.mpr (hp k).le))
    (div_nonneg (by norm_num) (hl 4).le)

theorem pilotWMax_nonneg (raw : FifthWireRow) (hl : ∀ k, 0 < (raw.lower k : ℝ)) :
    0 ≤ pilotWMax raw := originalTaylorWeight_nonneg _ hl

theorem original_weightSlope_le_pilotK (raw : FifthWireRow)
    (hl : ∀ k, 0 < (raw.lower k : ℝ))
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (i : Fin 5) :
    |axisWeightSlope t i (t i)| ≤ pilotWMax raw * pilotK raw i := by
  have hp : ∀ k, 0 < t k := fun k => (hl k).trans_le (ht k).1
  have hW := originalTaylorWeight_nonneg t hp
  have hmax := original_weight_le_pilotWMax raw hl t ht
  have hmax0 := pilotWMax_nonneg raw hl
  have hpower := axisPower_nonneg i
  simp only [axisWeightSlope, axisWeight_at_base, abs_div, abs_mul, abs_neg,
    abs_of_nonneg hpower, abs_of_nonneg hW, abs_of_pos (hp i)]
  calc
    axisPower i * originalTaylorWeight t / t i ≤
        axisPower i * pilotWMax raw / t i :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hpower) (hp i).le
    _ ≤ axisPower i * pilotWMax raw / (raw.lower i : ℝ) :=
      div_le_div_of_nonneg_left (mul_nonneg hpower hmax0) (hl i) (ht i).1
    _ = pilotWMax raw * pilotK raw i := by unfold pilotK; ring

theorem original_weightCurvature_le_pilotR (raw : FifthWireRow)
    (hl : ∀ k, 0 < (raw.lower k : ℝ))
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (i : Fin 5) :
    |axisWeightCurvature t i (t i)| ≤ pilotWMax raw * pilotR raw i := by
  have hp : ∀ k, 0 < t k := fun k => (hl k).trans_le (ht k).1
  have hW := originalTaylorWeight_nonneg t hp
  have hmax := original_weight_le_pilotWMax raw hl t ht
  have hmax0 := pilotWMax_nonneg raw hl
  have hpower := axisPower_nonneg i
  have hfactor : 0 ≤ axisPower i * (axisPower i + 1) := by positivity
  have hsquare : (raw.lower i : ℝ) ^ 2 ≤ (t i) ^ 2 :=
    (sq_le_sq₀ (hl i).le (hp i).le).2 (ht i).1
  have hcurv : 0 ≤ axisWeightCurvature t i (t i) := by
    rw [axisWeightCurvature, axisWeight_at_base]
    exact div_nonneg (mul_nonneg hfactor hW) (sq_nonneg _)
  rw [abs_of_nonneg hcurv, axisWeightCurvature, axisWeight_at_base]
  calc
    axisPower i * (axisPower i + 1) * originalTaylorWeight t / (t i) ^ 2 ≤
        axisPower i * (axisPower i + 1) * pilotWMax raw / (t i) ^ 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hmax hfactor) (sq_nonneg _)
    _ ≤ axisPower i * (axisPower i + 1) * pilotWMax raw / (raw.lower i : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hfactor hmax0) (sq_pos_of_pos (hl i)) hsquare
    _ = pilotWMax raw * pilotR raw i := by unfold pilotR; ring

end
end ImbalancedChen.P5OriginalTaylorWeightDerivatives
