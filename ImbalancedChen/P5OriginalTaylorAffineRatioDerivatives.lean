import ImbalancedChen.P5OriginalTaylorAffineBranchBinding

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal affine residual is (level(t) - sum(t))/t_5. Its coordinate
first and second derivatives, and the ORIGINAL D, E, T bounds from the
pilot, are proved here. In particular the last coordinate differentiates
the moving denominator; it is not treated like the first four slots.

This is a necessary analytic supplier, not a stored Taylor integral
licence. Actual smooth-row branch/range instances, the full weighted
Hessian, five-dimensional midpoint passage and saved-floor binding are
not asserted by this file.
-/
namespace ImbalancedChen.P5OriginalTaylorAffineRatioDerivatives
noncomputable section
open scoped Classical BigOperators
open Set
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OldFifthPointwiseQ P5OriginalTaylorAffineBranchBinding

def residualCoefficient (a : Affine5) (i : Fin 5) : ℝ :=
  (a.coefficient i : ℝ) - 1

def affineArgument (a : Affine5) (t : Fin 5 → ℝ) : ℝ := residual (a.eval t) t

/-- The original affine numerator after subtraction of all five primes. -/
def axisArgument (a : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  (a.eval t - sum5 t + residualCoefficient a i * (x - t i)) /
    (if i = 4 then x else t 4)

def axisSlope (a : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  if i = 4 then (residualCoefficient a i - axisArgument a t i x) / x
  else residualCoefficient a i / t 4

def axisCurvature (a : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) : ℝ :=
  if i = 4 then -2 * axisSlope a t i x / x else 0

theorem affine_eval_update (a : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) :
    a.eval (Function.update t i x) = a.eval t + (a.coefficient i : ℝ) * (x - t i) := by
  have hu : (∑ k : Fin 5, (a.coefficient k : ℝ) * Function.update t i x k) =
      (∑ k ∈ Finset.univ.erase i, (a.coefficient k : ℝ) * t k) +
        (a.coefficient i : ℝ) * x := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    congr 1
    · apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [Function.update, hki, Ne.symm hki]
    · simp
  have ht := Finset.sum_erase_add (Finset.univ : Finset (Fin 5))
    (fun k => (a.coefficient k : ℝ) * t k) (Finset.mem_univ i)
  unfold Affine5.eval
  rw [hu, ← ht]
  ring

theorem sum5_update (t : Fin 5 → ℝ) (i : Fin 5) (x : ℝ) :
    sum5 (Function.update t i x) = sum5 t + (x - t i) := by
  have h := affine_eval_update (indicatorAffine 1 Finset.univ) t i x
  simpa [indicatorAffine_eval, indicatorAffine, sum5] using h

theorem original_argument_on_axis (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) :
    affineArgument a (Function.update t i x) = axisArgument a t i x := by
  unfold affineArgument residual
  rw [affine_eval_update, sum5_update]
  have hd : Function.update t i x 4 = if i = 4 then x else t 4 := by
    by_cases hi : i = 4
    · subst i
      simp
    · simp [Function.update, hi, Ne.symm hi]
  rw [hd]
  unfold axisArgument residualCoefficient
  congr 1
  ring

theorem axisArgument_at_base (a : Affine5) (t : Fin 5 → ℝ) (i : Fin 5) :
    axisArgument a t i (t i) = affineArgument a t := by
  by_cases hi : i = 4
  · subst i
    simp [axisArgument, affineArgument, residual]
  · simp [axisArgument, affineArgument, residual, hi]

/-- First derivative of the original affine residual along an axis. -/
theorem hasDerivAt_axisArgument (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : i = 4 → x ≠ 0) :
    HasDerivAt (axisArgument a t i) (axisSlope a t i x) x := by
  have hn : HasDerivAt
      (fun y => a.eval t - sum5 t + residualCoefficient a i * (y - t i))
      (residualCoefficient a i) x := by
    simpa only [mul_one, zero_add] using
      (hasDerivAt_const x (a.eval t - sum5 t)).add
        (((hasDerivAt_id x).sub_const (t i)).const_mul (residualCoefficient a i))
  by_cases hi : i = 4
  · have hd := hn.div (hasDerivAt_id x) (hx hi)
    convert hd using 1
    · funext y
      simp [axisArgument, hi]
    · simp only [axisSlope, axisArgument, if_pos hi]
      field_simp [hx hi]
      <;> ring
  · simpa only [axisArgument, axisSlope, if_neg hi] using hn.div_const (t 4)

/-- Second derivative of the SAME last-coordinate quotient. -/
theorem hasDerivAt_axisSlope (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (x : ℝ) (h4 : t 4 ≠ 0) (hx : i = 4 → x ≠ 0) :
    HasDerivAt (axisSlope a t i) (axisCurvature a t i x) x := by
  by_cases hi : i = 4
  · have hn := (hasDerivAt_const x (residualCoefficient a i)).sub
      (hasDerivAt_axisArgument a t i x h4 hx)
    have hd := hn.div (hasDerivAt_id x) (hx hi)
    convert hd using 1
    · funext y
      simp [axisSlope, hi]
    · simp only [axisCurvature, axisSlope, if_pos hi]
      field_simp [hx hi]
      <;> ring
  · simpa only [axisSlope, axisCurvature, if_neg hi] using
      hasDerivAt_const x (residualCoefficient a i / t 4)

theorem original_argument_axis_hasDerivAt (a : Affine5) (t : Fin 5 → ℝ)
    (i : Fin 5) (h4 : t 4 ≠ 0) :
    HasDerivAt (fun x => affineArgument a (Function.update t i x))
      (axisSlope a t i (t i)) (t i) := by
  simpa only [original_argument_on_axis] using
    hasDerivAt_axisArgument a t i (t i) h4 (fun hi => by simpa [hi] using h4)

def pilotD (raw : FifthWireRow) (a : Affine5) (sMax : ℝ) (i : Fin 5) : ℝ :=
  if i = 4 then (sMax - residualCoefficient a i) / (raw.lower 4 : ℝ)
  else |residualCoefficient a i| / (raw.lower 4 : ℝ)

def pilotE (raw : FifthWireRow) (a : Affine5) (sMax : ℝ) (i : Fin 5) : ℝ :=
  if i = 4 then 2 * pilotD raw a sMax i / (raw.lower 4 : ℝ) else 0

def pilotT (raw : FifthWireRow) (new old : Affine5) (delta : ℝ) (i : Fin 5) : ℝ :=
  if i = 4 then
    (|residualCoefficient new i - residualCoefficient old i| + delta) / (raw.lower 4 : ℝ)
  else |residualCoefficient new i - residualCoefficient old i| / (raw.lower 4 : ℝ)

/-- All original tent residual coefficients are negative. The inherited
W also has this property; no unsupported sign of a raw slope is assumed. -/
theorem tent_residualCoefficient_nonpos (I : Finset (Fin 5)) (side : Bool) (i : Fin 5) :
    residualCoefficient (tentPlane I side) i ≤ 0 := by
  cases side <;> by_cases hi : i ∈ I <;>
    norm_num [residualCoefficient, tentPlane, Affine5.add, constantAffine, indicatorAffine, hi]

theorem selected_old_residualCoefficient_nonpos
    (sides : OldSides) (selected : Option OldMask) (i : Fin 5) :
    residualCoefficient (selectedOldPlane sides selected) i ≤ 0 := by
  cases selected with
  | none =>
      by_cases hi : i = 2 <;>
        norm_num [selectedOldPlane, inheritedWPlane, residualCoefficient,
          Affine5.add, constantAffine, indicatorAffine, hi]
  | some I => exact tent_residualCoefficient_nonpos _ _ _

theorem new_residualCoefficient_nonpos (raw : FifthWireRow) (side : Bool) (i : Fin 5) :
    residualCoefficient (newPlane raw side) i ≤ 0 :=
  tent_residualCoefficient_nonpos _ _ _

/-- The original last-coordinate D uses the range of the argument,
not an independent bound for the affine numerator. -/
theorem original_axisSlope_le_pilotD
    (raw : FifthWireRow) (a : Affine5) (sMax : ℝ)
    (t : Fin 5 → ℝ) (i : Fin 5) (hl : 0 < (raw.lower 4 : ℝ))
    (ht : t ∈ rawClosedBox raw) (harg : 2 ≤ affineArgument a t)
    (hmax : affineArgument a t ≤ sMax) (hcoef : residualCoefficient a 4 ≤ 0) :
    |axisSlope a t i (t i)| ≤ pilotD raw a sMax i := by
  have ht4 : 0 < t 4 := hl.trans_le (ht 4).1
  by_cases hi : i = 4
  · subst i
    have hn : residualCoefficient a 4 - affineArgument a t ≤ 0 := by linarith
    have hm : 0 ≤ sMax - residualCoefficient a 4 := by linarith
    have habs : |axisSlope a t 4 (t 4)| =
        (affineArgument a t - residualCoefficient a 4) / t 4 := by
      rw [axisSlope, if_pos rfl, axisArgument_at_base, abs_div,
        abs_of_nonpos hn, abs_of_pos ht4]
      ring
    rw [habs]
    change _ ≤ (sMax - residualCoefficient a 4) / (raw.lower 4 : ℝ)
    exact (div_le_div_of_nonneg_right (sub_le_sub_right hmax _) ht4.le).trans
      (div_le_div_of_nonneg_left hm hl (ht 4).1)
  · simp only [axisSlope, pilotD, if_neg hi, abs_div, abs_of_pos ht4]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl (ht 4).1

theorem original_axisCurvature_le_pilotE
    (raw : FifthWireRow) (a : Affine5) (sMax : ℝ)
    (t : Fin 5 → ℝ) (i : Fin 5) (hl : 0 < (raw.lower 4 : ℝ))
    (ht : t ∈ rawClosedBox raw) (harg : 2 ≤ affineArgument a t)
    (hmax : affineArgument a t ≤ sMax) (hcoef : residualCoefficient a 4 ≤ 0) :
    |axisCurvature a t i (t i)| ≤ pilotE raw a sMax i := by
  have hd := original_axisSlope_le_pilotD raw a sMax t i hl ht harg hmax hcoef
  by_cases hi : i = 4
  · subst i
    have ht4 : 0 < t 4 := hl.trans_le (ht 4).1
    have hD : 0 ≤ pilotD raw a sMax 4 := (abs_nonneg _).trans hd
    have habs : |axisCurvature a t 4 (t 4)| = 2 * |axisSlope a t 4 (t 4)| / t 4 := by
      simp [axisCurvature, abs_div, abs_mul, abs_of_pos ht4]
    rw [habs]
    change _ ≤ 2 * pilotD raw a sMax 4 / (raw.lower 4 : ℝ)
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) ht4.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hD) hl (ht 4).1)
  · simp [axisCurvature, pilotE, hi]

/-- This preserves the correlated new-minus-old argument gap in the
last slot, exactly as the original `derivative_gap` expression. -/
theorem original_axisSlope_difference_le_pilotT
    (raw : FifthWireRow) (new old : Affine5) (delta : ℝ)
    (t : Fin 5 → ℝ) (i : Fin 5) (hl : 0 < (raw.lower 4 : ℝ))
    (ht : t ∈ rawClosedBox raw) (hon : affineArgument old t ≤ affineArgument new t)
    (hdelta : affineArgument new t - affineArgument old t ≤ delta) :
    |axisSlope new t i (t i) - axisSlope old t i (t i)| ≤ pilotT raw new old delta i := by
  have ht4 : 0 < t 4 := hl.trans_le (ht 4).1
  by_cases hi : i = 4
  · subst i
    have heq : axisSlope new t 4 (t 4) - axisSlope old t 4 (t 4) =
        ((residualCoefficient new 4 - residualCoefficient old 4) -
          (affineArgument new t - affineArgument old t)) / t 4 := by
      simp only [axisSlope, if_pos rfl, axisArgument_at_base]
      ring
    have hnum : |(residualCoefficient new 4 - residualCoefficient old 4) -
        (affineArgument new t - affineArgument old t)| ≤
        |residualCoefficient new 4 - residualCoefficient old 4| + delta := by
      exact (abs_sub _ _).trans (add_le_add_left
        (by simpa only [abs_of_nonneg (sub_nonneg.mpr hon)] using hdelta) _)
    have hdelta0 : 0 ≤ delta := (sub_nonneg.mpr hon).trans hdelta
    rw [heq, abs_div, abs_of_pos ht4]
    change _ ≤ (|residualCoefficient new 4 - residualCoefficient old 4| + delta) /
      (raw.lower 4 : ℝ)
    exact (div_le_div_of_nonneg_right hnum ht4.le).trans
      (div_le_div_of_nonneg_left (add_nonneg (abs_nonneg _) hdelta0) hl (ht 4).1)
  · have heq : axisSlope new t i (t i) - axisSlope old t i (t i) =
        (residualCoefficient new i - residualCoefficient old i) / t 4 := by
      simp only [axisSlope, if_neg hi]
      ring
    rw [heq, abs_div, abs_of_pos ht4]
    simp only [pilotT, if_neg hi]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hl (ht 4).1

end
end ImbalancedChen.P5OriginalTaylorAffineRatioDerivatives
