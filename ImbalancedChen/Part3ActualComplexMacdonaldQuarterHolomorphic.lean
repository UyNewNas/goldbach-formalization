import ImbalancedChen.Part3ActualComplexMacdonaldQuarterL1
import ImbalancedChen.Part3ActualComplexArgumentKHolomorphic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual separate-parameter holomorphy of the complex Macdonald double
integral on the strict quarter-sector. The differentiated polynomial
exponent is computed. Its extra (1+cosh(v))/t factor is absorbed into
half of the proved positive damping. Compact coefficient floors on a
closed parameter disc then give an actual L1 derivative majorant, so
dominated complex differentiation proves the derivative of the integral.
No analyticity or continuation of the integral is assumed.
-/

namespace ImbalancedChen.Part3.ActualComplexMacdonaldQuarterHolomorphic20261026b

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualComplexMacdonaldQuarterL120261026b

def exponentZDerivative (z w : ℂ) (v t : ℝ) : ℂ :=
  -(2 * z) * ((1 / (2 * t) : ℝ) : ℂ) - w * ((Real.cosh v / t : ℝ) : ℂ)

def jointZDerivative (nu z w : ℂ) (v t : ℝ) : ℂ :=
  exponentZDerivative z w v t * complexMacdonaldJoint nu z w v t

def complexMacdonaldValue (nu z w : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ p : ℝ × ℝ, complexMacdonaldJoint nu z w p.1 p.2
    ∂positiveMeasure.prod positiveMeasure

theorem complexMacdonaldJoint_hasDerivAt (nu z w : ℂ) (v t : ℝ) :
    HasDerivAt (fun x : ℂ => complexMacdonaldJoint nu x w v t)
      (jointZDerivative nu z w v t) z := by
  have hsq : HasDerivAt (fun x : ℂ => x ^ 2) (2 * z) z := by
    simpa using (hasDerivAt_id z).pow 2
  have he := ((hasDerivAt_const z (((-t / 2 : ℝ) : ℂ))).sub
    ((hsq.add_const (w ^ 2)).mul_const ((1 / (2 * t) : ℝ) : ℂ))).sub
      (((hasDerivAt_id z).mul_const w).mul_const ((Real.cosh v / t : ℝ) : ℂ))
  have hexp := he.cexp
  convert (hexp.const_mul ((t⁻¹ : ℝ) : ℂ)).mul_const
    (Complex.cosh (nu * (v : ℂ))) using 1 <;>
    dsimp only [complexMacdonaldJoint, complexMacdonaldExponent, jointZDerivative,
      exponentZDerivative] <;> ring

theorem exponentZDerivative_eq (z w : ℂ) {t : ℝ} (ht : 0 < t) (v : ℝ) :
    exponentZDerivative z w v t =
      -(z + w * (Real.cosh v : ℂ)) * ((t⁻¹ : ℝ) : ℂ) := by
  unfold exponentZDerivative
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ht.ne'] <;> ring

private theorem linear_exp_damping {delta : ℝ} (hd : 0 < delta) (x : ℝ) :
    x * Real.exp (-(delta * x)) ≤ (2 / delta) * Real.exp (-((delta / 2) * x)) := by
  let y := (delta / 2) * x
  have hy : y * Real.exp (-y) ≤ 1 := by
    apply (Real.mul_exp_neg_le_exp_neg_one y).trans
    have h := Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)
    simpa only [Real.exp_zero] using h
  have he : Real.exp (-(delta * x)) = Real.exp (-y) * Real.exp (-y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [y]
    ring
  calc
    _ = (2 / delta) * (y * Real.exp (-y)) * Real.exp (-y) := by
      rw [he]
      dsimp [y]
      field_simp [hd.ne'] <;> ring
    _ ≤ (2 / delta) * 1 * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy (by positivity : 0 ≤ 2 / delta)) (Real.exp_pos _).le
    _ = _ := by simp only [mul_one, y]

theorem positiveMacdonaldMajorant_linear_bound (nu : ℂ) {delta t : ℝ}
    (hd : 0 < delta) (ht : 0 < t) (v : ℝ) :
    ((1 + Real.cosh v) / t) * positiveMacdonaldMajorant nu delta v t ≤
      (2 / delta) * positiveMacdonaldMajorant nu (delta / 2) v t := by
  have h := mul_le_mul_of_nonneg_left (linear_exp_damping hd ((1 + Real.cosh v) / t))
    (by positivity : 0 ≤ t⁻¹ * Real.exp (-t / 2) * ‖Complex.cosh (nu * (v : ℂ))‖)
  simpa only [positiveMacdonaldMajorant, sub_eq_add_neg, Real.exp_add,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The actual derivative has an integrable real Macdonald majorant at
half the coefficient floor. All bounds on the varying complex arguments
are retained explicitly and are later obtained from a compact disc. -/
theorem jointZDerivative_norm_le (nu : ℂ) {z w : ℂ} {delta M t : ℝ}
    (hd : 0 < delta) (hM : 0 ≤ M) (hz : delta ≤ (z ^ 2).re) (hw : delta ≤ (w ^ 2).re)
    (hzw : delta ≤ (z * w).re) (hzM : ‖z‖ ≤ M) (hwM : ‖w‖ ≤ M)
    (ht : 0 < t) (v : ℝ) :
    ‖jointZDerivative nu z w v t‖ ≤
      (M * (2 / delta)) * positiveMacdonaldMajorant nu (delta / 2) v t := by
  have hcoef : ‖z + w * (Real.cosh v : ℂ)‖ ≤ M * (1 + Real.cosh v) := by
    calc
      _ ≤ ‖z‖ + ‖w * (Real.cosh v : ℂ)‖ := norm_add_le _ _
      _ = ‖z‖ + ‖w‖ * Real.cosh v := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos v)]
      _ ≤ _ := by
        have hmul := mul_le_mul_of_nonneg_right hwM (Real.cosh_pos v).le
        nlinarith
  have hJ := complexMacdonaldJoint_norm_le nu hd hz hw hzw ht v
  have hnonneg : 0 ≤ positiveMacdonaldMajorant nu delta v t := by
    unfold positiveMacdonaldMajorant
    positivity
  unfold jointZDerivative
  rw [norm_mul, exponentZDerivative_eq z w ht v, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  calc
    _ ≤ (M * (1 + Real.cosh v)) * t⁻¹ * positiveMacdonaldMajorant nu delta v t :=
      mul_le_mul (mul_le_mul_of_nonneg_right hcoef (inv_pos.mpr ht).le) hJ
        (norm_nonneg _) (by positivity)
    _ = M * (((1 + Real.cosh v) / t) * positiveMacdonaldMajorant nu delta v t) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ M * ((2 / delta) * positiveMacdonaldMajorant nu (delta / 2) v t) :=
      mul_le_mul_of_nonneg_left (positiveMacdonaldMajorant_linear_bound nu hd ht v) hM
    _ = _ := by ring

theorem complexMacdonaldValue_hasDerivAt_left (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    HasDerivAt (fun x : ℂ => complexMacdonaldValue nu x w)
      ((1 / 2 : ℂ) * ∫ p : ℝ × ℝ, jointZDerivative nu z w p.1 p.2
        ∂positiveMeasure.prod positiveMeasure) z := by
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp strictQuarterSector_isOpen z hz
  let r : ℝ := epsilon / 2
  have hr : 0 < r := half_pos hepsilon
  let S : Set (ℂ × ℂ) := (fun x : ℂ => (x, w)) '' closedBall z r
  have hS : IsCompact S := (isCompact_closedBall z r).image (continuous_id.prodMk continuous_const)
  have hsector : S ⊆ strictQuarterSector ×ˢ strictQuarterSector := by
    rintro p ⟨x, hx, rfl⟩
    refine ⟨hball ?_, hw⟩
    apply mem_ball.mpr
    have hx' := mem_closedBall.mp hx
    dsimp [r] at hx'
    linarith
  obtain ⟨delta, hd, hfloor⟩ := compact_coefficient_floor hS hsector
  let M : ℝ := ‖z‖ + ‖w‖ + epsilon + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hwM : ‖w‖ ≤ M := by dsimp [M]; linarith [norm_nonneg z]
  have hxM : ∀ x ∈ ball z r, ‖x‖ ≤ M := by
    intro x hx
    have hdistance : ‖x - z‖ < r := by simpa only [dist_eq_norm] using mem_ball.mp hx
    have hnorm : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - z) z
    dsimp [M, r] at *
    linarith [norm_nonneg w]
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable
      (fun p : ℝ × ℝ => complexMacdonaldJoint nu x w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
    apply Eventually.of_forall
    intro x
    have hm : Measurable (fun p : ℝ × ℝ => complexMacdonaldJoint nu x w p.1 p.2) := by
      unfold complexMacdonaldJoint complexMacdonaldExponent
      fun_prop
    exact hm.aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (fun p : ℝ × ℝ => jointZDerivative nu z w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
    have hm : Measurable (fun p : ℝ × ℝ => jointZDerivative nu z w p.1 p.2) := by
      unfold jointZDerivative exponentZDerivative complexMacdonaldJoint complexMacdonaldExponent
      fun_prop
    exact hm.aestronglyMeasurable
  have hbound : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, ∀ x ∈ ball z r,
      ‖jointZDerivative nu x w p.1 p.2‖ ≤
        (M * (2 / delta)) * positiveMacdonaldMajorant nu (delta / 2) p.1 p.2 := by
    filter_upwards [positive_snd_ae] with p hp
    intro x hx
    rcases hfloor (x, w) ⟨x, mem_closedBall.mpr (mem_ball.mp hx).le, rfl⟩ with ⟨hx2, hw2, hxw⟩
    exact jointZDerivative_norm_le nu hd hM hx2 hw2 hxw (hxM x hx) hwM hp p.1
  have hdiff : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, ∀ x ∈ ball z r,
      HasDerivAt (fun y : ℂ => complexMacdonaldJoint nu y w p.1 p.2)
        (jointZDerivative nu x w p.1 p.2) x :=
    Eventually.of_forall fun p x _ => complexMacdonaldJoint_hasDerivAt nu x w p.1 p.2
  have hdifferentiation := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := positiveMeasure.prod positiveMeasure)
    (F := fun x p => complexMacdonaldJoint nu x w p.1 p.2)
    (F' := fun x p => jointZDerivative nu x w p.1 p.2)
    (bound := fun p => (M * (2 / delta)) * positiveMacdonaldMajorant nu (delta / 2) p.1 p.2)
    (ball_mem_nhds z hr) hFmeas (complexMacdonaldJoint_integrable nu hz hw) hF'meas hbound
    ((positiveMacdonaldMajorant_integrable nu (half_pos hd)).const_mul _) hdiff).2
  exact hdifferentiation.const_mul (1 / 2 : ℂ)

theorem complexMacdonaldJoint_symm (nu z w : ℂ) (v t : ℝ) :
    complexMacdonaldJoint nu z w v t = complexMacdonaldJoint nu w z v t := by
  have he : complexMacdonaldExponent z w v t = complexMacdonaldExponent w z v t := by
    unfold complexMacdonaldExponent
    ring
  unfold complexMacdonaldJoint
  rw [he]

theorem complexMacdonaldValue_symm (nu z w : ℂ) :
    complexMacdonaldValue nu z w = complexMacdonaldValue nu w z := by
  unfold complexMacdonaldValue
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun p => complexMacdonaldJoint_symm nu z w p.1 p.2

theorem complexMacdonaldValue_analyticOnNhd_left (nu : ℂ) {w : ℂ}
    (hw : w ∈ strictQuarterSector) :
    AnalyticOnNhd ℂ (fun z => complexMacdonaldValue nu z w) strictQuarterSector := by
  apply DifferentiableOn.analyticOnNhd _ strictQuarterSector_isOpen
  intro z hz
  exact (complexMacdonaldValue_hasDerivAt_left nu hz hw).differentiableAt.differentiableWithinAt

theorem complexMacdonaldValue_analyticOnNhd_right (nu : ℂ) {z : ℂ}
    (hz : z ∈ strictQuarterSector) :
    AnalyticOnNhd ℂ (fun w => complexMacdonaldValue nu z w) strictQuarterSector := by
  have he : (fun w => complexMacdonaldValue nu z w) =
      (fun w => complexMacdonaldValue nu w z) := funext (fun w => complexMacdonaldValue_symm nu z w)
  rw [he]
  exact complexMacdonaldValue_analyticOnNhd_left nu hz

end
end ImbalancedChen.Part3.ActualComplexMacdonaldQuarterHolomorphic20261026b
