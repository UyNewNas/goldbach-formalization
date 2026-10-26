import ImbalancedChen.Part3ActualComplexArgumentKSchlaefli
import ImbalancedChen.Part3ActualKMacdonaldPositive
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual joint Schwinger/Macdonald absolute convergence on the strict
quarter-sector |Im(z)|<Re(z), |Im(w)|<Re(w). Positivity of Re(z^2),
Re(w^2), and Re(z*w) is derived from those sector inequalities. Every
compact parameter set admits one positive coefficient floor and one
actual integrable positive-real Macdonald majorant. No complex product
formula or parameter-holomorphy hypothesis is assumed. The printed
large DLMF sectors are still OPEN.
-/

namespace ImbalancedChen.Part3.ActualComplexMacdonaldQuarterL120261026b

noncomputable section
open Set MeasureTheory Filter
open ActualComplexArgumentKLaplace20261026b ActualComplexArgumentKSchlaefli20261026b
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualKUnequalHyperbolicDistance20261026b
open ActualKZeroSchwingerFiber20261026b ActualKMacdonaldPositive20261026b

def strictQuarterSector : Set ℂ := {z | |z.im| < z.re}

theorem strictQuarterSector_re_pos {z : ℂ} (hz : z ∈ strictQuarterSector) : 0 < z.re :=
  (abs_nonneg z.im).trans_lt hz

theorem strictQuarterSector_split {z : ℂ} (hz : z ∈ strictQuarterSector) :
    0 < z.re + z.im ∧ 0 < z.re - z.im := by
  have h := abs_lt.mp hz
  constructor <;> linarith

theorem strictQuarterSector_square_re_pos {z : ℂ} (hz : z ∈ strictQuarterSector) :
    0 < (z ^ 2).re := by
  rcases strictQuarterSector_split hz with ⟨hp, hm⟩
  have hprod := mul_pos hp hm
  simp only [pow_two, Complex.mul_re] at hprod ⊢
  nlinarith [hprod]

theorem strictQuarterSector_mul_re_pos {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) : 0 < (z * w).re := by
  rcases strictQuarterSector_split hz with ⟨hzp, hzm⟩
  rcases strictQuarterSector_split hw with ⟨hwp, hwm⟩
  have hp := mul_pos hzp hwm
  have hm := mul_pos hzm hwp
  rw [Complex.mul_re]
  nlinarith [hp, hm]

theorem strictQuarterSector_isOpen : IsOpen strictQuarterSector :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) Complex.continuous_re

def coefficientFloor (p : ℂ × ℂ) : ℝ :=
  min (p.1 ^ 2).re (min (p.2 ^ 2).re (p.1 * p.2).re)

theorem coefficientFloor_continuous : Continuous coefficientFloor := by
  unfold coefficientFloor
  fun_prop

theorem coefficientFloor_pos {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    0 < coefficientFloor (z, w) :=
  lt_min (strictQuarterSector_square_re_pos hz)
    (lt_min (strictQuarterSector_square_re_pos hw) (strictQuarterSector_mul_re_pos hz hw))

theorem compact_coefficient_floor {S : Set (ℂ × ℂ)} (hS : IsCompact S)
    (hsector : S ⊆ strictQuarterSector ×ˢ strictQuarterSector) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ S,
      delta ≤ (p.1 ^ 2).re ∧ delta ≤ (p.2 ^ 2).re ∧ delta ≤ (p.1 * p.2).re := by
  obtain ⟨delta, hd, hfloor⟩ := hS.exists_forall_le' coefficientFloor_continuous.continuousOn
    (fun p hp => coefficientFloor_pos (hsector hp).1 (hsector hp).2)
  refine ⟨delta, hd, ?_⟩
  intro p hp
  have hf := hfloor p hp
  exact ⟨hf.trans (min_le_left _ _),
    hf.trans ((min_le_right _ _).trans (min_le_left _ _)),
    hf.trans ((min_le_right _ _).trans (min_le_right _ _))⟩

/-- The inverse t and all other scalar integration coordinates are real. -/
def complexMacdonaldExponent (z w : ℂ) (v t : ℝ) : ℂ :=
  ((-t / 2 : ℝ) : ℂ) - (z ^ 2 + w ^ 2) * ((1 / (2 * t) : ℝ) : ℂ) -
    (z * w) * ((Real.cosh v / t : ℝ) : ℂ)

def complexMacdonaldJoint (nu z w : ℂ) (v t : ℝ) : ℂ :=
  ((t⁻¹ : ℝ) : ℂ) * Complex.exp (complexMacdonaldExponent z w v t) *
    Complex.cosh (nu * (v : ℂ))

def positiveMacdonaldMajorant (nu : ℂ) (delta v t : ℝ) : ℝ :=
  t⁻¹ * Real.exp (-t / 2 - delta * ((1 + Real.cosh v) / t)) *
    ‖Complex.cosh (nu * (v : ℂ))‖

theorem positive_snd_ae : ∀ᵐ p : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure, 0 < p.2 := by
  apply (ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).mpr
  exact Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Ioi

/-- The real majorant is the norm of an existing actual positive-real
Macdonald joint density at equal arguments sqrt(delta). -/
theorem positiveMacdonaldMajorant_eq_norm (nu : ℂ) {delta t : ℝ}
    (hd : 0 < delta) (ht : 0 < t) (v : ℝ) :
    positiveMacdonaldMajorant nu delta v t =
      ‖macdonaldJoint nu (Real.sqrt delta) (Real.sqrt delta) v t‖ := by
  have hr := Real.sqrt_pos.mpr hd
  have hs := Real.sq_sqrt hd.le
  have hD : hyperbolicDistance (Real.sqrt delta) (Real.sqrt delta) v ^ 2 =
      2 * delta * (1 + Real.cosh v) := by
    rw [hyperbolicDistance_sq hr hr v]
    calc
      _ = delta + delta + 2 * (Real.sqrt delta * Real.sqrt delta) * Real.cosh v := by
        rw [hs]
        ring
      _ = _ := by rw [Real.mul_self_sqrt hd.le]; ring
  have he : -t / 2 - (2 * delta * (1 + Real.cosh v)) / (2 * t) =
      -t / 2 - delta * ((1 + Real.cosh v) / t) := by
    field_simp [ht.ne'] <;> ring
  rw [macdonaldJoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (zeroSchwingerDensity_pos _ ht)]
  unfold positiveMacdonaldMajorant zeroSchwingerDensity
  rw [hD, he]

theorem positiveMacdonaldMajorant_integrable (nu : ℂ) {delta : ℝ} (hd : 0 < delta) :
    Integrable (fun p : ℝ × ℝ => positiveMacdonaldMajorant nu delta p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hr := Real.sqrt_pos.mpr hd
  apply (macdonaldJoint_integrable nu hr hr).norm.congr
  filter_upwards [positive_snd_ae] with p hp
  exact (positiveMacdonaldMajorant_eq_norm nu hd hp p.1).symm

theorem complexMacdonaldJoint_norm (nu z w : ℂ) {t : ℝ} (ht : 0 < t) (v : ℝ) :
    ‖complexMacdonaldJoint nu z w v t‖ = t⁻¹ *
      Real.exp (-t / 2 - ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) -
        (z * w).re * (Real.cosh v / t)) * ‖Complex.cosh (nu * (v : ℂ))‖ := by
  simp only [complexMacdonaldJoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ht), Complex.norm_exp, complexMacdonaldExponent,
    Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]

/-- Actual positive-real joint domination, with the coefficient floor
explicitly retained rather than replaced by a product-formula assumption. -/
theorem complexMacdonaldJoint_norm_le (nu : ℂ) {z w : ℂ} {delta t : ℝ}
    (hd : 0 < delta) (hz : delta ≤ (z ^ 2).re) (hw : delta ≤ (w ^ 2).re)
    (hzw : delta ≤ (z * w).re) (ht : 0 < t) (v : ℝ) :
    ‖complexMacdonaldJoint nu z w v t‖ ≤ positiveMacdonaldMajorant nu delta v t := by
  have hsum := mul_le_mul_of_nonneg_right (add_le_add hz hw)
    (by positivity : 0 ≤ 1 / (2 * t))
  have hprod := mul_le_mul_of_nonneg_right hzw
    (div_nonneg (Real.cosh_pos v).le ht.le)
  have heq : (delta + delta) * (1 / (2 * t)) + delta * (Real.cosh v / t) =
      delta * ((1 + Real.cosh v) / t) := by field_simp [ht.ne'] <;> ring
  have he : -t / 2 - ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) -
      (z * w).re * (Real.cosh v / t) ≤ -t / 2 - delta * ((1 + Real.cosh v) / t) := by
    linarith
  rw [complexMacdonaldJoint_norm nu z w ht v]
  unfold positiveMacdonaldMajorant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (inv_pos.mpr ht).le) (norm_nonneg _)

theorem complexMacdonaldJoint_integrable_of_floor (nu : ℂ) {z w : ℂ} {delta : ℝ}
    (hd : 0 < delta) (hz : delta ≤ (z ^ 2).re) (hw : delta ≤ (w ^ 2).re)
    (hzw : delta ≤ (z * w).re) :
    Integrable (fun p : ℝ × ℝ => complexMacdonaldJoint nu z w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hm : Measurable (fun p : ℝ × ℝ => complexMacdonaldJoint nu z w p.1 p.2) := by
    unfold complexMacdonaldJoint complexMacdonaldExponent
    fun_prop
  apply (positiveMacdonaldMajorant_integrable nu hd).mono' hm.aestronglyMeasurable
  filter_upwards [positive_snd_ae] with p hp
  exact complexMacdonaldJoint_norm_le nu hd hz hw hzw hp p.1

theorem complexMacdonaldJoint_integrable (nu : ℂ) {z w : ℂ}
    (hz : z ∈ strictQuarterSector) (hw : w ∈ strictQuarterSector) :
    Integrable (fun p : ℝ × ℝ => complexMacdonaldJoint nu z w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hd := coefficientFloor_pos hz hw
  apply complexMacdonaldJoint_integrable_of_floor nu hd
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- Every compact two-argument quarter-sector family has one actual
integrable majorant. This is the compact domination needed for subsequent
parameter analysis; no holomorphy of the integral is assumed. -/
theorem compact_complexMacdonaldJoint_majorant (nu : ℂ) {S : Set (ℂ × ℂ)}
    (hS : IsCompact S) (hsector : S ⊆ strictQuarterSector ×ˢ strictQuarterSector) :
    ∃ delta : ℝ, 0 < delta ∧
      Integrable (fun p : ℝ × ℝ => positiveMacdonaldMajorant nu delta p.1 p.2)
        (positiveMeasure.prod positiveMeasure) ∧
      ∀ p ∈ S, ∀ᵐ x : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ‖complexMacdonaldJoint nu p.1 p.2 x.1 x.2‖ ≤
          positiveMacdonaldMajorant nu delta x.1 x.2 := by
  obtain ⟨delta, hd, hfloor⟩ := compact_coefficient_floor hS hsector
  refine ⟨delta, hd, positiveMacdonaldMajorant_integrable nu hd, ?_⟩
  intro p hp
  rcases hfloor p hp with ⟨hz, hw, hzw⟩
  filter_upwards [positive_snd_ae] with x hx
  exact complexMacdonaldJoint_norm_le nu hd hz hw hzw hx x.1

end
end ImbalancedChen.Part3.ActualComplexMacdonaldQuarterL120261026b
