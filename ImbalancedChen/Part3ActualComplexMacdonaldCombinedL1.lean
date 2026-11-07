import ImbalancedChen.Part3ActualComplexMacdonaldQuarterL1
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

Actual Macdonald joint absolute convergence from COMBINED damping.
The arguments lie in the right half-plane, their product has positive
real part, and their sum lies in the strict quarter-sector. Individual
real parts of z^2 and w^2 may be negative. The exact exponent numerator
is A+2B(cosh(v)-1), where A=Re((z+w)^2)>0 and B=Re(z*w)>0.
Compact floors for A and B give the previously proved actual positive
equal-argument Macdonald majorant. No product identity or sector growth
estimate is assumed. The printed domain with left-half-plane arguments
remains OPEN.
-/

namespace ImbalancedChen.Part3.ActualComplexMacdonaldCombinedL120261026b

noncomputable section
open Set MeasureTheory Filter
open ActualKUnequalPositiveShear20261026b (positiveMeasure)
open ActualComplexArgumentKLaplace20261026b
open ActualComplexMacdonaldQuarterL120261026b

def combinedMacdonaldDomain : Set (ℂ × ℂ) :=
  {p | 0 < p.1.re ∧ 0 < p.2.re ∧ 0 < (p.1 * p.2).re ∧
    p.1 + p.2 ∈ strictQuarterSector}

def combinedMacdonaldSlice (w : ℂ) : Set ℂ :=
  {z | (z, w) ∈ combinedMacdonaldDomain}

theorem combinedMacdonaldDomain_swap {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    (w, z) ∈ combinedMacdonaldDomain := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · simpa only [mul_comm] using h.2.2.1
  · simpa only [add_comm] using h.2.2.2

theorem combinedMacdonaldDomain_isOpen : IsOpen combinedMacdonaldDomain := by
  have hz : Continuous (fun p : ℂ × ℂ => p.1.re) := by fun_prop
  have hw : Continuous (fun p : ℂ × ℂ => p.2.re) := by fun_prop
  have hp : Continuous (fun p : ℂ × ℂ => (p.1 * p.2).re) := by fun_prop
  have hs : Continuous (fun p : ℂ × ℂ => p.1 + p.2) := by fun_prop
  exact (isOpen_lt continuous_const hz).inter
    ((isOpen_lt continuous_const hw).inter
      ((isOpen_lt continuous_const hp).inter (strictQuarterSector_isOpen.preimage hs)))

theorem combinedMacdonaldSlice_isOpen (w : ℂ) : IsOpen (combinedMacdonaldSlice w) :=
  combinedMacdonaldDomain_isOpen.preimage (continuous_id.prodMk continuous_const)

theorem combinedMacdonaldSlice_subset_rightHalfPlane (w : ℂ) :
    combinedMacdonaldSlice w ⊆ rightHalfPlane := fun _ hz => hz.1

theorem combined_product_argument_re_pos {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) {t : ℝ} (ht : 0 < t) :
    z * w / (t : ℂ) ∈ rightHalfPlane := by
  have heq : z * w / (t : ℂ) = z * w * ((t⁻¹ : ℝ) : ℂ) := by
    simp only [div_eq_mul_inv, Complex.ofReal_inv]
  change 0 < (z * w / (t : ℂ)).re
  rw [heq]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using mul_pos h.2.2.1 (inv_pos.mpr ht)

def combinedCoefficientFloor (p : ℂ × ℂ) : ℝ :=
  min ((p.1 + p.2) ^ 2).re (p.1 * p.2).re

theorem combinedCoefficientFloor_continuous : Continuous combinedCoefficientFloor := by
  unfold combinedCoefficientFloor
  fun_prop

theorem combinedCoefficientFloor_pos {p : ℂ × ℂ}
    (hp : p ∈ combinedMacdonaldDomain) : 0 < combinedCoefficientFloor p :=
  lt_min (strictQuarterSector_square_re_pos hp.2.2.2) hp.2.2.1

theorem compact_combined_coefficient_floor {S : Set (ℂ × ℂ)}
    (hS : IsCompact S) (hcombined : S ⊆ combinedMacdonaldDomain) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ p ∈ S,
      delta ≤ ((p.1 + p.2) ^ 2).re ∧ delta ≤ (p.1 * p.2).re := by
  obtain ⟨delta, hd, hfloor⟩ := hS.exists_forall_le'
    combinedCoefficientFloor_continuous.continuousOn
    (fun p hp => combinedCoefficientFloor_pos (hcombined hp))
  refine ⟨delta, hd, ?_⟩
  intro p hp
  exact ⟨(hfloor p hp).trans (min_le_left _ _),
    (hfloor p hp).trans (min_le_right _ _)⟩

theorem combined_square_re (z w : ℂ) :
    ((z + w) ^ 2).re = (z ^ 2).re + (w ^ 2).re + 2 * (z * w).re := by
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.add_im]
  ring

/-- This is the exact combined damping identity; neither individual
square coefficient is required to be positive. -/
theorem combined_damping_eq (z w : ℂ) {t : ℝ} (ht : 0 < t) (v : ℝ) :
    ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) +
        (z * w).re * (Real.cosh v / t) =
      (((z + w) ^ 2).re + 2 * (z * w).re * (Real.cosh v - 1)) * (1 / (2 * t)) := by
  rw [combined_square_re]
  field_simp [ht.ne'] <;> ring

theorem combined_damping_lower_bound {z w : ℂ} {delta t : ℝ}
    (hd : 0 < delta) (hA : delta ≤ ((z + w) ^ 2).re)
    (hB : delta ≤ (z * w).re) (ht : 0 < t) (v : ℝ) :
    (delta / 4) * ((1 + Real.cosh v) / t) ≤
      ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) +
        (z * w).re * (Real.cosh v / t) := by
  have hc := Real.one_le_cosh v
  have hcm : 0 ≤ Real.cosh v - 1 := sub_nonneg.mpr hc
  have hp := mul_le_mul_of_nonneg_right hB hcm
  have hdc := mul_nonneg hd.le hcm
  have hnum : (delta / 2) * (1 + Real.cosh v) ≤
      ((z + w) ^ 2).re + 2 * (z * w).re * (Real.cosh v - 1) := by
    nlinarith [hp, hdc]
  have hdiv := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ 1 / (2 * t))
  have heq : (delta / 2) * (1 + Real.cosh v) * (1 / (2 * t)) =
      (delta / 4) * ((1 + Real.cosh v) / t) := by
    field_simp [ht.ne'] <;> ring
  rw [heq] at hdiv
  rw [combined_damping_eq z w ht v]
  exact hdiv

theorem complexMacdonaldJoint_norm_le_combined (nu : ℂ) {z w : ℂ} {delta t : ℝ}
    (hd : 0 < delta) (hA : delta ≤ ((z + w) ^ 2).re)
    (hB : delta ≤ (z * w).re) (ht : 0 < t) (v : ℝ) :
    ‖complexMacdonaldJoint nu z w v t‖ ≤
      positiveMacdonaldMajorant nu (delta / 4) v t := by
  have he : -t / 2 - ((z ^ 2).re + (w ^ 2).re) * (1 / (2 * t)) -
      (z * w).re * (Real.cosh v / t) ≤
        -t / 2 - (delta / 4) * ((1 + Real.cosh v) / t) := by
    linarith [combined_damping_lower_bound hd hA hB ht v]
  rw [complexMacdonaldJoint_norm nu z w ht v]
  unfold positiveMacdonaldMajorant
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (inv_pos.mpr ht).le) (norm_nonneg _)

theorem complexMacdonaldJoint_integrable_combined_of_floor (nu : ℂ) {z w : ℂ} {delta : ℝ}
    (hd : 0 < delta) (hA : delta ≤ ((z + w) ^ 2).re) (hB : delta ≤ (z * w).re) :
    Integrable (fun p : ℝ × ℝ => complexMacdonaldJoint nu z w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  have hm : Measurable (fun p : ℝ × ℝ => complexMacdonaldJoint nu z w p.1 p.2) := by
    unfold complexMacdonaldJoint complexMacdonaldExponent
    fun_prop
  apply (positiveMacdonaldMajorant_integrable nu (by positivity : 0 < delta / 4)).mono'
    hm.aestronglyMeasurable
  filter_upwards [positive_snd_ae] with p hp
  exact complexMacdonaldJoint_norm_le_combined nu hd hA hB hp p.1

theorem complexMacdonaldJoint_integrable_combined (nu : ℂ) {z w : ℂ}
    (h : (z, w) ∈ combinedMacdonaldDomain) :
    Integrable (fun p : ℝ × ℝ => complexMacdonaldJoint nu z w p.1 p.2)
      (positiveMeasure.prod positiveMeasure) := by
  apply complexMacdonaldJoint_integrable_combined_of_floor nu (combinedCoefficientFloor_pos h)
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- One genuine integrable real majorant works over every compact subset
of the combined domain, even when an individual square has negative
real part. The factor one quarter records the exact damping loss. -/
theorem compact_complexMacdonaldJoint_combined_majorant (nu : ℂ) {S : Set (ℂ × ℂ)}
    (hS : IsCompact S) (hcombined : S ⊆ combinedMacdonaldDomain) :
    ∃ delta : ℝ, 0 < delta ∧
      Integrable (fun p : ℝ × ℝ => positiveMacdonaldMajorant nu (delta / 4) p.1 p.2)
        (positiveMeasure.prod positiveMeasure) ∧
      ∀ p ∈ S, ∀ᵐ x : ℝ × ℝ ∂positiveMeasure.prod positiveMeasure,
        ‖complexMacdonaldJoint nu p.1 p.2 x.1 x.2‖ ≤
          positiveMacdonaldMajorant nu (delta / 4) x.1 x.2 := by
  obtain ⟨delta, hd, hfloor⟩ := compact_combined_coefficient_floor hS hcombined
  refine ⟨delta, hd, positiveMacdonaldMajorant_integrable nu (by positivity), ?_⟩
  intro p hp
  rcases hfloor p hp with ⟨hA, hB⟩
  filter_upwards [positive_snd_ae] with x hx
  exact complexMacdonaldJoint_norm_le_combined nu hd hA hB hx x.1

end
end ImbalancedChen.Part3.ActualComplexMacdonaldCombinedL120261026b
