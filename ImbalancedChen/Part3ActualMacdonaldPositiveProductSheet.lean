import ImbalancedChen.Part3ActualMacdonaldProductDetermination
import ImbalancedChen.Part3ActualComplexMacdonaldCombinedL1
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual inherited product sheet in the positive-product part of the
printed Macdonald domain. Slit arguments and Re(z+w)>0 imply an inherited
phase of absolute value below 3pi/2. If Re(z*w)>0, its cosine is positive,
so that phase is actually in (-pi/2,pi/2). Thus the product half-log is
the genuine principal right-half-plane half-log. Literal order-evenness
also extends the supplied actual K-cover/Laplace binding to negative real
orders in the small strip. No endpoint integral or E18 identity is used.
-/

namespace ImbalancedChen.Part3.ActualMacdonaldPositiveProductSheet20261026b

noncomputable section
open Set MeasureTheory Filter
open ActualComplexArgumentKLaplace20261026b
open ActualLogCoverKModel20261026b ActualMacdonaldProductDetermination20261026b
open ActualComplexMacdonaldQuarterL120261026b

def printedMacdonaldDomain : Set (ℂ × ℂ) :=
  {p | p.1 ∈ Complex.slitPlane ∧ p.2 ∈ Complex.slitPlane ∧
    p.1 + p.2 ∈ strictQuarterSector}

theorem printedMacdonaldDomain_isOpen : IsOpen printedMacdonaldDomain :=
  (Complex.isOpen_slitPlane.preimage continuous_fst).inter
    ((Complex.isOpen_slitPlane.preimage continuous_snd).inter
      (strictQuarterSector_isOpen.preimage (continuous_fst.add continuous_snd)))

theorem slit_abs_arg_lt_pi {z : ℂ} (hz : z ∈ Complex.slitPlane) : |Complex.arg z| < Real.pi := by
  have hu : Complex.arg z < Real.pi :=
    (lt_or_eq_of_le (Complex.arg_le_pi z)).resolve_right (Complex.slitPlane_arg_ne_pi hz)
  exact abs_lt.mpr ⟨Complex.neg_pi_lt_arg z, hu⟩

theorem inherited_phase_lt_three_half_pi {z w : ℂ}
    (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : 0 < (z + w).re) :
    |Complex.arg z + Complex.arg w| < 3 * Real.pi / 2 := by
  have hzpi := slit_abs_arg_lt_pi hz
  have hwpi := slit_abs_arg_lt_pi hw
  have hsome : 0 < z.re ∨ 0 < w.re := by
    by_cases hzr : 0 < z.re
    · exact Or.inl hzr
    · right
      have hzr' : z.re ≤ 0 := le_of_not_gt hzr
      rw [Complex.add_re] at hs
      linarith
  rcases hsome with hzr | hwr
  · have hh := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hzr)
    exact (abs_add (Complex.arg z) (Complex.arg w)).trans_lt (by linarith)
  · have hh := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hwr)
    exact (abs_add (Complex.arg z) (Complex.arg w)).trans_lt (by linarith)

theorem cos_inherited_phase {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    Real.cos (Complex.arg z + Complex.arg w) = (z * w).re / (‖z‖ * ‖w‖) := by
  rw [Real.cos_add, Complex.cos_arg hz, Complex.cos_arg hw, Complex.sin_arg, Complex.sin_arg,
    Complex.mul_re]
  field_simp [(norm_pos_iff.mpr hz).ne', (norm_pos_iff.mpr hw).ne'] <;> ring

theorem positive_cos_three_half_window {theta : ℝ}
    (hwindow : |theta| < 3 * Real.pi / 2) (hcos : 0 < Real.cos theta) :
    |theta| < Real.pi / 2 := by
  by_contra h
  have hl : Real.pi / 2 ≤ |theta| := le_of_not_gt h
  have hu : |theta| ≤ Real.pi + Real.pi / 2 := by linarith
  have hn := Real.cos_nonpos_of_pi_div_two_le_of_le hl hu
  rw [Real.cos_abs] at hn
  linarith

theorem positive_product_inherited_phase {z w : ℂ}
    (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : 0 < (z + w).re) (hp : 0 < (z * w).re) :
    |Complex.arg z + Complex.arg w| < Real.pi / 2 := by
  have hzn := (Complex.mem_slitPlane_iff_arg.mp hz).2
  have hwn := (Complex.mem_slitPlane_iff_arg.mp hw).2
  apply positive_cos_three_half_window (inherited_phase_lt_three_half_pi hz hw hs)
  rw [cos_inherited_phase hzn hwn]
  exact div_pos hp (mul_pos (norm_pos_iff.mpr hzn) (norm_pos_iff.mpr hwn))

theorem positive_product_argument_re_pos {z w : ℂ} (hp : 0 < (z * w).re)
    {t : ℝ} (ht : 0 < t) : 0 < (physicalProductArgument z w t).re := by
  have he : physicalProductArgument z w t = z * w * ((t⁻¹ : ℝ) : ℂ) := by
    simp only [physicalProductArgument, div_eq_mul_inv, Complex.ofReal_inv]
  rw [he]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    using mul_pos hp (inv_pos.mpr ht)

/-- A genuine principal-sheet conclusion, including its actual phase
window, is proved before any Laplace K fiber is used. -/
theorem positive_product_principal_half_log {z w : ℂ}
    (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : 0 < (z + w).re) (hp : 0 < (z * w).re) {t : ℝ} (ht : 0 < t) :
    Complex.log (physicalProductArgument z w t / 2) = productHalfLog z w t := by
  have hphase := abs_lt.mp (positive_product_inherited_phase hz hw hs hp)
  exact principal_half_log_eq_productHalfLog
    (Complex.mem_slitPlane_iff_arg.mp hz).2 (Complex.mem_slitPlane_iff_arg.mp hw).2 ht
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

theorem logCoverKNonintegral_neg_order (nu L : ℂ) :
    logCoverKNonintegral (-nu) L = logCoverKNonintegral nu L := by
  simp only [logCoverKNonintegral, neg_neg, mul_neg, Complex.sin_neg, div_neg]
  ring

theorem logCoverK_neg_order (nu L : ℂ) : logCoverK (-nu) L = logCoverK nu L := by
  by_cases hn : nu = 0
  · subst nu
    simp only [neg_zero]
  · simpa only [logCoverK, if_neg hn, if_neg (neg_ne_zero.mpr hn)] using
      logCoverKNonintegral_neg_order nu L

theorem complexArgumentK_neg_order (nu z : ℂ) : complexArgumentK (-nu) z = complexArgumentK nu z := by
  rw [complexArgumentK_eq_integral, complexArgumentK_eq_integral]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by simp only [neg_mul, Complex.cosh_neg]

/-- Exact actual Laplace binding on the full small order strip. The
negative-real-part case is derived by the literal evenness above. -/
theorem logCoverK_eq_actual_rightHalfPlane_small {nu q : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2) (hq : 0 < q.re) :
    logCoverK nu (Complex.log (q / 2)) = complexArgumentK nu q := by
  by_cases hn : nu = 0
  · exact logCoverK_eq_actual_rightHalfPlane (Or.inl hn) hq
  by_cases hp : 0 < nu.re
  · exact logCoverK_eq_actual_rightHalfPlane (Or.inr (Or.inl ⟨hp, by linarith⟩)) hq
  by_cases he : nu.re = 0
  · have hi : nu.im ≠ 0 := by
      intro hi
      apply hn
      exact Complex.ext he hi
    exact logCoverK_eq_actual_rightHalfPlane (Or.inr (Or.inr ⟨he, hi⟩)) hq
  · have hm : 0 < (-nu).re := by rw [Complex.neg_re]; have := le_of_not_gt hp; linarith
    calc
      _ = logCoverK (-nu) (Complex.log (q / 2)) := (logCoverK_neg_order nu _).symm
      _ = complexArgumentK (-nu) q := logCoverK_eq_actual_rightHalfPlane
        (Or.inr (Or.inl ⟨hm, by rw [Complex.neg_re]; linarith⟩)) hq
      _ = _ := complexArgumentK_neg_order nu q

/-- Actual inherited-sheet/Laplace-fiber equality in the positive-product
region. Both the argument sheet and the small order binding are proved. -/
theorem determinedProductK_eq_actual_positive_product {nu z w : ℂ}
    (hL : -(1 / 2 : ℝ) < nu.re) (hU : nu.re < 1 / 2)
    (hz : z ∈ Complex.slitPlane) (hw : w ∈ Complex.slitPlane)
    (hs : 0 < (z + w).re) (hp : 0 < (z * w).re) {t : ℝ} (ht : 0 < t) :
    determinedProductK nu z w t = complexArgumentK nu (physicalProductArgument z w t) := by
  unfold determinedProductK
  rw [← positive_product_principal_half_log hz hw hs hp ht]
  exact logCoverK_eq_actual_rightHalfPlane_small hL hU (positive_product_argument_re_pos hp ht)

end
end ImbalancedChen.Part3.ActualMacdonaldPositiveProductSheet20261026b
