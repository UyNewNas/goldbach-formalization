import ImbalancedChen.Part3ActualRealOrderJLargeQ
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Fresh real-order J positive-q germ from its literal principal power and
compact entire core: |J_nu(q)|<=C*q^nu on 0<q<=1. Combining this with the
actual real-order energy tail gives full actual Mellin L1 when
Re(s)+nu>0 and Re(s)<1/2, for |nu|<=1/2. In particular the nonempty strip
for nu=-7/16 is 7/16<Re(s)<1/2. No 7/32 or full Kuznetsov claim is made.
-/

namespace ImbalancedChen.Part3.ActualRealOrderJMellinL120261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly GeneralComplexISeriesSourceOnly
open ActualRealOrderJRadialJet20261026b ActualRealOrderJLargeQ20261026b

def realOrderJMellinIntegrand (s : ℂ) (nu q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * generalJ (nu : ℂ) q
def realOrderJMellinIntegral (s : ℂ) (nu : ℝ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), realOrderJMellinIntegrand s nu q

theorem exists_generalJ_real_small_q_bound {nu : ℝ} (hnu : |nu| ≤ 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ q ∈ Ioc (0 : ℝ) 1, ‖generalJ (nu : ℂ) q‖ ≤ C * q ^ nu := by
  have hc : Continuous (fun q : ℝ => generalICore (nu : ℂ) (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))) :=
    (continuous_generalICore (real_order_lower hnu)).comp (by fun_prop)
  obtain ⟨A, hA⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hc.continuousOn
  let C : ℝ := (|A| + 1) / (2 : ℝ) ^ nu
  have h2 : 0 < (2 : ℝ) ^ nu := Real.rpow_pos_of_pos (by norm_num) nu
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro q hq
  have hb : ‖generalICore (nu : ℂ) (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))‖ ≤ |A| + 1 := by
    have h := hA q ⟨hq.1.le, hq.2⟩
    have hh := le_abs_self A
    linarith
  rw [generalJ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : (0 : ℝ) < q / 2)]
  simp only [Complex.ofReal_re]
  calc
    (q / 2) ^ nu * ‖generalICore (nu : ℂ) (-(((q / 2 : ℝ) : ℂ) ^ (2 : ℕ)))‖ ≤
        (q / 2) ^ nu * (|A| + 1) :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by positivity) _)
    _ = C * q ^ nu := by rw [Real.div_rpow hq.1.le (by norm_num : (0 : ℝ) ≤ 2)]; dsimp [C]; ring

theorem realOrderJMellinIntegrand_continuousOn {nu : ℝ} (hnu : |nu| ≤ 1 / 2) (s : ℂ) :
    ContinuousOn (realOrderJMellinIntegrand s nu) (Ioi 0) := by
  intro q hq
  exact ((Complex.continuousAt_ofReal_cpow_const q (s - 1) (Or.inr hq.ne')).mul
    (generalJ_differentiableAt (real_order_lower hnu) hq).continuousAt).continuousWithinAt

theorem integrableOn_realOrderJMellin_near_zero {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {s : ℂ} (hsnu : 0 < s.re + nu) :
    IntegrableOn (realOrderJMellinIntegrand s nu) (Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  obtain ⟨C, hC, hb⟩ := exists_generalJ_real_small_q_bound hnu
  have hi : IntegrableOn (fun q : ℝ => C * q ^ (s.re + nu - 1)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by linarith : -1 < s.re + nu - 1)).const_mul C
  have hc := (realOrderJMellinIntegrand_continuousOn hnu s).mono
    (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hq => hq.1)
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  rw [realOrderJMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq.1]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    q ^ (s.re - 1) * ‖generalJ (nu : ℂ) q‖ ≤ q ^ (s.re - 1) * (C * q ^ nu) :=
      mul_le_mul_of_nonneg_left (hb q ⟨hq.1, hq.2.le⟩) (Real.rpow_nonneg hq.1.le _)
    _ = C * (q ^ (s.re - 1) * q ^ nu) := by ring
    _ = C * q ^ (s.re + nu - 1) := by
      rw [← Real.rpow_add hq.1]
      congr 1
      congr 1
      ring

/-- Genuine full complementary real-order Mellin L1. -/
theorem integrableOn_realOrderJMellin {nu : ℝ} (hnu : |nu| ≤ 1 / 2)
    {s : ℂ} (hsnu : 0 < s.re + nu) (hsHalf : s.re < 1 / 2) :
    IntegrableOn (realOrderJMellinIntegrand s nu) (Ioi 0) := by
  have hn := integrableOn_realOrderJMellin_near_zero hnu hsnu
  have ht : IntegrableOn (realOrderJMellinIntegrand s nu) (Ioi 1) :=
    integrableOn_generalJ_real_Mellin_tail hnu hsHalf
  have h := hn.union ht
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h

end
end ImbalancedChen.Part3.ActualRealOrderJMellinL120261026b
