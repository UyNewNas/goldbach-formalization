import ImbalancedChen.Part3ActualJImaginarySmallQBound
import ImbalancedChen.Part3ActualJLargeQEnergyBound
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Genuine full L1 for the literal fixed-order J_(2it) Mellin integrand in the
nonempty strip 0<Re(s)<1/2. The near-zero bounded actual core supplier and
the independently proved actual ODE-energy tail supplier are combined.
No result about the logarithmically singular removable critical quotient
is imported, repaired, or treated as available.
Actual Mellin evaluation as a Gamma quotient remains OPEN.
-/

namespace ImbalancedChen.Part3.ActualJFixedOrderMellinL120261026b

noncomputable section
open Complex Set MeasureTheory
open ActualGeneralJBesselSourceOnly ActualJImaginarySmallQBound20261026b
open ActualJLargeQEnergyBound20261026b

def actualJMellinIntegrand (s : ℂ) (t q : ℝ) : ℂ :=
  (q : ℂ) ^ (s - 1) * generalJ (2 * I * (t : ℂ)) q

def actualJMellinIntegral (s : ℂ) (t : ℝ) : ℂ :=
  ∫ q in Ioi (0 : ℝ), actualJMellinIntegrand s t q

theorem actualJMellinIntegrand_continuousOn (s : ℂ) (t : ℝ) :
    ContinuousOn (actualJMellinIntegrand s t) (Ioi 0) := by
  intro q hq
  have hnu : -1 < (2 * I * (t : ℂ)).re := by simp
  have hp := Complex.continuousAt_ofReal_cpow_const q (s - 1) (Or.inr hq.ne')
  exact (hp.mul (generalJ_differentiableAt hnu hq).continuousAt).continuousWithinAt

theorem integrableOn_actualJMellin_near_zero {s : ℂ} (hs : 0 < s.re) (t : ℝ) :
    IntegrableOn (actualJMellinIntegrand s t) (Ioc 0 1) := by
  rw [integrableOn_Ioc_iff_integrableOn_Ioo]
  obtain ⟨C, hC, hb⟩ := exists_generalJ_imaginary_small_q_bound t
  have hi : IntegrableOn (fun q : ℝ => C * q ^ (s.re - 1)) (Ioo 0 1) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)).2
      (by linarith : -1 < s.re - 1)).const_mul C
  have hc := (actualJMellinIntegrand_continuousOn s t).mono
    (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ hq => hq.1)
  apply hi.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with q hq
  rw [actualJMellinIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hq.1]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    q ^ (s.re - 1) * ‖generalJ (2 * I * (t : ℂ)) q‖ ≤ q ^ (s.re - 1) * C :=
      mul_le_mul_of_nonneg_left (hb q ⟨hq.1, hq.2.le⟩) (Real.rpow_nonneg hq.1.le _)
    _ = C * q ^ (s.re - 1) := mul_comm _ _

/-- Actual full fixed-order Mellin integrability, including t=0 ordinary
J_0. This theorem concerns J itself, not its opposite-order derivative. -/
theorem integrableOn_actualJMellin {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    IntegrableOn (actualJMellinIntegrand s t) (Ioi 0) := by
  have hn := integrableOn_actualJMellin_near_zero hs0 t
  have ht : IntegrableOn (actualJMellinIntegrand s t) (Ioi 1) :=
    integrableOn_generalJ_Mellin_tail hsHalf t
  have h := hn.union ht
  rwa [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] at h

theorem integrableOn_actualJMellin_norm {s : ℂ}
    (hs0 : 0 < s.re) (hsHalf : s.re < 1 / 2) (t : ℝ) :
    IntegrableOn (fun q => ‖actualJMellinIntegrand s t q‖) (Ioi 0) :=
  (integrableOn_actualJMellin hs0 hsHalf t).norm

end
end ImbalancedChen.Part3.ActualJFixedOrderMellinL120261026b
