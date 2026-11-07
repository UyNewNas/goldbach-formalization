import ImbalancedChen.Part3ActualJPoissonQDerivatives
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual J and its native first q-jet are jointly continuous for real order
nu in [-r,r] and q>0, r<1/2. One actual endpoint-integrable Poisson weight
of order -r dominates every finite q moment. No order-holomorphy theorem
restricted to Re(nu)>-1/4 is invoked for negative complementary orders.
-/

namespace ImbalancedChen.Part3.ActualJCompactRealOrderContinuity20261026b

noncomputable section
open Complex Set Filter MeasureTheory
open scoped Topology
open ActualGeneralJBesselSourceOnly GeneralJSymmetricPoissonIntegralSourceOnly
open JBesselPoissonEvenMoments20261025a ActualJPoissonQDerivatives20261025a

def realOrderBand (r : ℝ) : Set (ℝ × ℝ) := Icc (-r) r ×ˢ (univ : Set ℝ)
def positiveRealOrderBand (r : ℝ) : Set (ℝ × ℝ) := Icc (-r) r ×ˢ Ioi (0 : ℝ)

private theorem symmetricWeight_eq (nu : ℂ) (u : ℝ) :
    jSymmetricPoissonWeight nu u = poissonWeight nu u := by
  simp only [jSymmetricPoissonWeight, poissonWeight, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow]

theorem realPoissonWeight_norm_antitone {nu0 nu : ℝ} (hn : nu0 ≤ nu)
    {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ‖jSymmetricPoissonWeight (nu : ℂ) u‖ ≤ ‖jSymmetricPoissonWeight (nu0 : ℂ) u‖ := by
  have hx : 0 < 1 - u ^ 2 := by
    have h := abs_lt.mpr hu
    nlinarith [sq_abs u, abs_nonneg u]
  simp only [symmetricWeight_eq, poissonWeight]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.sub_re, Complex.ofReal_re]
  norm_num
  exact Real.rpow_le_rpow_of_exponent_ge hx (by nlinarith [sq_nonneg u]) (by linarith)

theorem jPoissonMoment_joint_continuousOn (k : ℕ) {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun p : ℝ × ℝ => jPoissonMoment k (p.1 : ℂ) p.2) (realOrderBand r) := by
  have hminus : -(1 / 2 : ℝ) < ((-r : ℝ) : ℂ).re := by simp only [Complex.ofReal_re]; linarith
  have hWeight : IntegrableOn (fun u => ‖jSymmetricPoissonWeight ((-r : ℝ) : ℂ) u‖)
      (Ioo (-1 : ℝ) 1) := by
    simpa only [symmetricWeight_eq] using (poissonWeight_integrable hminus).norm
  intro p hp
  apply tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖jSymmetricPoissonWeight ((-r : ℝ) : ℂ) u‖)
  · exact Eventually.of_forall (fun z => (by
      unfold jPoissonMomentIntegrand jSymmetricPoissonIntegrand jSymmetricPoissonWeight
      fun_prop : Measurable (jPoissonMomentIntegrand k (z.1 : ℂ) z.2)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (jPoissonMomentIntegrand_norm_le k (z.1 : ℂ) z.2 hu).trans
      (realPoissonWeight_norm_antitone hz.1.1 hu)
  · exact hWeight
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hx : 0 < 1 - u ^ 2 := by
      have h := abs_lt.mpr hu
      nlinarith [sq_abs u, abs_nonneg u]
    have hb : 1 - (u : ℂ) ^ 2 ≠ 0 := by
      rw [show (1 : ℂ) - (u : ℂ) ^ 2 = ((1 - u ^ 2 : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_ne_zero.mpr hx.ne'
    have he : Continuous (fun z : ℝ × ℝ => (z.1 : ℂ) - 1 / 2) := by fun_prop
    have hpow := he.const_cpow (Or.inl hb)
    have hc : Continuous (fun z : ℝ × ℝ => jPoissonMomentIntegrand k (z.1 : ℂ) z.2 u) := by
      unfold jPoissonMomentIntegrand jSymmetricPoissonIntegrand jSymmetricPoissonWeight
      exact continuous_const.mul ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
        Complex.exp (I * (z.2 : ℂ) * (u : ℂ)))).mul hpow)
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

private theorem gamma_continuousAt_of_re_pos {z : ℂ} (hz : 0 < z.re) : ContinuousAt Gamma z := by
  apply Complex.continuousAt_Gamma
  intro n hn
  have he := congrArg Complex.re hn
  simp only [Complex.neg_re, Complex.natCast_re] at he
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem jPoissonPrefactor_joint_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun p : ℝ × ℝ => jPoissonPrefactor (p.1 : ℂ) p.2) (positiveRealOrderBand r) := by
  intro p hp
  have hnu : 0 < ((p.1 : ℂ) + 1 / 2).re := by
    have hlow := hp.1.1
    simp only [Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  have hG := (gamma_continuousAt_of_re_pos hnu).comp
    (by fun_prop : ContinuousAt (fun z : ℝ × ℝ => (z.1 : ℂ) + 1 / 2) p)
  have hden : (Real.sqrt Real.pi : ℂ) * Gamma ((p.1 : ℂ) + 1 / 2) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 Real.pi_pos).ne') (Gamma_ne_zero_of_re_pos hnu)
  have hq : 0 < p.2 := hp.2
  have hbase : (((p.2 / 2 : ℝ) : ℂ)) ∈ Complex.slitPlane :=
    Or.inl (by simpa using (show 0 < p.2 / 2 by positivity))
  have hpow := (by fun_prop : ContinuousAt (fun z : ℝ × ℝ => ((z.2 / 2 : ℝ) : ℂ)) p).cpow
    (by fun_prop : ContinuousAt (fun z : ℝ × ℝ => (z.1 : ℂ)) p) hbase
  exact (hpow.div (continuousAt_const.mul hG) hden).continuousWithinAt

theorem generalJ_joint_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun p : ℝ × ℝ => generalJ (p.1 : ℂ) p.2) (positiveRealOrderBand r) := by
  have hM := (jPoissonMoment_joint_continuousOn 0 hr).mono
    (show positiveRealOrderBand r ⊆ realOrderBand r from fun _ hp => ⟨hp.1, mem_univ _⟩)
  apply ((jPoissonPrefactor_joint_continuousOn hr).mul hM).congr
  intro p hp
  have hnu : -(1 / 2 : ℝ) < (p.1 : ℂ).re := by
    simp only [Complex.ofReal_re]
    linarith [hp.1.1]
  rw [jPoissonMoment_zero]
  exact generalJ_eq_symmetric_poisson_integral hnu hp.2

theorem generalJFirst_joint_continuousOn {r : ℝ} (hr : r < 1 / 2) :
    ContinuousOn (fun p : ℝ × ℝ => generalJFirst (p.1 : ℂ) p.2) (positiveRealOrderBand r) := by
  have hJ := generalJ_joint_continuousOn hr
  have hP := jPoissonPrefactor_joint_continuousOn hr
  have hM := (jPoissonMoment_joint_continuousOn 1 hr).mono
    (show positiveRealOrderBand r ⊆ realOrderBand r from fun _ hp => ⟨hp.1, mem_univ _⟩)
  have hQ : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) / (p.2 : ℂ)) (positiveRealOrderBand r) := by
    apply (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ)) (positiveRealOrderBand r)).div
      (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => (p.2 : ℂ)) (positiveRealOrderBand r))
    intro p hp
    exact Complex.ofReal_ne_zero.mpr hp.2.ne'
  apply ((hQ.mul hJ).add (hP.mul hM)).congr
  intro p hp
  have hn : -(1 / 2 : ℝ) < (p.1 : ℂ).re := by simp only [Complex.ofReal_re]; linarith [hp.1.1]
  have hn' : -1 < (p.1 : ℂ).re := by linarith
  exact (generalJ_hasDerivAt hn' hp.2).unique (generalJ_poisson_hasDerivAt hn hp.2)

end
end ImbalancedChen.Part3.ActualJCompactRealOrderContinuity20261026b
