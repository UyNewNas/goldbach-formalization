import ImbalancedChen.Part3ImaginaryOrderKQSmooth
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
No compiler, checker, audit, numerical replay or actual-source edit is used.

An actual convergent Taylor expansion of the existing K integral is proved
at every q0>0, for every |h|<q0/2. Coefficients are actual M_n(t,q0)/n!.
The existing actual pointwise factorial envelope gives a geometric series
times one integrable exponential, justifying the series/integral exchange.
No analytic hypothesis or power-series equality is assumed.

Real-parameter analyticity is then supplied for K, K/q and their complex
coercions/actual extension. This is AnalyticOnNhd over ℝ, not a claim of a
complex-q holomorphic extension. In this pin analytic means ContDiff ω=⊤.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKQAnalyticSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKQMomentsSourceOnly
open ImaginaryOrderKQSmoothSourceOnly
open P3ActualLiteralPacketIntegralSourceOnly

def taylorCoefficient (n : ℕ) (t q0 : ℝ) : ℝ := qMoment n t q0/(n.factorial : ℝ)

def actualTaylorSeries (t q0 : ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => taylorCoefficient n t q0)

def taylorTermIntegrand (n : ℕ) (t q0 h u : ℝ) : ℝ :=
  (h^n/(n.factorial : ℝ))*qMomentIntegrand n t q0 u

def seriesRatio (q0 h : ℝ) : ℝ := (2/q0)*|h|

lemma seriesRatio_nonneg {q0 : ℝ} (hq0 : 0 < q0) (h : ℝ) :
    0 ≤ seriesRatio q0 h := by unfold seriesRatio; positivity

lemma seriesRatio_lt_one {q0 h : ℝ} (hq0 : 0 < q0) (hh : |h| < q0/2) :
    seriesRatio q0 h < 1 := by
  have he : seriesRatio q0 h = (2*|h|)/q0 := by unfold seriesRatio; ring
  rw [he]
  exact (div_lt_one hq0).mpr (by linarith)

/-- Actual term domination. Factorial cancellation is justified by the
positive natural factorial, including n=0. -/
lemma taylorTermIntegrand_norm_le (n : ℕ) (t : ℝ) {q0 : ℝ}
    (hq0 : 0 < q0) (h u : ℝ) :
    ‖taylorTermIntegrand n t q0 h u‖ ≤
      (seriesRatio q0 h)^n*Real.exp (-(q0/4)*u) := by
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hc : 0 ≤ |h|^n/(n.factorial : ℝ) := by positivity
  calc
    ‖taylorTermIntegrand n t q0 h u‖ =
        (|h|^n/(n.factorial : ℝ))*‖qMomentIntegrand n t q0 u‖ := by
      simp only [taylorTermIntegrand, norm_mul, Real.norm_eq_abs, abs_div,
        abs_pow, abs_of_pos hfac]
    _ ≤ (|h|^n/(n.factorial : ℝ))*
        (momentCoefficient n q0*Real.exp (-(q0/4)*u)) :=
      mul_le_mul_of_nonneg_left (qMomentIntegrand_norm_le n hq0 le_rfl t u) hc
    _ = (seriesRatio q0 h)^n*Real.exp (-(q0/4)*u) := by
      unfold seriesRatio momentCoefficient
      simp only [mul_pow]
      field_simp [hfac.ne', hq0.ne'] <;> ring

lemma taylorTermIntegrand_pointwise_hasSum (t q0 h u : ℝ) :
    HasSum (fun n => taylorTermIntegrand n t q0 h u) (kIntegrand t (q0+h) u) := by
  have hexp : HasSum (fun n : ℕ => (-h*Real.cosh u)^n/(n.factorial : ℝ))
      (Real.exp (-h*Real.cosh u)) := by
    simpa only [← Real.exp_eq_exp_ℝ] using
      NormedSpace.expSeries_div_hasSum_exp (-h*Real.cosh u)
  have hs := hexp.mul_right (Real.exp (-q0*Real.cosh u)*Real.cos (2*t*u))
  convert hs using 1
  · funext n
    unfold taylorTermIntegrand qMomentIntegrand
    have hp : -h*Real.cosh u = h*(-Real.cosh u) := by ring
    rw [hp, mul_pow]
    ring
  · unfold kIntegrand
    have he : -h*Real.cosh u + (-q0*Real.cosh u) = -(q0+h)*Real.cosh u := by ring
    rw [← mul_assoc, ← Real.exp_add, he]

/-- The actual Taylor series converges to the actual integral in the stated
concrete positive-radius neighborhood; the sum is not a new definition of K. -/
theorem imaginaryOrderK_taylor_hasSum (t : ℝ) {q0 h : ℝ}
    (hq0 : 0 < q0) (hh : |h| < q0/2) :
    HasSum (fun n : ℕ => h^n*taylorCoefficient n t q0) (imaginaryOrderK t (q0+h)) := by
  have hr0 := seriesRatio_nonneg hq0 h
  have hr : ‖seriesRatio q0 h‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact seriesRatio_lt_one hq0 hh
  have hgeom : Summable (fun n : ℕ => (seriesRatio q0 h)^n) :=
    summable_geometric_of_norm_lt_one hr
  have hexpInt : IntegrableOn (fun u : ℝ => Real.exp (-(q0/4)*u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith : -(q0/4) < 0) 0
  have hboundInt : IntegrableOn
      (fun u : ℝ => ∑' n : ℕ, (seriesRatio q0 h)^n*Real.exp (-(q0/4)*u)) (Ioi 0) := by
    simpa only [tsum_mul_right] using
      hexpInt.const_mul (∑' n : ℕ, (seriesRatio q0 h)^n)
  have hmeas (n : ℕ) : AEStronglyMeasurable (taylorTermIntegrand n t q0 h)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : Continuous (taylorTermIntegrand n t q0 h) := by
      unfold taylorTermIntegrand qMomentIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      ‖taylorTermIntegrand n t q0 h u‖ ≤
        (seriesRatio q0 h)^n*Real.exp (-(q0/4)*u) :=
    Eventually.of_forall (taylorTermIntegrand_norm_le n t hq0 h)
  have hsumBound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      Summable (fun n : ℕ => (seriesRatio q0 h)^n*Real.exp (-(q0/4)*u)) :=
    Eventually.of_forall (fun u => hgeom.mul_right (Real.exp (-(q0/4)*u)))
  have hpoint : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)),
      HasSum (fun n => taylorTermIntegrand n t q0 h u) (kIntegrand t (q0+h) u) :=
    Eventually.of_forall (taylorTermIntegrand_pointwise_hasSum t q0 h)
  have hs := hasSum_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (fun n u => (seriesRatio q0 h)^n*Real.exp (-(q0/4)*u))
    hmeas hbound hsumBound hboundInt hpoint
  convert hs using 1
  funext n
  unfold taylorTermIntegrand taylorCoefficient qMoment
  rw [integral_const_mul]
  ring

theorem imaginaryOrderK_hasFPowerSeriesAt (t : ℝ) {q0 : ℝ} (hq0 : 0 < q0) :
    HasFPowerSeriesAt (imaginaryOrderK t) (actualTaylorSeries t q0) q0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by linarith : 0 < q0/2)] with h hh
  have habs : |h| < q0/2 := by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hh
  simpa only [actualTaylorSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul] using
    imaginaryOrderK_taylor_hasSum t hq0 habs

theorem taylorCoefficient_eq_iteratedDeriv (n : ℕ) (t : ℝ) {q0 : ℝ} (hq0 : 0 < q0) :
    taylorCoefficient n t q0 = iteratedDeriv n (imaginaryOrderK t) q0/(n.factorial : ℝ) := by
  rw [iteratedDeriv_imaginaryOrderK n t hq0]
  rfl

theorem imaginaryOrderK_analyticAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    AnalyticAt ℝ (imaginaryOrderK t) q := by
  exact ⟨actualTaylorSeries t q, imaginaryOrderK_hasFPowerSeriesAt t hq⟩

theorem imaginaryOrderK_analyticOnNhd (t : ℝ) :
    AnalyticOnNhd ℝ (imaginaryOrderK t) (Ioi 0) := by
  intro q hq
  exact imaginaryOrderK_analyticAt t hq

theorem imaginaryOrderK_div_analyticOnNhd (t : ℝ) :
    AnalyticOnNhd ℝ (fun q : ℝ => imaginaryOrderK t q/q) (Ioi 0) := by
  exact (imaginaryOrderK_analyticOnNhd t).div analyticOnNhd_id (fun q hq => hq.ne')

theorem complexK_analyticOnNhd (t : ℝ) :
    AnalyticOnNhd ℝ (fun q : ℝ => (imaginaryOrderK t q : ℂ)) (Ioi 0) := by
  intro q hq
  simpa only [Complex.ofRealCLM_apply] using
    (Complex.ofRealCLM.analyticAt (imaginaryOrderK t q)).comp (imaginaryOrderK_analyticAt t hq)

theorem complexK_div_analyticOnNhd (t : ℝ) :
    AnalyticOnNhd ℝ (fun q : ℝ => (imaginaryOrderK t q : ℂ)/(q : ℂ)) (Ioi 0) := by
  intro q hq
  simpa only [Complex.ofRealCLM_apply, Complex.ofReal_div] using
    (Complex.ofRealCLM.analyticAt (imaginaryOrderK t q/q)).comp
      (imaginaryOrderK_div_analyticOnNhd t q hq)

theorem imaginaryOrderK_contDiffOn_omega (t : ℝ) :
    ContDiffOn ℝ ω (imaginaryOrderK t) (Ioi 0) := by
  exact (imaginaryOrderK_analyticOnNhd t).contDiffOn_of_completeSpace

theorem imaginaryOrderK_div_contDiffOn_omega (t : ℝ) :
    ContDiffOn ℝ ω (fun q : ℝ => imaginaryOrderK t q/q) (Ioi 0) := by
  exact (imaginaryOrderK_div_analyticOnNhd t).contDiffOn_of_completeSpace

theorem complexK_div_contDiffOn_omega (t : ℝ) :
    ContDiffOn ℝ ω (fun q : ℝ => (imaginaryOrderK t q : ℂ)/(q : ℂ)) (Ioi 0) := by
  exact (complexK_div_analyticOnNhd t).contDiffOn_of_completeSpace

theorem extendedKKernel_analyticOnNhd (a : ℝ) (ha : 0 < a) (t : ℝ) :
    AnalyticOnNhd ℝ (fun q : ℝ => extendedKKernel a ha t q) (Ioi a) := by
  intro q hq
  have hqp : 0 < q := lt_trans ha hq
  have hc := complexK_div_analyticOnNhd t q hqp
  apply hc.congr
  filter_upwards [Ioi_mem_nhds hq] with r hr
  exact (extendedKKernel_eq a ha t r hr.le).symm

theorem extendedKKernel_contDiffOn_omega (a : ℝ) (ha : 0 < a) (t : ℝ) :
    ContDiffOn ℝ ω (fun q : ℝ => extendedKKernel a ha t q) (Ioi a) := by
  exact (extendedKKernel_analyticOnNhd a ha t).contDiffOn_of_completeSpace

theorem physical_extendedKKernel_analyticOnNhd {ι : Type*} (P : PacketData ι) (t : ℝ) :
    AnalyticOnNhd ℝ (fun q : ℝ => extendedKKernel (P.Y0/32)
      (by have h := P.Y0_pos; positivity) t q) (Ioi (P.Y0/32)) := by
  exact extendedKKernel_analyticOnNhd (P.Y0/32)
    (by have h := P.Y0_pos; positivity) t

end
end ImbalancedChen.Part3.ImaginaryOrderKQAnalyticSourceOnly
