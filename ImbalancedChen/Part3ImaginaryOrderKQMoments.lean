import ImbalancedChen.Part3ImaginaryOrderKQDerivative
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
No compiler/checker/numerical helper or actual-source mutation is run.

The explicit actual q-moment family, rather than an abstract assumed smooth
family: M_n(t,q)=integral (-cosh u)^n exp(-q*cosh u) cos(2tu) du.
Every moment is absolutely integrable on q>0, with a q-uniform integrable
majorant for q>=a>0. Actual dominated differentiation proves M_n'=M_(n+1).
All moments are continuous in positive q. No spectral estimate is assumed.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKQMomentsSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly

def qMomentIntegrand (n : ℕ) (t q u : ℝ) : ℝ :=
  (-Real.cosh u)^n*Real.exp (-q*Real.cosh u)*Real.cos (2*t*u)

def qMoment (n : ℕ) (t q : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), qMomentIntegrand n t q u

def momentCoefficient (n : ℕ) (a : ℝ) : ℝ :=
  (n.factorial : ℝ)*(2/a)^n

def qMomentMajorant (n : ℕ) (a u : ℝ) : ℝ :=
  momentCoefficient n a*Real.exp (-(a/4)*u)

lemma qMomentIntegrand_hasDerivAt_q (n : ℕ) (t q u : ℝ) :
    HasDerivAt (fun r => qMomentIntegrand n t r u)
      (qMomentIntegrand (n+1) t q u) q := by
  convert ((((hasDerivAt_id q).neg.mul_const (Real.cosh u)).exp.const_mul
    ((-Real.cosh u)^n)).mul_const (Real.cos (2*t*u))) using 1 <;>
    dsimp [qMomentIntegrand] <;> rw [pow_succ] <;> ring

lemma momentCoefficient_nonneg (n : ℕ) {a : ℝ} (ha : 0 < a) :
    0 ≤ momentCoefficient n a := by
  unfold momentCoefficient
  positivity

lemma cosh_power_exp_bound (n : ℕ) {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.cosh u^n*Real.exp (-a*Real.cosh u) ≤
      momentCoefficient n a*Real.exp (-(a/2)*Real.cosh u) := by
  have hfac : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hp0 := Real.pow_div_factorial_le_exp
    (by positivity : 0 ≤ a*Real.cosh u/2) n
  have hp : (a*Real.cosh u/2)^n ≤
      (n.factorial : ℝ)*Real.exp (a*Real.cosh u/2) := by
    simpa only [mul_comm] using (div_le_iff₀ hfac).mp hp0
  have hmul : (a/2)^n*(Real.cosh u^n*Real.exp (-a*Real.cosh u)) ≤
      (n.factorial : ℝ)*Real.exp (-(a/2)*Real.cosh u) := by
    calc
      (a/2)^n*(Real.cosh u^n*Real.exp (-a*Real.cosh u)) =
          (a*Real.cosh u/2)^n*Real.exp (-a*Real.cosh u) := by
        simp only [div_pow, mul_pow]
        ring
      _ ≤ ((n.factorial : ℝ)*Real.exp (a*Real.cosh u/2))*
          Real.exp (-a*Real.cosh u) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = (n.factorial : ℝ)*Real.exp (-(a/2)*Real.cosh u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
  apply (mul_le_mul_left (pow_pos (by positivity : 0 < a/2) n)).mp
  calc
    (a/2)^n*(Real.cosh u^n*Real.exp (-a*Real.cosh u)) ≤
        (n.factorial : ℝ)*Real.exp (-(a/2)*Real.cosh u) := hmul
    _ = (a/2)^n*(momentCoefficient n a*Real.exp (-(a/2)*Real.cosh u)) := by
      unfold momentCoefficient
      simp only [div_pow]
      field_simp [ha.ne'] <;> ring

lemma qMomentIntegrand_norm_le (n : ℕ) {a q : ℝ} (ha : 0 < a) (hq : a ≤ q)
    (t u : ℝ) : ‖qMomentIntegrand n t q u‖ ≤ qMomentMajorant n a u := by
  have he : Real.exp (-q*Real.cosh u) ≤ Real.exp (-a*Real.cosh u) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le
    linarith
  calc
    ‖qMomentIntegrand n t q u‖ =
        Real.cosh u^n*Real.exp (-q*Real.cosh u)*|Real.cos (2*t*u)| := by
      simp only [qMomentIntegrand, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg,
        abs_of_pos (Real.cosh_pos u), abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.cosh u^n*Real.exp (-q*Real.cosh u)*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (mul_nonneg (pow_nonneg (Real.cosh_pos u).le n) (Real.exp_pos _).le)
    _ ≤ Real.cosh u^n*Real.exp (-a*Real.cosh u) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left he (pow_nonneg (Real.cosh_pos u).le n)
    _ ≤ momentCoefficient n a*Real.exp (-(a/2)*Real.cosh u) :=
      cosh_power_exp_bound n ha u
    _ ≤ qMomentMajorant n a u :=
      mul_le_mul_of_nonneg_left (half_exp_le_linear ha u) (momentCoefficient_nonneg n ha)

lemma qMomentMajorant_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (qMomentMajorant n a) (Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (by linarith : -(a/4) < 0) 0).const_mul
    (momentCoefficient n a)

lemma qMomentIntegrand_integrable (n : ℕ) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qMomentIntegrand n t q) (Ioi 0) := by
  have hc : Continuous (qMomentIntegrand n t q) := by unfold qMomentIntegrand; fun_prop
  exact (qMomentMajorant_integrable n hq).mono' hc.aestronglyMeasurable
    (Eventually.of_forall (qMomentIntegrand_norm_le n hq le_rfl t))

theorem qMoment_hasDerivAt_succ (n : ℕ) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (qMoment n t) (qMoment (n+1) t q) q := by
  have ha : 0 < q/2 := by linarith
  have hs : Ioi (q/2) ∈ 𝓝 q := Ioi_mem_nhds (by linarith)
  have hF : ∀ᶠ r in 𝓝 q, AEStronglyMeasurable (qMomentIntegrand n t r)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply Eventually.of_forall
    intro r
    have hc : Continuous (qMomentIntegrand n t r) := by unfold qMomentIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  have hF' : AEStronglyMeasurable (qMomentIntegrand (n+1) t q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : Continuous (qMomentIntegrand (n+1) t q) := by
      unfold qMomentIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q/2),
      ‖qMomentIntegrand (n+1) t r u‖ ≤ qMomentMajorant (n+1) (q/2) u := by
    exact Eventually.of_forall (fun u r hr => qMomentIntegrand_norm_le (n+1) ha hr.le t u)
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q/2),
      HasDerivAt (fun x => qMomentIntegrand n t x u) (qMomentIntegrand (n+1) t r u) r := by
    exact Eventually.of_forall (fun u r _ => qMomentIntegrand_hasDerivAt_q n t r u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r u => qMomentIntegrand n t r u)
    (F' := fun r u => qMomentIntegrand (n+1) t r u)
    (bound := qMomentMajorant (n+1) (q/2)) hs hF (qMomentIntegrand_integrable n t hq)
    hF' hbound (qMomentMajorant_integrable (n+1) ha) hdiff).2

theorem qMoment_continuousAt (n : ℕ) (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ContinuousAt (qMoment n t) q := by
  have ha : 0 < q/2 := by linarith
  change Tendsto (fun r : ℝ => ∫ u in Ioi (0 : ℝ), qMomentIntegrand n t r u)
    (𝓝 q) (𝓝 (∫ u in Ioi (0 : ℝ), qMomentIntegrand n t q u))
  apply tendsto_integral_filter_of_dominated_convergence (qMomentMajorant n (q/2))
  · apply Eventually.of_forall
    intro r
    have hc : Continuous (qMomentIntegrand n t r) := by unfold qMomentIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (by linarith : q/2 < q)] with r hr
    exact Eventually.of_forall (qMomentIntegrand_norm_le n ha hr.le t)
  · exact qMomentMajorant_integrable n ha
  · apply Eventually.of_forall
    intro u
    have hc : Continuous (fun r : ℝ => qMomentIntegrand n t r u) := by
      unfold qMomentIntegrand
      fun_prop
    exact hc.continuousAt

theorem qMoment_zero (t q : ℝ) : qMoment 0 t q = imaginaryOrderK t q := by
  simp only [qMoment, qMomentIntegrand, pow_zero, one_mul, imaginaryOrderK, kIntegrand]

theorem qMoment_one (t q : ℝ) : qMoment 1 t q = qDerivative t q := by
  simp only [qMoment, qMomentIntegrand, pow_one, qDerivative, qDerivativeIntegrand]

lemma qMomentMajorant_integral (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ u in Ioi (0 : ℝ), qMomentMajorant n a u) = momentCoefficient n a*(4/a) := by
  have hexp : (∫ u in Ioi (0 : ℝ), Real.exp (-(a/4)*u)) = 4/a := by
    rw [integral_exp_mul_Ioi (by linarith : -(a/4) < 0) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ha.ne']
  change (∫ u in Ioi (0 : ℝ), momentCoefficient n a*Real.exp (-(a/4)*u)) = _
  rw [integral_const_mul, hexp]

theorem qMoment_abs_le (n : ℕ) (t : ℝ) {a q : ℝ} (ha : 0 < a) (hq : a ≤ q) :
    |qMoment n t q| ≤ momentCoefficient n a*(4/a) := by
  calc
    |qMoment n t q| ≤ ∫ u in Ioi (0 : ℝ), qMomentMajorant n a u := by
      simpa only [qMoment, Real.norm_eq_abs] using
        norm_integral_le_of_norm_le (qMomentMajorant_integrable n ha)
          (Eventually.of_forall (qMomentIntegrand_norm_le n ha hq t))
    _ = _ := qMomentMajorant_integral n ha

end
end ImbalancedChen.Part3.ImaginaryOrderKQMomentsSourceOnly
