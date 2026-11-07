import ImbalancedChen.Part3ImaginaryOrderKQDerivative
import ImbalancedChen.Part3ImaginaryOrderKHeightDecay
import Mathlib.Tactic

/-!
CODE_ONLY / SOURCEONLY / UNCOMPILED / 2026-10-24. No acceptance credit.
No compiler/checker/numerical helper or actual source edit is run.

Same actual q-calculus chain: the actual second q derivative is the integral
of +cosh(u)^2*exp(-q*cosh(u))*cos(2*t*u). All dominated differentiation
hypotheses are again proved from that actual kernel. Combined with the y
actual u-IBP identity, this gives the actual modified Bessel equation at
imaginary order 2it, with the exact sign q^2-4t^2.

Both intended local imports are SOURCEONLY candidates. No unrelated Bessel
library, normalized Kuznetsov kernel or spectral estimate is identified.
-/

namespace ImbalancedChen.Part3.ImaginaryOrderKSecondQDerivativeSourceOnly
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open ImaginaryOrderKBesselSourceOnly
open ImaginaryOrderKQDerivativeSourceOnly
open ImaginaryOrderKHeightDecaySourceOnly

def qSecondIntegrand (t q u : ℝ) : ℝ :=
  Real.cosh u^2 * Real.exp (-q*Real.cosh u) * Real.cos (2*t*u)

def qSecond (t q : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), qSecondIntegrand t q u

def qSecondMajorant (a u : ℝ) : ℝ :=
  (8/a^2)*Real.exp (-(a/4)*u)

lemma qDerivativeIntegrand_hasDerivAt_q (t q u : ℝ) :
    HasDerivAt (fun r => qDerivativeIntegrand t r u) (qSecondIntegrand t q u) q := by
  convert ((((hasDerivAt_id q).neg.mul_const (Real.cosh u)).exp.const_mul
    (-Real.cosh u)).mul_const (Real.cos (2*t*u))) using 1 <;>
    dsimp [qDerivativeIntegrand, qSecondIntegrand] <;> ring

lemma square_cosh_exp_bound {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.cosh u^2 * Real.exp (-a*Real.cosh u) ≤
      (8/a^2)*Real.exp (-(a/2)*Real.cosh u) := by
  have hp0 := Real.pow_div_factorial_le_exp
    (by positivity : 0 ≤ a*Real.cosh u/2) 2
  norm_num at hp0
  have hp : (a*Real.cosh u)^2 ≤ 8*Real.exp (a*Real.cosh u/2) := by
    nlinarith
  have hmul : a^2*(Real.cosh u^2*Real.exp (-a*Real.cosh u)) ≤
      8*Real.exp (-(a/2)*Real.cosh u) := by
    calc
      a^2*(Real.cosh u^2*Real.exp (-a*Real.cosh u)) =
          (a*Real.cosh u)^2*Real.exp (-a*Real.cosh u) := by ring
      _ ≤ (8*Real.exp (a*Real.cosh u/2))*Real.exp (-a*Real.cosh u) :=
        mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
      _ = 8*Real.exp (-(a/2)*Real.cosh u) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        ring
  apply (mul_le_mul_left (pow_pos ha 2)).mp
  calc
    a^2*(Real.cosh u^2*Real.exp (-a*Real.cosh u)) ≤
        8*Real.exp (-(a/2)*Real.cosh u) := hmul
    _ = a^2*((8/a^2)*Real.exp (-(a/2)*Real.cosh u)) := by
      field_simp [ha.ne'] <;> ring

lemma qSecondIntegrand_norm_le {a q : ℝ} (ha : 0 < a) (hq : a ≤ q)
    (t u : ℝ) :
    ‖qSecondIntegrand t q u‖ ≤ qSecondMajorant a u := by
  have he : Real.exp (-q*Real.cosh u) ≤ Real.exp (-a*Real.cosh u) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hq (Real.cosh_pos u).le
    linarith
  calc
    ‖qSecondIntegrand t q u‖ =
        Real.cosh u^2*Real.exp (-q*Real.cosh u)*|Real.cos (2*t*u)| := by
      simp only [qSecondIntegrand, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (Real.cosh u)), abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.cosh u^2*Real.exp (-q*Real.cosh u)*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
        (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    _ ≤ Real.cosh u^2*Real.exp (-a*Real.cosh u) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ ≤ (8/a^2)*Real.exp (-(a/2)*Real.cosh u) := square_cosh_exp_bound ha u
    _ ≤ qSecondMajorant a u :=
      mul_le_mul_of_nonneg_left (half_exp_le_linear ha u) (by positivity)

lemma qSecondMajorant_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (qSecondMajorant a) (Ioi 0) := by
  exact (integrableOn_exp_mul_Ioi (by linarith : -(a/4) < 0) 0).const_mul (8/a^2)

lemma qSecondIntegrand_integrable (t : ℝ) {q : ℝ} (hq : 0 < q) :
    IntegrableOn (qSecondIntegrand t q) (Ioi 0) := by
  have hc : Continuous (qSecondIntegrand t q) := by
    unfold qSecondIntegrand
    fun_prop
  exact (qSecondMajorant_integrable hq).mono' hc.aestronglyMeasurable
    (Eventually.of_forall (qSecondIntegrand_norm_le hq le_rfl t))

theorem qDerivative_hasDerivAt_qSecond (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (qDerivative t) (qSecond t q) q := by
  have ha : 0 < q/2 := by linarith
  have hs : Ioi (q/2) ∈ 𝓝 q := Ioi_mem_nhds (by linarith)
  have hF : ∀ᶠ r in 𝓝 q, AEStronglyMeasurable (qDerivativeIntegrand t r)
      (volume.restrict (Ioi (0 : ℝ))) := by
    apply Eventually.of_forall
    intro r
    have hc : Continuous (qDerivativeIntegrand t r) := by
      unfold qDerivativeIntegrand
      fun_prop
    exact hc.aestronglyMeasurable
  have hF' : AEStronglyMeasurable (qSecondIntegrand t q)
      (volume.restrict (Ioi (0 : ℝ))) := by
    have hc : Continuous (qSecondIntegrand t q) := by unfold qSecondIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q/2),
      ‖qSecondIntegrand t r u‖ ≤ qSecondMajorant (q/2) u := by
    exact Eventually.of_forall (fun u r hr => qSecondIntegrand_norm_le ha hr.le t u)
  have hdiff : ∀ᵐ u ∂volume.restrict (Ioi (0 : ℝ)), ∀ r ∈ Ioi (q/2),
      HasDerivAt (fun x => qDerivativeIntegrand t x u) (qSecondIntegrand t r u) r := by
    exact Eventually.of_forall (fun u r _ => qDerivativeIntegrand_hasDerivAt_q t r u)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r u => qDerivativeIntegrand t r u)
    (F' := fun r u => qSecondIntegrand t r u)
    (bound := qSecondMajorant (q/2)) hs hF (qDerivativeIntegrand_integrable t hq)
    hF' hbound (qSecondMajorant_integrable ha) hdiff).2

theorem deriv_imaginaryOrderK_hasDerivAt_qSecond (t : ℝ) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (deriv (imaginaryOrderK t)) (qSecond t q) q := by
  apply (qDerivative_hasDerivAt_qSecond t hq).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with r hr
  exact (imaginaryOrderK_hasDerivAt_q_integral t hr).deriv

theorem qSecond_continuousAt (t : ℝ) {q : ℝ} (hq : 0 < q) :
    ContinuousAt (qSecond t) q := by
  have ha : 0 < q/2 := by linarith
  change Tendsto (fun r : ℝ => ∫ u in Ioi (0 : ℝ), qSecondIntegrand t r u)
    (𝓝 q) (𝓝 (∫ u in Ioi (0 : ℝ), qSecondIntegrand t q u))
  apply tendsto_integral_filter_of_dominated_convergence (qSecondMajorant (q/2))
  · apply Eventually.of_forall
    intro r
    have hc : Continuous (qSecondIntegrand t r) := by unfold qSecondIntegrand; fun_prop
    exact hc.aestronglyMeasurable
  · filter_upwards [Ioi_mem_nhds (by linarith : q/2 < q)] with r hr
    exact Eventually.of_forall (qSecondIntegrand_norm_le ha hr.le t)
  · exact qSecondMajorant_integrable ha
  · apply Eventually.of_forall
    intro u
    have hc : Continuous (fun r : ℝ => qSecondIntegrand t r u) := by
      unfold qSecondIntegrand
      fun_prop
    exact hc.continuousAt

theorem qSecond_continuousOn (t : ℝ) : ContinuousOn (qSecond t) (Ioi 0) := by
  intro q hq
  exact (qSecond_continuousAt t hq).continuousWithinAt

theorem qDerivative_contDiffOn_one (t : ℝ) :
    ContDiffOn ℝ 1 (qDerivative t) (Ioi 0) := by
  have hd : DifferentiableOn ℝ (qDerivative t) (Ioi (0 : ℝ)) := by
    intro q hq
    exact (qDerivative_hasDerivAt_qSecond t hq).differentiableAt.differentiableWithinAt
  have hc : ContinuousOn (deriv (qDerivative t)) (Ioi (0 : ℝ)) :=
    (qSecond_continuousOn t).congr
      (fun q hq => (qDerivative_hasDerivAt_qSecond t hq).deriv)
  have hchar : ContDiffOn ℝ 1 (qDerivative t) (Ioi (0 : ℝ)) ↔
      DifferentiableOn ℝ (qDerivative t) (Ioi (0 : ℝ)) ∧
        ContinuousOn (deriv (qDerivative t)) (Ioi (0 : ℝ)) := by
    rw [show (1 : ℕ∞ω) = 0+1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    simp
  exact hchar.mpr ⟨hd,hc⟩

/-- qSecond is actually continuous, so the genuine K integral is C2 on the
positive q-axis; existence of a formal second-derivative expression alone
is not used as a substitute for this continuity proof. -/
theorem imaginaryOrderK_contDiffOn_two_q (t : ℝ) :
    ContDiffOn ℝ 2 (imaginaryOrderK t) (Ioi 0) := by
  have hD : ContDiffOn ℝ 1 (deriv (imaginaryOrderK t)) (Ioi (0 : ℝ)) :=
    (qDerivative_contDiffOn_one t).congr
      (fun q hq => (imaginaryOrderK_hasDerivAt_q_integral t hq).deriv)
  have hchar : ContDiffOn ℝ 2 (imaginaryOrderK t) (Ioi (0 : ℝ)) ↔
      DifferentiableOn ℝ (imaginaryOrderK t) (Ioi (0 : ℝ)) ∧
        ContDiffOn ℝ 1 (deriv (imaginaryOrderK t)) (Ioi (0 : ℝ)) := by
    rw [show (2 : ℕ∞ω) = 1+1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    simp
  exact hchar.mpr ⟨imaginaryOrderK_differentiableOn_q t,hD⟩

/-- Exact algebra at the actual u-integrand. cosh^2-sinh^2=1 accounts for
the q^2*K term; neither it nor the imaginary-order sign is discarded. -/
lemma twiceIBPIntegrand_q_calculus (t q u : ℝ) :
    twiceIBPIntegrand t q u =
      (-q)*qDerivativeIntegrand t q u -
        q^2*(qSecondIntegrand t q u-kIntegrand t q u) := by
  unfold twiceIBPIntegrand qDerivativeIntegrand qSecondIntegrand kIntegrand amplitude
  rw [Real.sinh_sq]
  ring

theorem actual_K_modifiedBessel_equation_integral (t : ℝ) {q : ℝ} (hq : 0 < q) :
    q^2*qSecond t q + q*qDerivative t q -
      (q^2-4*t^2)*imaginaryOrderK t q = 0 := by
  have hD := qDerivativeIntegrand_integrable t hq
  have hD2 := qSecondIntegrand_integrable t hq
  have hK := kIntegrand_integrable t hq
  have hR : (∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u) =
      (-q)*qDerivative t q - q^2*(qSecond t q-imaginaryOrderK t q) := by
    calc
      (∫ u in Ioi (0 : ℝ), twiceIBPIntegrand t q u) =
          ∫ u in Ioi (0 : ℝ), (-q)*qDerivativeIntegrand t q u -
            q^2*(qSecondIntegrand t q u-kIntegrand t q u) := by
        apply integral_congr_ae
        exact Eventually.of_forall (twiceIBPIntegrand_q_calculus t q)
      _ = _ := by
        rw [integral_sub (hD.const_mul (-q)) ((hD2.sub hK).const_mul (q^2)),
          integral_const_mul, integral_const_mul, integral_sub hD2 hK]
        rfl
  have hY := imaginaryOrderK_twiceIBP_mul t hq
  linear_combination hY + hR

/-- The genuine second q derivative of the actual K integral satisfies the
modified Bessel equation with nu^2=(2it)^2=-4t^2. Valid also at t=0. -/
theorem actual_K_modifiedBessel_equation (t : ℝ) {q : ℝ} (hq : 0 < q) :
    q^2*deriv (deriv (imaginaryOrderK t)) q +
      q*deriv (imaginaryOrderK t) q -
      (q^2-4*t^2)*imaginaryOrderK t q = 0 := by
  rw [(deriv_imaginaryOrderK_hasDerivAt_qSecond t hq).deriv,
    (imaginaryOrderK_hasDerivAt_q_integral t hq).deriv]
  exact actual_K_modifiedBessel_equation_integral t hq

end
end ImbalancedChen.Part3.ImaginaryOrderKSecondQDerivativeSourceOnly
