import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Native imaginary-order radial cutoff energy

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is a direct Caccioppoli primitive for the actual equation
u'' = (exp(2r) - tau^2) u on a right half-line. It has no basis,
limit-point, energy, or integrability premise. Finite-interval
integrability is obtained from the genuine first/second derivative
jets. An arbitrary C1 cutoff vanishing at the two endpoints is allowed.
The real component identity is proved by differentiating the actual
flux eta^2 f f'; the complex estimate is its sum for real and imaginary
parts. No real-order I-growth theorem is used.

This module does not yet exhaust the cutoffs to infinity. L2
integrability of u' on a tail, zero Wronskians, and selection of the
actual K remain subsequent obligations.
-/

namespace ImbalancedChen.Part3.ImaginaryRadialCutoffEnergy20261026b

noncomputable section
open Set MeasureTheory

/-- Native C2 ODE data on the genuine tail. The derivative is the
actual derivative of u, and the second derivative is supplied by the
radial equation, with a real spectral parameter tau. -/
def TailSolution (tau R : ℝ) (u : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, R < r →
    HasDerivAt u (deriv u r) r ∧
    HasDerivAt (deriv u) (((Real.exp (2*r) - tau^2 : ℝ) : ℂ) * u r) r

private def realEnergy (tau : ℝ) (eta f p : ℝ → ℝ) (r : ℝ) : ℝ :=
  (deriv eta r*f r + eta r*p r)^2 +
    (Real.exp (2*r)-tau^2)*eta r^2*f r^2

private def realError (eta f : ℝ → ℝ) (r : ℝ) : ℝ :=
  (deriv eta r)^2*f r^2

private def realMass (eta f : ℝ → ℝ) (r : ℝ) : ℝ :=
  eta r^2*f r^2

private def realKinetic (eta p : ℝ → ℝ) (r : ℝ) : ℝ :=
  eta r^2*p r^2

private theorem component_continuity {a b tau : ℝ} {f p : ℝ → ℝ}
    (hf : ∀ r ∈ uIcc a b, HasDerivAt f (p r) r)
    (hp : ∀ r ∈ uIcc a b,
      HasDerivAt p ((Real.exp (2*r)-tau^2)*f r) r) :
    ContinuousOn f (uIcc a b) ∧ ContinuousOn p (uIcc a b) := by
  exact ⟨fun r hr => (hf r hr).continuousAt.continuousWithinAt,
    fun r hr => (hp r hr).continuousAt.continuousWithinAt⟩

/-- Exact cutoff IMS identity, proved from the ODE rather than assumed
as an energy statement. All functions are only required to solve the
ODE on this interval. -/
private theorem component_IMS {a b tau : ℝ} {eta f p : ℝ → ℝ}
    (heta : ContDiff ℝ 1 eta) (ha : eta a = 0) (hb : eta b = 0)
    (hf : ∀ r ∈ uIcc a b, HasDerivAt f (p r) r)
    (hp : ∀ r ∈ uIcc a b,
      HasDerivAt p ((Real.exp (2*r)-tau^2)*f r) r) :
    (∫ r in a..b, realEnergy tau eta f p r) =
      ∫ r in a..b, realError eta f r := by
  obtain ⟨hfc,hpc⟩ := component_continuity hf hp
  have hec : ContinuousOn eta (uIcc a b) := heta.continuous.continuousOn
  have hepc : ContinuousOn (deriv eta) (uIcc a b) :=
    (heta.continuous_deriv (by norm_num)).continuousOn
  have hvc : ContinuousOn (fun r : ℝ => Real.exp (2*r)-tau^2) (uIcc a b) := by
    fun_prop
  have hE : IntervalIntegrable (realEnergy tau eta f p) volume a b :=
    (((hepc.mul hfc).add (hec.mul hpc)).pow 2 |>.add
      (((hvc.mul (hec.pow 2)).mul (hfc.pow 2)))).intervalIntegrable
  have hErr : IntervalIntegrable (realError eta f) volume a b :=
    ((hepc.pow 2).mul (hfc.pow 2)).intervalIntegrable
  have hflux : ∀ r ∈ uIcc a b,
      HasDerivAt (fun s => eta s^2*f s*p s)
        (realEnergy tau eta f p r-realError eta f r) r := by
    intro r hr
    have hd := ((((heta.differentiable (by norm_num) r).hasDerivAt.pow 2).mul
      (hf r hr)).mul (hp r hr))
    convert hd using 1 <;> dsimp [realEnergy,realError] <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hflux (hE.sub hErr)
  rw [intervalIntegral.integral_sub hE hErr, ha, hb] at hFTC
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, sub_self] at hFTC
  linarith

/-- Finite-interval Caccioppoli for a genuine real component. The mass
term handles the negative part -tau^2 of the potential, so no artificial
positivity restriction on the starting height is imposed. -/
private theorem component_Caccioppoli {a b tau : ℝ} (hab : a ≤ b)
    {eta f p : ℝ → ℝ} (heta : ContDiff ℝ 1 eta)
    (ha : eta a = 0) (hb : eta b = 0)
    (hf : ∀ r ∈ uIcc a b, HasDerivAt f (p r) r)
    (hp : ∀ r ∈ uIcc a b,
      HasDerivAt p ((Real.exp (2*r)-tau^2)*f r) r) :
    (∫ r in a..b, realKinetic eta p r) ≤
      4*(∫ r in a..b, realError eta f r) +
        2*tau^2*(∫ r in a..b, realMass eta f r) := by
  obtain ⟨hfc,hpc⟩ := component_continuity hf hp
  have hec : ContinuousOn eta (uIcc a b) := heta.continuous.continuousOn
  have hepc : ContinuousOn (deriv eta) (uIcc a b) :=
    (heta.continuous_deriv (by norm_num)).continuousOn
  have hvc : ContinuousOn (fun r : ℝ => Real.exp (2*r)-tau^2) (uIcc a b) := by
    fun_prop
  have hE : IntervalIntegrable (realEnergy tau eta f p) volume a b :=
    (((hepc.mul hfc).add (hec.mul hpc)).pow 2 |>.add
      (((hvc.mul (hec.pow 2)).mul (hfc.pow 2)))).intervalIntegrable
  have hErr : IntervalIntegrable (realError eta f) volume a b :=
    ((hepc.pow 2).mul (hfc.pow 2)).intervalIntegrable
  have hM : IntervalIntegrable (realMass eta f) volume a b :=
    ((hec.pow 2).mul (hfc.pow 2)).intervalIntegrable
  have hK : IntervalIntegrable (realKinetic eta p) volume a b :=
    ((hec.pow 2).mul (hpc.pow 2)).intervalIntegrable
  have hpoint (r : ℝ) : realKinetic eta p r ≤
      2*realEnergy tau eta f p r + 2*tau^2*realMass eta f r +
        2*realError eta f r := by
    have hsq := sq_nonneg (eta r*p r+2*deriv eta r*f r)
    have hpos : 0 ≤ Real.exp (2*r)*eta r^2*f r^2 :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)) (sq_nonneg _)
    dsimp [realKinetic,realEnergy,realMass,realError]
    nlinarith
  have hbound := intervalIntegral.integral_mono_on hab hK
    (((hE.const_mul 2).add (hM.const_mul (2*tau^2))).add (hErr.const_mul 2))
    (fun r _ => hpoint r)
  rw [intervalIntegral.integral_add ((hE.const_mul 2).add
      (hM.const_mul (2*tau^2))) (hErr.const_mul 2),
    intervalIntegral.integral_add (hE.const_mul 2) (hM.const_mul (2*tau^2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, component_IMS heta ha hb hf hp] at hbound
  linarith

/-- Every term in the native complex Caccioppoli estimate is integrable,
independently of any L2 assumption on the whole tail. -/
theorem cutoff_terms_integrable {tau R a b : ℝ} {u : ℝ → ℂ}
    (hu : TailSolution tau R u) (hab : a ≤ b) (hRa : R < a)
    (eta : ℝ → ℝ) (heta : ContDiff ℝ 1 eta) :
    IntervalIntegrable (fun r => eta r^2*Complex.normSq (deriv u r)) volume a b ∧
      IntervalIntegrable (fun r => (deriv eta r)^2*Complex.normSq (u r)) volume a b ∧
      IntervalIntegrable (fun r => eta r^2*Complex.normSq (u r)) volume a b := by
  have ht (r : ℝ) (hr : r ∈ uIcc a b) : R < r :=
    hRa.trans_le ((show r ∈ Icc a b by simpa only [uIcc_of_le hab] using hr).1)
  have huc : ContinuousOn u (uIcc a b) :=
    fun r hr => (hu r (ht r hr)).1.continuousAt.continuousWithinAt
  have hpc : ContinuousOn (deriv u) (uIcc a b) :=
    fun r hr => (hu r (ht r hr)).2.continuousAt.continuousWithinAt
  have hec : ContinuousOn eta (uIcc a b) := heta.continuous.continuousOn
  have hepc : ContinuousOn (deriv eta) (uIcc a b) :=
    (heta.continuous_deriv (by norm_num)).continuousOn
  have hnormU : ContinuousOn (fun r => Complex.normSq (u r)) (uIcc a b) := by
    simpa only [Complex.normSq_apply, pow_two] using (huc.re.pow 2).add (huc.im.pow 2)
  have hnormP : ContinuousOn (fun r => Complex.normSq (deriv u r)) (uIcc a b) := by
    simpa only [Complex.normSq_apply, pow_two] using (hpc.re.pow 2).add (hpc.im.pow 2)
  exact ⟨((hec.pow 2).mul hnormP).intervalIntegrable,
    ((hepc.pow 2).mul hnormU).intervalIntegrable,
    ((hec.pow 2).mul hnormU).intervalIntegrable⟩

/-- Genuine native complex cutoff Caccioppoli. The only analytic input
is that u solves u''=(exp(2r)-tau^2)u on r>R; endpoint vanishing of the
C1 cutoff kills the actual flux boundary terms. In particular, the
energy estimate is a conclusion, not a hidden limit-point premise. -/
theorem tail_cutoff_Caccioppoli {tau R a b : ℝ} {u : ℝ → ℂ}
    (hu : TailSolution tau R u) (hab : a ≤ b) (hRa : R < a)
    (eta : ℝ → ℝ) (heta : ContDiff ℝ 1 eta)
    (ha : eta a = 0) (hb : eta b = 0) :
    (∫ r in a..b, eta r^2*Complex.normSq (deriv u r)) ≤
      4*(∫ r in a..b, (deriv eta r)^2*Complex.normSq (u r)) +
        2*tau^2*(∫ r in a..b, eta r^2*Complex.normSq (u r)) := by
  have ht (r : ℝ) (hr : r ∈ uIcc a b) : R < r := by
    have hlow : a ≤ r := (show r ∈ Icc a b by simpa only [uIcc_of_le hab] using hr).1
    exact hRa.trans_le hlow
  have hR1 (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun s => (u s).re) (deriv u r).re r :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hu r (ht r hr)).1
  have hI1 (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun s => (u s).im) (deriv u r).im r :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (hu r (ht r hr)).1
  have hR2 (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun s => (deriv u s).re)
        ((Real.exp (2*r)-tau^2)*(u r).re) r := by
    simpa only [Complex.re_ofReal_mul] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt r (hu r (ht r hr)).2
  have hI2 (r : ℝ) (hr : r ∈ uIcc a b) :
      HasDerivAt (fun s => (deriv u s).im)
        ((Real.exp (2*r)-tau^2)*(u r).im) r := by
    simpa only [Complex.im_ofReal_mul] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt r (hu r (ht r hr)).2
  have hreal := component_Caccioppoli hab heta ha hb hR1 hR2
  have himag := component_Caccioppoli hab heta ha hb hI1 hI2
  obtain ⟨hRc,hRpc⟩ := component_continuity hR1 hR2
  obtain ⟨hIc,hIpc⟩ := component_continuity hI1 hI2
  have hec : ContinuousOn eta (uIcc a b) := heta.continuous.continuousOn
  have hepc : ContinuousOn (deriv eta) (uIcc a b) :=
    (heta.continuous_deriv (by norm_num)).continuousOn
  have hKR : IntervalIntegrable (fun r => eta r^2*(deriv u r).re^2) volume a b :=
    ((hec.pow 2).mul (hRpc.pow 2)).intervalIntegrable
  have hKI : IntervalIntegrable (fun r => eta r^2*(deriv u r).im^2) volume a b :=
    ((hec.pow 2).mul (hIpc.pow 2)).intervalIntegrable
  have hER : IntervalIntegrable (fun r => (deriv eta r)^2*(u r).re^2) volume a b :=
    ((hepc.pow 2).mul (hRc.pow 2)).intervalIntegrable
  have hEI : IntervalIntegrable (fun r => (deriv eta r)^2*(u r).im^2) volume a b :=
    ((hepc.pow 2).mul (hIc.pow 2)).intervalIntegrable
  have hMR : IntervalIntegrable (fun r => eta r^2*(u r).re^2) volume a b :=
    ((hec.pow 2).mul (hRc.pow 2)).intervalIntegrable
  have hMI : IntervalIntegrable (fun r => eta r^2*(u r).im^2) volume a b :=
    ((hec.pow 2).mul (hIc.pow 2)).intervalIntegrable
  simp only [Complex.normSq_apply, ← pow_two, mul_add]
  rw [intervalIntegral.integral_add hKR hKI,
    intervalIntegral.integral_add hER hEI, intervalIntegral.integral_add hMR hMI]
  dsimp [realKinetic,realError,realMass] at hreal himag
  linarith

end
end ImbalancedChen.Part3.ImaginaryRadialCutoffEnergy20261026b


