import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Direct physical-height coercivity for -y^2 f'' + a f = 0. The first and
second derivatives are the ACTUAL derivatives on y>0. Finite positive
interval integrability and the cutoff flux identity are proved from
these jets. A C1 cutoff vanishing at the endpoints yields
a integral eta^2 |f|^2/y^2 <= integral |eta'|^2 |f|^2.
No energy estimate, Euler basis, growth bound or global mass is assumed.
No held constant-mode logarithmic-operator source is imported.
-/
namespace ImbalancedChen.Part3.PositiveZeroModePhysicalCaccioppoli20261026b

noncomputable section
open Set MeasureTheory

def PositiveHeightSolution (a : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ y : ℝ, 0 < y → HasDerivAt f (deriv f y) y ∧
    HasDerivAt (deriv f) (((a / y^2 : ℝ) : ℂ) * f y) y

private def componentEnergy (a : ℝ) (eta f p : ℝ → ℝ) (y : ℝ) : ℝ :=
  (deriv eta y * f y + eta y * p y)^2 + a * (eta y^2 * f y^2 / y^2)

private def componentError (eta f : ℝ → ℝ) (y : ℝ) : ℝ := (deriv eta y)^2 * f y^2

private def componentMass (eta f : ℝ → ℝ) (y : ℝ) : ℝ := eta y^2 * f y^2 / y^2

private theorem component_cutoff_IMS {a c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {eta f p : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hetac : eta c = 0) (hetad : eta d = 0)
    (hf : ∀ y ∈ uIcc c d, HasDerivAt f (p y) y)
    (hp : ∀ y ∈ uIcc c d, HasDerivAt p ((a / y^2) * f y) y) :
    (∫ y in c..d, componentEnergy a eta f p y) =
      ∫ y in c..d, componentError eta f y := by
  have hpos : ∀ y ∈ uIcc c d, 0 < y := by
    intro y hy
    exact hc.trans_le ((show y ∈ Icc c d by simpa only [uIcc_of_le hcd] using hy).1)
  have hfc : ContinuousOn f (uIcc c d) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (uIcc c d) := fun y hy => (hp y hy).continuousAt.continuousWithinAt
  have hec := heta.continuous.continuousOn (s := uIcc c d)
  have hepc := (heta.continuous_deriv (by norm_num)).continuousOn (s := uIcc c d)
  have hmassc : ContinuousOn (componentMass eta f) (uIcc c d) :=
    ((hec.pow 2).mul (hfc.pow 2)).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (hpos y hy)))
  have hE : IntervalIntegrable (componentEnergy a eta f p) volume c d :=
    (((hepc.mul hfc).add (hec.mul hpc)).pow 2 |>.add (hmassc.const_mul a)).intervalIntegrable
  have hErr : IntervalIntegrable (componentError eta f) volume c d :=
    ((hepc.pow 2).mul (hfc.pow 2)).intervalIntegrable
  have hflux : ∀ y ∈ uIcc c d,
      HasDerivAt (fun t => eta t^2 * f t * p t)
        (componentEnergy a eta f p y - componentError eta f y) y := by
    intro y hy
    have hd := ((((heta.differentiable (by norm_num) y).hasDerivAt.pow 2).mul
      (hf y hy)).mul (hp y hy))
    convert hd using 1 <;> dsimp [componentEnergy, componentMass, componentError] <;> ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hflux (hE.sub hErr)
  rw [intervalIntegral.integral_sub hE hErr, hetac, hetad] at hFTC
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, sub_self] at hFTC
  linarith

private theorem component_cutoff_Caccioppoli {a c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {eta f p : ℝ → ℝ} (heta : ContDiff ℝ 1 eta) (hetac : eta c = 0) (hetad : eta d = 0)
    (hf : ∀ y ∈ uIcc c d, HasDerivAt f (p y) y)
    (hp : ∀ y ∈ uIcc c d, HasDerivAt p ((a / y^2) * f y) y) :
    a * (∫ y in c..d, componentMass eta f y) ≤ ∫ y in c..d, componentError eta f y := by
  have hpos : ∀ y ∈ uIcc c d, 0 < y := by
    intro y hy
    exact hc.trans_le ((show y ∈ Icc c d by simpa only [uIcc_of_le hcd] using hy).1)
  have hfc : ContinuousOn f (uIcc c d) := fun y hy => (hf y hy).continuousAt.continuousWithinAt
  have hpc : ContinuousOn p (uIcc c d) := fun y hy => (hp y hy).continuousAt.continuousWithinAt
  have hec := heta.continuous.continuousOn (s := uIcc c d)
  have hepc := (heta.continuous_deriv (by norm_num)).continuousOn (s := uIcc c d)
  have hmc : ContinuousOn (componentMass eta f) (uIcc c d) :=
    ((hec.pow 2).mul (hfc.pow 2)).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (hpos y hy)))
  have hMi := hmc.intervalIntegrable
  have hEi : IntervalIntegrable (componentEnergy a eta f p) volume c d :=
    (((hepc.mul hfc).add (hec.mul hpc)).pow 2 |>.add (hmc.const_mul a)).intervalIntegrable
  calc
    a * (∫ y in c..d, componentMass eta f y) =
        ∫ y in c..d, a * componentMass eta f y := (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ y in c..d, componentEnergy a eta f p y :=
      intervalIntegral.integral_mono_on hcd (hMi.const_mul a) hEi (fun y _ => by
        dsimp [componentEnergy]
        linarith [sq_nonneg (deriv eta y * f y + eta y * p y)])
    _ = _ := component_cutoff_IMS hc hcd heta hetac hetad hf hp

theorem physical_cutoff_terms_integrable {a c d : ℝ} {f : ℝ → ℂ}
    (hf : PositiveHeightSolution a f) (hc : 0 < c) (hcd : c ≤ d)
    (eta : ℝ → ℝ) (heta : ContDiff ℝ 1 eta) :
    IntervalIntegrable (fun y => eta y^2 * Complex.normSq (f y) / y^2) volume c d ∧
      IntervalIntegrable (fun y => (deriv eta y)^2 * Complex.normSq (f y)) volume c d := by
  have hpos : ∀ y ∈ uIcc c d, 0 < y := by
    intro y hy
    exact hc.trans_le ((show y ∈ Icc c d by simpa only [uIcc_of_le hcd] using hy).1)
  have hfc : ContinuousOn f (uIcc c d) :=
    fun y hy => (hf y (hpos y hy)).1.continuousAt.continuousWithinAt
  have hnc : ContinuousOn (fun y => Complex.normSq (f y)) (uIcc c d) := by
    simpa only [Complex.normSq_apply, pow_two] using (hfc.re.pow 2).add (hfc.im.pow 2)
  have hec := heta.continuous.continuousOn (s := uIcc c d)
  have hepc := (heta.continuous_deriv (by norm_num)).continuousOn (s := uIcc c d)
  exact ⟨(((hec.pow 2).mul hnc).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (hpos y hy)))).intervalIntegrable,
    ((hepc.pow 2).mul hnc).intervalIntegrable⟩

/-- Genuine complex physical-height Caccioppoli. This conclusion is
derived from the actual ODE, not supplied as an energy hypothesis. -/
theorem physical_positive_zeroMode_Caccioppoli {a c d : ℝ} {f : ℝ → ℂ}
    (hf : PositiveHeightSolution a f) (hc : 0 < c) (hcd : c ≤ d)
    (eta : ℝ → ℝ) (heta : ContDiff ℝ 1 eta) (hetac : eta c = 0) (hetad : eta d = 0) :
    a * (∫ y in c..d, eta y^2 * Complex.normSq (f y) / y^2) ≤
      ∫ y in c..d, (deriv eta y)^2 * Complex.normSq (f y) := by
  have hpos : ∀ y ∈ uIcc c d, 0 < y := by
    intro y hy
    exact hc.trans_le ((show y ∈ Icc c d by simpa only [uIcc_of_le hcd] using hy).1)
  have hR : ∀ y ∈ uIcc c d, HasDerivAt (fun t => (f t).re) (deriv f y).re y :=
    fun y hy => Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hf y (hpos y hy)).1
  have hI : ∀ y ∈ uIcc c d, HasDerivAt (fun t => (f t).im) (deriv f y).im y :=
    fun y hy => Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hf y (hpos y hy)).1
  have hR2 : ∀ y ∈ uIcc c d,
      HasDerivAt (fun t => (deriv f t).re) ((a / y^2) * (f y).re) y := by
    intro y hy
    simpa only [Complex.re_ofReal_mul] using
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hf y (hpos y hy)).2
  have hI2 : ∀ y ∈ uIcc c d,
      HasDerivAt (fun t => (deriv f t).im) ((a / y^2) * (f y).im) y := by
    intro y hy
    simpa only [Complex.im_ofReal_mul] using
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hf y (hpos y hy)).2
  have hreal := component_cutoff_Caccioppoli hc hcd heta hetac hetad hR hR2
  have himag := component_cutoff_Caccioppoli hc hcd heta hetac hetad hI hI2
  have hec := heta.continuous.continuousOn (s := uIcc c d)
  have hepc := (heta.continuous_deriv (by norm_num)).continuousOn (s := uIcc c d)
  have hRc : ContinuousOn (fun y => (f y).re) (uIcc c d) :=
    fun y hy => (hR y hy).continuousAt.continuousWithinAt
  have hIc : ContinuousOn (fun y => (f y).im) (uIcc c d) :=
    fun y hy => (hI y hy).continuousAt.continuousWithinAt
  have hMR : IntervalIntegrable (fun y => eta y^2 * (f y).re^2 / y^2) volume c d :=
    (((hec.pow 2).mul (hRc.pow 2)).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (hpos y hy)))).intervalIntegrable
  have hMI : IntervalIntegrable (fun y => eta y^2 * (f y).im^2 / y^2) volume c d :=
    (((hec.pow 2).mul (hIc.pow 2)).div (continuousOn_id.pow 2)
      (fun y hy => pow_ne_zero 2 (ne_of_gt (hpos y hy)))).intervalIntegrable
  have hER : IntervalIntegrable (fun y => (deriv eta y)^2 * (f y).re^2) volume c d :=
    ((hepc.pow 2).mul (hRc.pow 2)).intervalIntegrable
  have hEI : IntervalIntegrable (fun y => (deriv eta y)^2 * (f y).im^2) volume c d :=
    ((hepc.pow 2).mul (hIc.pow 2)).intervalIntegrable
  simp only [Complex.normSq_apply, ← pow_two, mul_add, add_div]
  rw [intervalIntegral.integral_add hMR hMI, intervalIntegral.integral_add hER hEI]
  dsimp [componentMass, componentError] at hreal himag
  linarith

end
end ImbalancedChen.Part3.PositiveZeroModePhysicalCaccioppoli20261026b
