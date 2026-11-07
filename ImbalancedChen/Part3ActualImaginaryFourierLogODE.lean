import ImbalancedChen.Part3ActualFourierBesselLogL2
import ImbalancedChen.Part3ImaginaryRadialCutoffEnergy
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Actual signed Fourier coefficients: imaginary-order logarithmic ODE

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original periodic C2 Maass PDE at lambda=1/4+tau^2 supplies the
literal signed Fourier coefficient's q-Bessel jets. Actual exp chain
rules prove the native log ODE, and the original spatial strip norm
supplies its L2 tail by the existing exact Jacobian/Parseval theorem.
The frequency is 2*pi*|n|; the signed n remains in the Fourier phase.
The lower log endpoint is exactly log(2*pi*|n|*Y), and no scale constant
is lost. This clean coordinate/PDE leaf does not import the held
imaginary-order derivative-L2 or K-selection chain.
-/

namespace ImbalancedChen.Part3.ActualImaginaryFourierLogODE20261026b

noncomputable section
open Set MeasureTheory
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open ActualFourierBesselLogL220261026a ImaginaryRadialCutoffEnergy20261026b
attribute [local instance] Measure.Subtype.measureSpace

def actualFourierLogMode (u : ℝ × ℝ → ℂ) (n : ℤ) (r : ℝ) : ℂ :=
  actualBesselMode u n (Real.exp r)

private theorem imaginary_spectral_parameter (tau : ℝ) :
    (1/4 : ℂ)-((tau : ℂ)*Complex.I)^2 = ((1/4+tau^2 : ℝ) : ℂ) := by
  rw [mul_pow,Complex.I_sq]
  push_cast
  ring

private theorem imaginary_log_coefficient (tau r : ℝ) :
    ((Real.exp (2*r)-tau^2 : ℝ) : ℂ) =
      (Real.exp r : ℂ)^2+((tau : ℂ)*Complex.I)^2 := by
  have he : Real.exp (2*r) = (Real.exp r)^2 := by
    rw [show 2*r=r+r by ring,Real.exp_add,pow_two]
  rw [he,mul_pow,Complex.I_sq]
  push_cast
  ring

variable {u : ℝ × ℝ → ℂ} {tau : ℝ} {n : ℤ}
variable (hu : ContDiffOn ℝ 2 u upperDomain)
  (hp : ∀ x y : ℝ, 0 < y → u (x+1,y)=u(x,y))
  (hPDE : ∀ p ∈ upperDomain,
    -(p.2 : ℂ)^2*(partialX (partialX u) p+partialY (partialY u) p) =
      ((1/4+tau^2 : ℝ) : ℂ)*u p)
  (hn : n ≠ 0)

private theorem actual_imaginary_qjet {q : ℝ} (hq : 0 < q) :
    HasDerivAt (actualBesselMode u n) (deriv (actualBesselMode u n) q) q ∧
      HasDerivAt (deriv (actualBesselMode u n))
        (deriv (deriv (actualBesselMode u n)) q) q ∧
      (q : ℂ)^2*deriv (deriv (actualBesselMode u n)) q+
        (q : ℂ)*deriv (actualBesselMode u n) q-
        ((q : ℂ)^2+((tau : ℂ)*Complex.I)^2)*actualBesselMode u n q=0 := by
  apply actual_fourier_bessel_jet hu hp ((tau : ℂ)*Complex.I) _ hn hq
  simpa only [imaginary_spectral_parameter] using hPDE

/-- The first native derivative of the actual Fourier log mode. -/
theorem actualFourierLogMode_hasDerivAt (r : ℝ) :
    HasDerivAt (actualFourierLogMode u n)
      (Real.exp r • deriv (actualBesselMode u n) (Real.exp r)) r := by
  simpa only [actualFourierLogMode,Function.comp_def] using
    (actual_imaginary_qjet hu hp hPDE hn (Real.exp_pos r)).1.scomp r (Real.hasDerivAt_exp r)

/-- Native second derivative and actual imaginary-order radial ODE.
The signed Fourier coefficient and all native q derivatives came from
the original periodic C2 PDE rather than supplied coefficient data. -/
theorem actualFourierLogMode_second_hasDerivAt (r : ℝ) :
    HasDerivAt (deriv (actualFourierLogMode u n))
      (((Real.exp (2*r)-tau^2 : ℝ) : ℂ)*actualFourierLogMode u n r) r := by
  have hfirst : deriv (actualFourierLogMode u n) =
      fun s => Real.exp s • deriv (actualBesselMode u n) (Real.exp s) := by
    funext s
    exact (actualFourierLogMode_hasDerivAt hu hp hPDE hn s).deriv
  have hjet := actual_imaginary_qjet hu hp hPDE hn (Real.exp_pos r)
  have hd := (Real.hasDerivAt_exp r).smul
    (hjet.2.1.scomp r (Real.hasDerivAt_exp r))
  rw [hfirst]
  convert hd using 1
  simp only [smul_smul,Complex.real_smul,Complex.ofReal_mul,actualFourierLogMode]
  rw [imaginary_log_coefficient]
  linear_combination -hjet.2.2

/-- Genuine native radial solution data on any real log tail, derived
from the original actual Maass function at lambda=1/4+tau^2. -/
theorem actualFourierLogMode_tailSolution (R : ℝ) :
    TailSolution tau R (actualFourierLogMode u n) := by
  intro r _
  constructor
  · exact (actualFourierLogMode_hasDerivAt hu hp hPDE hn r).differentiableAt.hasDerivAt
  · exact actualFourierLogMode_second_hasDerivAt hu hp hPDE hn r

/-- End-to-end original PDE plus raw physical strip L2 gives both native
ODE jets and log-tail L2, including tau=0 and both signs of n. The exact
endpoint and measure normalization are retained. -/
theorem actualFourierLogMode_ODE_and_L2_of_strip {Y : ℝ} (hY : 0 < Y)
    (hstrip : Integrable (fun p : PeriodCell × ℝ => p.2⁻¹^2*‖u (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y)))) :
    TailSolution tau (Real.log (modeFrequency n*Y)) (actualFourierLogMode u n) ∧
      MemLp (actualFourierLogMode u n) 2
        (volume.restrict (Ioi (Real.log (modeFrequency n*Y)))) := by
  exact ⟨actualFourierLogMode_tailSolution hu hp hPDE hn _,
    actual_fourier_log_bessel_memLp_of_strip hu hY hstrip hn⟩

end
end ImbalancedChen.Part3.ActualImaginaryFourierLogODE20261026b
