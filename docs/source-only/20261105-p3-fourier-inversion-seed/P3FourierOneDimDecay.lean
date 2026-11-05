import ImbalancedChen.P3FourierCutoffIdentity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
P3.6 / MANUSCRIPT INTERNAL / SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

A true one-dimensional Fourier derivative calculation at the locked Mathlib
convention exp(-2*pi*I*x*eta), followed by the exact xi=2*pi*eta
translation to the manuscript convention exp(-I*x*xi).

This is the first analytic (not finite combinatorial) factor of (F).
It does NOT establish the d-dimensional product decay, Fourier integrability
for the actual W/HB chart, or the quantitative multidimensional tail.
The primitive derivative input consists of C^2 regularity and the actual
integrability of derivatives through order two, NOT a hypothesis about
the Fourier decay that is being established.
-/

namespace ImbalancedChen.P3FourierOneDimDecay
noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
open P3FourierCutoffIdentity

/-- A non-2pi manuscript frequency xi corresponds to the pinned
Mathlib frequency eta=xi/(2*pi). -/
theorem physical_frequency_eq (xi : ℝ) :
    2 * Real.pi * (xi / (2 * Real.pi)) = xi := by
  have h : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp [h]

/-- The exact frequency renormalization applies coordinatewise, including
repeated derivative directions. This is algebra, not a Fourier transform
change-of-variables theorem. -/
theorem physical_frequency_factor (d : ℕ) (xi : Fin d → ℝ) :
    (∏ i : Fin d, (1 + (2 * Real.pi *
      (xi i / (2 * Real.pi))) ^ 2)) =
      ∏ i : Fin d, (1 + (xi i) ^ 2) := by
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_frequency_eq]

/-- Norm ≤ actual L1 norm directly from the pinned Fourier integral,
without assuming the transform itself is integrable. -/
private theorem norm_fourier_le_L1 (f : ℝ → ℂ) (eta : ℝ) :
    ‖𝓕 f eta‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  rw [Real.fourier_real_eq]
  calc
    ‖∫ x : ℝ, (𝐞 (-(x * eta))) • f x‖ ≤
      ∫ x : ℝ, ‖(𝐞 (-(x * eta))) • f x‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖f x‖ := by simp_rw [Circle.norm_smul]

/-- ONE actual 1D factor (1 + (2*pi*eta)^2). The key identity is
F(f'')=(2*pi*I*eta)^2 F(f)=- (2*pi*eta)^2 F(f).
The sum of the true f and f'' L1 norms pays the decay. -/
theorem two_derivative_fourier_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hderiv : ∀ n : ℕ, n ≤ (2 : ℕ∞) →
      Integrable (iteratedDeriv n f)) (eta : ℝ) :
    (1 + (2 * Real.pi * eta) ^ 2) * ‖𝓕 f eta‖ ≤
      (∫ x : ℝ, ‖f x‖) +
      (∫ x : ℝ, ‖iteratedDeriv 2 f x‖) := by
  have h2 : 𝓕 (iteratedDeriv 2 f) eta =
      (2 * Real.pi * Complex.I * (eta : ℂ)) ^ 2 • (𝓕 f eta) := by
    have h := Real.fourier_iteratedDeriv (f := f) hf hderiv
      (n := 2) (by norm_num : (2 : ℕ) ≤ (2 : ℕ∞))
    exact congrFun h eta
  have hI : (2 * Real.pi * Complex.I * (eta : ℂ)) ^ 2 =
      -((((2 * Real.pi * eta) ^ 2 : ℝ) : ℂ)) := by
    calc
      _ = ((((2 * Real.pi * eta) : ℝ) : ℂ) ^ 2) *
            Complex.I ^ 2 := by push_cast; ring
      _ = _ := by rw [Complex.I_sq]; push_cast; ring
  have hdiff : (𝓕 f eta) - (𝓕 (iteratedDeriv 2 f) eta) =
      (((1 + (2 * Real.pi * eta) ^ 2 : ℝ) : ℂ)) * (𝓕 f eta) := by
    rw [h2, smul_eq_mul, hI]
    push_cast
    ring
  have hden : 0 ≤ (1 + (2 * Real.pi * eta) ^ 2 : ℝ) := by positivity
  calc
    (1 + (2 * Real.pi * eta) ^ 2) * ‖𝓕 f eta‖ =
        ‖(𝓕 f eta) - (𝓕 (iteratedDeriv 2 f) eta)‖ := by
          rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hden]
    _ ≤ ‖𝓕 f eta‖ + ‖𝓕 (iteratedDeriv 2 f) eta‖ :=
      norm_sub_le _ _
    _ ≤ (∫ x : ℝ, ‖f x‖) +
          (∫ x : ℝ, ‖iteratedDeriv 2 f x‖) :=
      add_le_add (norm_fourier_le_L1 f eta)
        (norm_fourier_le_L1 (iteratedDeriv 2 f) eta)

/-- The manuscript's (1+xi^2)^(-1) bound for ONE variable,
where the numerator is a real, genuine derivative L1 ledger. -/
theorem manuscript_one_dim_decay (f : ℝ → ℂ)
    (hf : ContDiff ℝ (2 : ℕ∞) f)
    (hderiv : ∀ n : ℕ, n ≤ (2 : ℕ∞) →
      Integrable (iteratedDeriv n f)) (xi : ℝ) :
    ‖𝓕 f (xi / (2 * Real.pi))‖ ≤
      ((∫ x : ℝ, ‖f x‖) +
        (∫ x : ℝ, ‖iteratedDeriv 2 f x‖)) / (1 + xi ^ 2) := by
  have hh := two_derivative_fourier_decay f hf hderiv
    (xi / (2 * Real.pi))
  rw [physical_frequency_eq] at hh
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + xi ^ 2)).2
  simpa [mul_comm] using hh

/-- EXACT mass of one factor in MANUSCRIPT xi frequency.
The pinned Mathlib theorem is in its own non-scaled variable:
integral_(R) (1+xi²)^(-1)=pi. With d factors this gives pi^d,
and dividing by (2*pi)^d yields the expected 2^(-d).
The higher-dimensional Fubini step is NOT claimed here. -/
theorem manuscript_one_dim_cauchy_mass :
    (∫ xi : ℝ, (1 + xi ^ 2)⁻¹) = Real.pi := by
  exact Real.integral_univ_inv_one_add_sq

end
end ImbalancedChen.P3FourierOneDimDecay
