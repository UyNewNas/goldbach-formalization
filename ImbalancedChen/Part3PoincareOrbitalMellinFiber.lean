import ImbalancedChen.Part3PoincareOrbitalCosine
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-26.

The actual coupled radial orbital profile is parameterized by r=c^(-2).
For each actual positive output height y and Fourier variable u, its
literal r-Mellin transform is evaluated by r=y*(1+u^2)*v. Both radial
seeds, both negative Fourier signs, the principal complex power, and the
Jacobian are retained. Compact positive seed support proves absolute
convergence for every complex Mellin exponent at this fiber stage.

Convention checks: generalJ is DLMF10.2.2; complexOrderK is DLMF10.32.9.
DLMF10.32.11 is Basset's cosine representation, not a Weber formula.
The present source proves a coordinate/Mellin leaf only. Integrating in
u, Basset identification, a J/K orbital formula, the automorphic measure,
and Kuznetsov completeness are not assumed or claimed here.
-/

namespace ImbalancedChen.Part3.PoincareOrbitalMellinFiber20261026b

noncomputable section
open Set MeasureTheory Filter
open ImbalancedChen.Part3.PoincareOrbitalDilation20261026a
open ImbalancedChen.Part3.PoincareOrbitalCosine20261026a

/-- No Fourier scale is absorbed into the transform measure. -/
def oscillation (k : ℤ) (u v : ℝ) : ℂ :=
  Complex.exp (-Complex.I * (2 * Real.pi * (k : ℝ) * u * v : ℝ))

theorem oscillation_norm (k : ℤ) (u v : ℝ) : ‖oscillation k u v‖ = 1 := by
  simp [oscillation, Complex.norm_exp]

theorem oscillation_continuous (k : ℤ) (u : ℝ) : Continuous (oscillation k u) := by
  unfold oscillation
  fun_prop

/-- The literal Mellin-Fourier seed density, with Lebesgue dv. -/
def mellinSeedDensity (φ : ℝ → ℂ) (k : ℤ) (s : ℂ) (u v : ℝ) : ℂ :=
  (v : ℂ) ^ (s - 1) * oscillation k u v * φ v

def mellinSeed (φ : ℝ → ℂ) (k : ℤ) (s : ℂ) (u : ℝ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), mellinSeedDensity φ k s u v

/-- This is genuine absolute convergence, for every complex exponent;
positive compact seed support avoids both endpoints of the Mellin line. -/
theorem mellinSeedDensity_integrable (φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ))
    (k : ℤ) (s : ℂ) (u : ℝ) : Integrable (mellinSeedDensity φ k s u) := by
  have hp : ContinuousOn (fun v : ℝ => (v : ℂ) ^ (s - 1)) (tsupport φ) :=
    Complex.continuous_ofReal.continuousOn.cpow_const
      (fun v hv => Or.inl (by simpa using hposφ hv))
  have hc : ContinuousOn (mellinSeedDensity φ k s u) (tsupport φ) :=
    (hp.mul (oscillation_continuous k u).continuousOn).mul hφ.continuousOn
  have hs : Function.support (mellinSeedDensity φ k s u) ⊆ tsupport φ := by
    intro v hv
    apply subset_tsupport φ
    intro hz
    exact hv (by simp [mellinSeedDensity, hz])
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (hc.integrableOn_compact hcφ)

/-- The actual modulus c corresponding to the inverse-square scale r. -/
def scaleModulus (r : ℝ) : ℝ := (Real.sqrt r)⁻¹

/-- This reuses the literal actual orbital kernel; it is not a new
radial model with a prescribed transform. -/
def scaleOrbitalKernel (m n : ℤ) (ψ φ : ℝ → ℂ) (r y u : ℝ) : ℂ :=
  explicitOrbitalKernel (scaleModulus r) m n ψ φ (u, y)

def fiberScale (y u : ℝ) : ℝ := y * (1 + u ^ 2)

theorem fiberScale_pos {y : ℝ} (hy : 0 < y) (u : ℝ) : 0 < fiberScale y u :=
  mul_pos hy (by positivity)

theorem scaleModulus_pos {r : ℝ} (hr : 0 < r) : 0 < scaleModulus r :=
  inv_pos.mpr (Real.sqrt_pos.mpr hr)

/-- Exact original-height dictionary, including the square root of r. -/
theorem scale_orbitalHeight {r y : ℝ} (hr : 0 < r) (hy : 0 < y) (u : ℝ) :
    orbitalHeight (scaleModulus r) y u = r / fiberScale y u := by
  have hs := Real.sq_sqrt hr.le
  unfold orbitalHeight scaleModulus fiberScale
  rw [inv_pow, hs]
  field_simp [hr.ne', hy.ne', ne_of_gt (by positivity : 0 < 1 + u ^ 2)]

/-- Under the actual scale change, the two negative orbital phases
separate exactly. Neither m nor n is set to zero or changed in sign. -/
theorem scaleOrbitalKernel_at_fiberScale (m n : ℤ) (ψ φ : ℝ → ℂ)
    {y v : ℝ} (hy : 0 < y) (hv : 0 < v) (u : ℝ) :
    scaleOrbitalKernel m n ψ φ (fiberScale y u * v) y u =
      (y⁻¹ : ℂ) * star (ψ y) * oscillation m u y *
        oscillation n u v * φ v := by
  have hA := fiberScale_pos hy u
  have hh : orbitalHeight (scaleModulus (fiberScale y u * v)) y u = v := by
    rw [scale_orbitalHeight (mul_pos hA hv) hy, mul_div_cancel_left₀ _ hA.ne']
  unfold scaleOrbitalKernel explicitOrbitalKernel
  rw [hh]
  have he : -Complex.I * (orbitalPhase (scaleModulus (fiberScale y u * v)) m n y u : ℂ) =
      -Complex.I * (2 * Real.pi * (m : ℝ) * u * y : ℝ) +
        -Complex.I * (2 * Real.pi * (n : ℝ) * u * v : ℝ) := by
    unfold orbitalPhase
    rw [hh]
    push_cast
    ring
  rw [he, Complex.exp_add]
  unfold oscillation
  ring

/-- The literal r-Mellin density of the actual coupled orbital fiber. -/
def orbitalMellinDensity (m n : ℤ) (ψ φ : ℝ → ℂ) (s : ℂ)
    (y u r : ℝ) : ℂ :=
  (r : ℂ) ^ (s - 1) * scaleOrbitalKernel m n ψ φ r y u

def fiberCoefficient (m : ℤ) (ψ : ℝ → ℂ) (s : ℂ) (y u : ℝ) : ℂ :=
  (fiberScale y u : ℂ) ^ s * (y⁻¹ : ℂ) * star (ψ y) * oscillation m u y

/-- The actual positive Jacobian combines with the Mellin power to
give A^s, not A^(s-1), where A=y*(1+u^2). -/
theorem orbitalMellinDensity_pullback (m n : ℤ) (ψ φ : ℝ → ℂ) (s : ℂ)
    {y v : ℝ} (hy : 0 < y) (hv : 0 < v) (u : ℝ) :
    (fiberScale y u : ℂ) *
        orbitalMellinDensity m n ψ φ s y u (fiberScale y u * v) =
      fiberCoefficient m ψ s y u * mellinSeedDensity φ n s u v := by
  have hA := fiberScale_pos hy u
  have hAC : (fiberScale y u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hp : (fiberScale y u : ℂ) * (fiberScale y u : ℂ) ^ (s - 1) =
      (fiberScale y u : ℂ) ^ s := by
    rw [← Complex.cpow_one (fiberScale y u : ℂ), ← Complex.cpow_add _ _ hAC]
    congr 1
    ring
  unfold orbitalMellinDensity
  rw [scaleOrbitalKernel_at_fiberScale m n ψ φ hy hv u, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hA.le hv.le]
  unfold fiberCoefficient mellinSeedDensity
  calc
    _ = ((fiberScale y u : ℂ) * (fiberScale y u : ℂ) ^ (s - 1)) *
        (y⁻¹ : ℂ) * star (ψ y) * oscillation m u y *
          ((v : ℂ) ^ (s - 1) * oscillation n u v * φ v) := by ring
    _ = _ := by rw [hp]

/-- True absolute convergence of the actual orbital Mellin fiber.
No oscillatory convergence or Mellin identity is an input. -/
theorem orbitalMellinDensity_integrable (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ)
    (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) (s : ℂ)
    {y : ℝ} (hy : 0 < y) (u : ℝ) :
    IntegrableOn (orbitalMellinDensity m n ψ φ s y u) (Ioi (0 : ℝ)) := by
  have hA := fiberScale_pos hy u
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun v _ => by simpa only [mul_one] using
      ((hasDerivAt_id v).const_mul (fiberScale y u)).hasDerivWithinAt)
    (fun v _ w _ hvw => mul_left_cancel₀ hA.ne' hvw)
    (orbitalMellinDensity m n ψ φ s y u)
  rw [image_mul_left_Ioi hA, mul_zero] at hchange
  apply hchange.mpr
  apply ((mellinSeedDensity_integrable φ hφ hcφ hposφ n s u).const_mul
    (fiberCoefficient m ψ s y u)).integrableOn.congr_fun _ measurableSet_Ioi
  intro v hv
  rw [abs_of_pos hA, Complex.real_smul]
  exact (orbitalMellinDensity_pullback m n ψ φ s hy hv u).symm

/-- An evaluated actual Mellin transform, with its derived coefficient.
This is a fiber identity and makes no unproved exchange in u or y. -/
theorem actual_orbital_mellin_fiber (m n : ℤ) (ψ φ : ℝ → ℂ) (s : ℂ)
    {y : ℝ} (hy : 0 < y) (u : ℝ) :
    (∫ r in Ioi (0 : ℝ), orbitalMellinDensity m n ψ φ s y u r) =
      fiberCoefficient m ψ s y u * mellinSeed φ n s u := by
  have hA := fiberScale_pos hy u
  have hscale := integral_comp_mul_left_Ioi'
    (orbitalMellinDensity m n ψ φ s y u) 0 hA
  rw [mul_zero, Complex.real_smul, ← integral_const_mul] at hscale
  rw [← hscale]
  calc
    _ = ∫ v in Ioi (0 : ℝ),
        fiberCoefficient m ψ s y u * mellinSeedDensity φ n s u v := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      exact orbitalMellinDensity_pullback m n ψ φ s hy hv u
    _ = _ := by rw [integral_const_mul]; rfl

end
end ImbalancedChen.Part3.PoincareOrbitalMellinFiber20261026b
