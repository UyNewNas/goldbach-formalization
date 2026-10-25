import ImbalancedChen.Part3ActualKLCompactTestWeightedL2
import ImbalancedChen.Part3KLDensityMeasure
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Exact coordinate changes between three concrete raw KL density measures.
The positive-axis Jacobian theorem supplies the measure equalities. No
spectral measure, Plancherel equality, automorphic normalization, Gamma
factor, or dt/cosh(pi*t) identification is assumed or concluded.
-/

namespace ImbalancedChen.Part3.ActualKLCoordinateMeasures20261025a

noncomputable section
open Set MeasureTheory
open scoped ENNReal

/-- Native order parameter for K_{i*tau}. -/
def tauDensity (tau : ℝ) : ℝ :=
  (2 / Real.pi ^ 2) * tau * Real.sinh (Real.pi * tau)

/-- Energy coordinate lambda=tau^2. The Jacobian cancels the factor 2*tau. -/
def energyDensity (lam : ℝ) : ℝ :=
  Real.sinh (Real.pi * Real.sqrt lam) / Real.pi ^ 2

/-- Half-order parameter t=tau/2, hence K_{2it}. -/
def halfOrderDensity (t : ℝ) : ℝ :=
  (8 / Real.pi ^ 2) * t * Real.sinh (2 * Real.pi * t)

def positiveDensityMeasure (w : ℝ → ℝ) : Measure ℝ :=
  ((volume : Measure ℝ).restrict (Ioi 0)).withDensity
    (fun x => ENNReal.ofReal (w x))

def tauMeasure : Measure ℝ := positiveDensityMeasure tauDensity
def energyMeasure : Measure ℝ := positiveDensityMeasure energyDensity
def halfOrderMeasure : Measure ℝ := positiveDensityMeasure halfOrderDensity

@[simp] theorem tauDensity_eq_actualKLWeight (tau : ℝ) :
    tauDensity tau =
      ActualKLCompactTestWeightedL220261025a.actualKLWeight tau := rfl

/-- Relates the old unnormalized candidate to the correctly normalized raw
half-order density, without identifying either with a spectral measure. -/
theorem halfOrderDensity_eq_candidate (t : ℝ) :
    halfOrderDensity t = (8 / Real.pi ^ 2) *
      P3KLDensityMeasureSourceOnly.candidateDensity t := by
  simp only [halfOrderDensity, P3KLDensityMeasureSourceOnly.candidateDensity]
  ring

private theorem measurable_tauDensity : Measurable tauDensity := by
  unfold tauDensity
  fun_prop
private theorem measurable_energyDensity : Measurable energyDensity := by
  unfold energyDensity
  fun_prop
private theorem measurable_halfOrderDensity : Measurable halfOrderDensity := by
  unfold halfOrderDensity
  fun_prop

/-- A genuine density pushforward theorem on the positive axis. The only
pointwise density premise is the Jacobian identity; no measure identity is
assumed. This proof uses Mathlib's differentiable change of variables. -/
theorem map_positiveDensityMeasure_of_jacobian
    (f df source target : ℝ → ℝ)
    (hf : Measurable f)
    (hsource : Measurable source) (htarget : Measurable target)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt f (df x) (Ioi 0) x)
    (hinj : InjOn f (Ioi (0 : ℝ)))
    (himage : f '' Ioi (0 : ℝ) = Ioi (0 : ℝ))
    (hweight : ∀ x ∈ Ioi (0 : ℝ), source x = |df x| * target (f x)) :
    Measure.map f (positiveDensityMeasure source) = positiveDensityMeasure target := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hf]
  unfold positiveDensityMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ hsource.ennreal_ofReal (hg.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ htarget.ennreal_ofReal hg]
  have hj := lintegral_image_eq_lintegral_abs_deriv_mul
    measurableSet_Ioi hderiv hinj
    (fun y => ENNReal.ofReal (target y) * g y)
  rw [himage] at hj
  rw [hj]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_Ioi :
    MeasurableSet (Ioi (0 : ℝ)))] with x hx
  change ENNReal.ofReal (source x) * g (f x) =
    ENNReal.ofReal |df x| * (ENNReal.ofReal (target (f x)) * g (f x))
  rw [hweight x hx, ENNReal.ofReal_mul (abs_nonneg _), mul_assoc]

private theorem square_image_positive :
    (fun x : ℝ => x ^ 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sq_pos_of_pos hx
  · intro hy
    exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩

private theorem square_inj_positive : InjOn (fun x : ℝ => x ^ 2) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  nlinarith

/-- Exact cancellation of the energy-coordinate Jacobian. -/
theorem tauDensity_square_jacobian {tau : ℝ} (htau : 0 < tau) :
    tauDensity tau = |2 * tau| * energyDensity (tau ^ 2) := by
  rw [energyDensity, Real.sqrt_sq_eq_abs, abs_of_pos htau,
    abs_of_pos (mul_pos (by norm_num) htau)]
  unfold tauDensity
  ring

/-- Native raw KL measure in the actual energy coordinate lambda=tau^2. -/
theorem map_square_tauMeasure :
    Measure.map (fun tau : ℝ => tau ^ 2) tauMeasure = energyMeasure := by
  apply map_positiveDensityMeasure_of_jacobian
    (fun tau : ℝ => tau ^ 2) (fun tau => 2 * tau)
    tauDensity energyDensity (by fun_prop)
    measurable_tauDensity measurable_energyDensity
  · intro tau htau
    convert ((hasDerivAt_id tau).pow 2).hasDerivWithinAt using 1 <;> simp
  · exact square_inj_positive
  · exact square_image_positive
  · intro tau htau
    exact tauDensity_square_jacobian htau

private theorem half_image_positive :
    (fun x : ℝ => x / 2) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hx (by norm_num)
  · intro ht
    refine ⟨2 * t, mul_pos (by norm_num) ht, ?_⟩
    ring

/-- The second Jacobian contributes another factor 2, giving 8/pi^2. -/
theorem tauDensity_half_jacobian (tau : ℝ) :
    tauDensity tau = |(1 : ℝ) / 2| * halfOrderDensity (tau / 2) := by
  have harg : 2 * Real.pi * (tau / 2) = Real.pi * tau := by ring
  simp only [halfOrderDensity, harg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  unfold tauDensity
  ring

/-- Native raw KL measure in the half-order coordinate t=tau/2. -/
theorem map_half_tauMeasure :
    Measure.map (fun tau : ℝ => tau / 2) tauMeasure = halfOrderMeasure := by
  apply map_positiveDensityMeasure_of_jacobian
    (fun tau : ℝ => tau / 2) (fun _ => (1 : ℝ) / 2)
    tauDensity halfOrderDensity (by fun_prop)
    measurable_tauDensity measurable_halfOrderDensity
  · intro tau htau
    simpa using ((hasDerivAt_id tau).div_const 2).hasDerivWithinAt
  · intro x hx y hy hxy
    linarith
  · exact half_image_positive
  · intro tau htau
    exact tauDensity_half_jacobian tau

private theorem ae_tauMeasure_positive : ∀ᵐ tau ∂tauMeasure, 0 < tau := by
  exact (ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- Inverse energy coordinate, proved from the genuine forward map. -/
theorem map_sqrt_energyMeasure :
    Measure.map Real.sqrt energyMeasure = tauMeasure := by
  rw [← map_square_tauMeasure,
    Measure.map_map Real.continuous_sqrt.measurable (by fun_prop)]
  calc
    Measure.map (Real.sqrt ∘ fun tau : ℝ => tau ^ 2) tauMeasure =
        Measure.map id tauMeasure := by
      apply Measure.map_congr
      filter_upwards [ae_tauMeasure_positive] with tau htau
      simp [Function.comp_apply, Real.sqrt_sq_eq_abs, abs_of_pos htau]
    _ = tauMeasure := Measure.map_id

/-- Inverse half-order coordinate. -/
theorem map_double_halfOrderMeasure :
    Measure.map (fun t : ℝ => 2 * t) halfOrderMeasure = tauMeasure := by
  rw [← map_half_tauMeasure,
    Measure.map_map (by fun_prop) (by fun_prop)]
  have hcomp : (fun t : ℝ => 2 * t) ∘ (fun tau : ℝ => tau / 2) = id := by
    funext tau
    dsimp
    ring
  rw [hcomp, Measure.map_id]

/-- The two forward maps are measure preserving between the literal measures. -/
theorem square_measurePreserving :
    MeasurePreserving (fun tau : ℝ => tau ^ 2) tauMeasure energyMeasure :=
  ⟨by fun_prop, map_square_tauMeasure⟩

theorem half_measurePreserving :
    MeasurePreserving (fun tau : ℝ => tau / 2) tauMeasure halfOrderMeasure :=
  ⟨by fun_prop, map_half_tauMeasure⟩

/-- Extended nonnegative test functions require no integrability premise. -/
theorem lintegral_energyMeasure (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ lam, g lam ∂energyMeasure) = ∫⁻ tau, g (tau ^ 2) ∂tauMeasure := by
  rw [← map_square_tauMeasure, lintegral_map hg (by fun_prop)]

theorem lintegral_halfOrderMeasure (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ t, g t ∂halfOrderMeasure) = ∫⁻ tau, g (tau / 2) ∂tauMeasure := by
  rw [← map_half_tauMeasure, lintegral_map hg (by fun_prop)]

/-- This is the useful direction when a Stone density is given in lambda. -/
theorem lintegral_tauMeasure (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ tau, g tau ∂tauMeasure) = ∫⁻ lam, g (Real.sqrt lam) ∂energyMeasure := by
  rw [← map_sqrt_energyMeasure, lintegral_map hg Real.continuous_sqrt.measurable]

/-- Real-valued Stone test functions in the energy coordinate. -/
theorem integral_energyMeasure (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ lam, g lam ∂energyMeasure) = ∫ tau, g (tau ^ 2) ∂tauMeasure := by
  rw [← map_square_tauMeasure]
  exact integral_map_of_stronglyMeasurable (by fun_prop) hg

theorem integral_halfOrderMeasure (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ t, g t ∂halfOrderMeasure) = ∫ tau, g (tau / 2) ∂tauMeasure := by
  rw [← map_half_tauMeasure]
  exact integral_map_of_stronglyMeasurable (by fun_prop) hg

/-- For the usual squared transform test, the Stone variable is sqrt(lambda). -/
theorem integral_tauMeasure (g : ℝ → ℝ) (hg : StronglyMeasurable g) :
    (∫ tau, g tau ∂tauMeasure) = ∫ lam, g (Real.sqrt lam) ∂energyMeasure := by
  rw [← map_sqrt_energyMeasure]
  exact integral_map_of_stronglyMeasurable Real.continuous_sqrt.measurable hg
end
end ImbalancedChen.Part3.ActualKLCoordinateMeasures20261025a
