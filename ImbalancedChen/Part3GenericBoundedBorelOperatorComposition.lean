import ImbalancedChen.Part3GenericBoundedBorelScalarTransport
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
A genuine continuous-composition theorem for A=φ(R), with bounded real Borel φ.
Both sides are constructed continuous real algebra homomorphisms on a common
compact interval, then native Stone--Weierstrass uniqueness applies. No spectral
map from pointwise φ-values into spectrum(A) is assumed or constructed. -/
namespace ImbalancedChen.Part3.GenericBoundedBorelOperatorComposition20261025a
noncomputable section
open MeasureTheory
open ImbalancedChen.Part3.GenericResolventScalarMeasure20261025a
open ImbalancedChen.Part3.GenericBoundedBorelCalculus20261025a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (R : H →L[ℂ] H) (hSA : IsSelfAdjoint R)

abbrev coefficientInterval (φ : BoundedBorelFunction (ResolventSpectrum R)) : Set ℝ :=
  Set.Icc (-φ.bound) φ.bound

def coefficientInInterval (φ : BoundedBorelFunction (ResolventSpectrum R))
    (t : ResolventSpectrum R) : coefficientInterval R φ :=
  ⟨(φ t).re, abs_le.mp ((Complex.abs_re_le_norm (φ t)).trans (φ.norm_le_bound t))⟩

theorem coefficientInInterval_measurable (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    Measurable (coefficientInInterval R φ) :=
  φ.measurable_toFun.re.subtype_mk _

theorem coefficient_eq_real (φ : BoundedBorelFunction (ResolventSpectrum R))
    (hreal : ∀ t, star (φ t) = φ t) (t : ResolventSpectrum R) :
    (((φ t).re : ℝ) : ℂ) = φ t := by
  have hi := congrArg Complex.im (hreal t)
  simp only [Complex.star_def, Complex.conj_im] at hi
  have hz : (φ t).im = 0 := by linarith
  apply Complex.ext <;> simp [hz]

/-- Pointwise Borel composition with a continuous real function on the
common interval, with the actual sup norm as uniform bound. -/
def continuousAfterBorel (φ : BoundedBorelFunction (ResolventSpectrum R))
    (g : C(coefficientInterval R φ, ℝ)) : BoundedBorelFunction (ResolventSpectrum R) where
  toFun := fun t => (g (coefficientInInterval R φ t) : ℂ)
  measurable_toFun := Complex.measurable_ofReal.comp
    (g.continuous.measurable.comp (coefficientInInterval_measurable R φ))
  bound := ‖g‖
  bound_nonneg := norm_nonneg g
  norm_le_bound := fun t => by
    rw [Complex.norm_real]
    exact g.norm_coe_le_norm _

/-- Actual Borel calculus applied after a continuous real test. -/
def intervalEvaluation (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    C(coefficientInterval R φ, ℝ) →ₐ[ℝ] (H →L[ℂ] H) where
  toFun := fun g => borelFunctionalCalculus R hSA (continuousAfterBorel R φ g)
  map_zero' := by
    trans borelFunctionalCalculus R hSA (BoundedBorelFunction.const 0)
    · apply borelFunctionalCalculus_congr
      intro t
      rfl
    · rw [borelFunctionalCalculus_const]
      simp
  map_one' := by
    trans borelFunctionalCalculus R hSA (BoundedBorelFunction.const 1)
    · apply borelFunctionalCalculus_congr
      intro t
      rfl
    · rw [borelFunctionalCalculus_const, one_smul]
      rfl
  map_add' f g := by
    rw [← borelFunctionalCalculus_add]
    apply borelFunctionalCalculus_congr
    intro t
    change ((f _ + g _ : ℝ) : ℂ) = (f _ : ℂ) + (g _ : ℂ)
    exact Complex.ofReal_add _ _
  map_mul' f g := by
    change borelFunctionalCalculus R hSA (continuousAfterBorel R φ (f * g)) =
      (borelFunctionalCalculus R hSA (continuousAfterBorel R φ f)).comp
        (borelFunctionalCalculus R hSA (continuousAfterBorel R φ g))
    rw [← borelFunctionalCalculus_mul]
    apply borelFunctionalCalculus_congr
    intro t
    change ((f _ * g _ : ℝ) : ℂ) = (f _ : ℂ) * (g _ : ℂ)
    exact Complex.ofReal_mul _ _
  commutes' r := by
    trans borelFunctionalCalculus R hSA (BoundedBorelFunction.const (r : ℂ))
    · apply borelFunctionalCalculus_congr
      intro t
      rfl
    · rw [borelFunctionalCalculus_const, Algebra.algebraMap_eq_smul_one]
      simpa using (algebraMap_smul ℂ r (1 : H →L[ℂ] H))

theorem intervalEvaluation_norm_le (φ : BoundedBorelFunction (ResolventSpectrum R))
    (g : C(coefficientInterval R φ, ℝ)) : ‖intervalEvaluation R hSA φ g‖ ≤ ‖g‖ :=
  borelFunctionalCalculus_opNorm_le R hSA (continuousAfterBorel R φ g)

theorem intervalEvaluation_continuous (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    Continuous (intervalEvaluation R hSA φ) := by
  let T := (intervalEvaluation R hSA φ).toLinearMap.mkContinuous 1
    (fun g => by simpa only [one_mul] using intervalEvaluation_norm_le R hSA φ g)
  exact T.continuous

theorem transformed_spectrum_subset_interval (φ : BoundedBorelFunction (ResolventSpectrum R)) :
    spectrum ℝ (borelFunctionalCalculus R hSA φ) ⊆ coefficientInterval R φ := by
  intro t ht
  have hn : ‖t‖ ≤ φ.bound := calc
    ‖t‖ ≤ ‖borelFunctionalCalculus R hSA φ‖ * ‖(1 : H →L[ℂ] H)‖ :=
      spectrum.norm_le_norm_mul_of_mem ht
    _ ≤ ‖borelFunctionalCalculus R hSA φ‖ * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
    _ ≤ φ.bound := by simpa only [mul_one] using borelFunctionalCalculus_opNorm_le R hSA φ
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hn)

/-- All continuous tests are justified by algebra-hom continuity and the
pinned polynomial-density uniqueness theorem, not by bare coordinate equality. -/
theorem intervalEvaluation_eq_cfcHomSuperset
    (φ : BoundedBorelFunction (ResolventSpectrum R))
    (hreal : ∀ t, star (φ t) = φ t) :
    intervalEvaluation R hSA φ =
      (cfcHomSuperset (borelFunctionalCalculus_selfAdjoint R hSA φ hreal)
        (transformed_spectrum_subset_interval R hSA φ)).toAlgHom := by
  apply ContinuousMap.algHom_ext_map_X
    (intervalEvaluation_continuous R hSA φ)
    (cfcHomSuperset_continuous (borelFunctionalCalculus_selfAdjoint R hSA φ hreal)
      (transformed_spectrum_subset_interval R hSA φ))
  simp only [Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_X_eq_restrict_id]
  rw [cfcHomSuperset_id]
  apply borelFunctionalCalculus_congr
  intro t
  exact coefficient_eq_real R φ hreal t

theorem continuous_borel_composition
    (φ : BoundedBorelFunction (ResolventSpectrum R))
    (hreal : ∀ t, star (φ t) = φ t) (g : C(coefficientInterval R φ, ℝ)) :
    borelFunctionalCalculus R hSA (continuousAfterBorel R φ g) =
      cfcHomSuperset (borelFunctionalCalculus_selfAdjoint R hSA φ hreal)
        (transformed_spectrum_subset_interval R hSA φ) g :=
  congrArg (fun T : C(coefficientInterval R φ, ℝ) →ₐ[ℝ] (H →L[ℂ] H) => T g)
    (intervalEvaluation_eq_cfcHomSuperset R hSA φ hreal)

end
end ImbalancedChen.Part3.GenericBoundedBorelOperatorComposition20261025a