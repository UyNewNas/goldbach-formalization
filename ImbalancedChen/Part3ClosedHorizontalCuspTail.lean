import ImbalancedChen.Part3CuspZeroMeanEnergyOnlyTail
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Order

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The sharp smooth period-one estimate already exists. This module proves its
stability on the actual closed horizontal derivative graph, with two different
physical measures: Haar times dy/y² for the function and Haar times dy for its
physical horizontal derivative. The tail restriction is the native continuous
map between Lp quotients for ordered measures. No tail estimate, compactness,
weak derivative identification, or spectral theorem is an input.

For width w the normalized coordinate is t=x/w; the derivative of the lifted
function is w D. Multiplying both physical measures by w would cancel the same
factor on both sides. The conclusion is w²/(4π²Y²), not a whole-H spectral gap.
-/

noncomputable section

namespace ImbalancedChen.Part3.ClosedHorizontalCuspTail20261026a

open Set MeasureTheory
open ImbalancedChen.Part3.CuspCylinderMeasure20261024z
open ImbalancedChen.Part3.CuspZeroMeanEnergyOnlyTail20261025a

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

def rawCylinderMeasure : Measure CuspCylinder :=
  (AddCircle.haarAddCircle (T := (1 : ℝ))).prod (volume : Measure PositiveHeight)

def functionMeasure (a : ℝ) : Measure CuspCylinder :=
  cylinderMeasure.restrict (strictCylinderTail a)

def derivativeMeasure (a : ℝ) : Measure CuspCylinder :=
  rawCylinderMeasure.restrict (strictCylinderTail a)

abbrev FunctionL2 (a : ℝ) := Lp ℂ 2 (functionMeasure a)
abbrev DerivativeL2 (a : ℝ) := Lp ℂ 2 (derivativeMeasure a)

theorem tail_subset {a Y : ℝ} (haY : a ≤ Y) :
    strictCylinderTail Y ⊆ strictCylinderTail a := by
  intro z hz
  exact ⟨hz.1, lt_of_le_of_lt haY hz.2⟩

theorem functionMeasure_mono {a Y : ℝ} (haY : a ≤ Y) :
    functionMeasure Y ≤ functionMeasure a :=
  Measure.restrict_mono (tail_subset haY) le_rfl

theorem derivativeMeasure_mono {a Y : ℝ} (haY : a ≤ Y) :
    derivativeMeasure Y ≤ derivativeMeasure a :=
  Measure.restrict_mono (tail_subset haY) le_rfl

/-- The horizontal boundary at a positive height has zero hyperbolic measure. -/
theorem horizontal_boundary_null (Y : ℝ) (hY : 0 < Y) :
    cylinderMeasure {z : CuspCylinder | (z.2 : ℝ) = Y} = 0 := by
  have heq : {z : CuspCylinder | (z.2 : ℝ) = Y} =
      Set.univ ×ˢ ({⟨Y, hY⟩} : Set PositiveHeight) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, Set.mem_singleton_iff,
      true_and, Subtype.ext_iff]
  rw [heq, cylinderMeasure, Measure.prod_prod]
  have hz : heightMeasure ({⟨Y, hY⟩} : Set PositiveHeight) = 0 := by
    letI : NullSingletonClass (volume : Measure PositiveHeight) := ⟨fun y => by
      rw [Measure.Subtype.volume_def,
        (MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
      simp only [Set.image_singleton, measure_singleton]⟩
    unfold heightMeasure
    exact measure_singleton _
  rw [hz, mul_zero]

/-- In particular the theorem below also uses exactly the measure on y ≥ Y. -/
theorem functionMeasure_eq_closed_tail (Y : ℝ) (hY : 0 < Y) :
    functionMeasure Y = cylinderMeasure.restrict {z : CuspCylinder | Y ≤ (z.2 : ℝ)} := by
  apply Measure.restrict_congr_set
  have hne : ∀ᵐ z : CuspCylinder ∂cylinderMeasure, (z.2 : ℝ) ≠ Y := by
    rw [ae_iff]
    simpa using horizontal_boundary_null Y hY
  filter_upwards [hne] with z hz
  change (z ∈ Set.univ ×ˢ strictHeightTail Y) = (Y ≤ (z.2 : ℝ))
  simp only [Set.mem_prod, Set.mem_univ, true_and, strictHeightTail, Set.mem_setOf_eq]
  apply propext
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h hz.symm⟩

/-- Restriction of an actual L² class to a higher cusp tail. -/
def tailRestriction (a Y : ℝ) (haY : a ≤ Y) :
    FunctionL2 a →L[ℝ] FunctionL2 Y :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using functionMeasure_mono haY)

theorem tailRestriction_ae (a Y : ℝ) (haY : a ≤ Y) (u : FunctionL2 a) :
    tailRestriction a Y haY u =ᵐ[functionMeasure Y] u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ u

private theorem norm_sq_integral {μ : Measure CuspCylinder} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [integral_ofReal] at h
  exact Complex.ofReal_injective h

private theorem norm_toLp_sq {μ : Measure CuspCylinder}
    (F : CuspCylinder → ℂ) (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ ^ 2 = ∫ z, ‖F z‖ ^ 2 ∂μ := by
  rw [norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp] with z hz
  rw [hz]

/-- Genuine classical zero-mean periodic derivatives, before taking closure.
`D` is the physical derivative; no coercivity estimate is stored here. -/
structure ClassicalPair (w a : ℝ) where
  function : CuspCylinder → ℂ
  derivative : CuspCylinder → ℂ
  continuous_function : Continuous function
  continuous_derivative : Continuous derivative
  hasDeriv : ∀ y : PositiveHeight, a < (y : ℝ) → ∀ t : ℝ,
    HasDerivAt (fun s : ℝ => function ((s : UnitAddCircle), y))
      ((w : ℂ) * derivative ((t : UnitAddCircle), y)) t
  mean_zero : ∀ y : PositiveHeight, a < (y : ℝ) →
    (∫ x : UnitAddCircle, function (x, y) ∂AddCircle.haarAddCircle) = 0
  function_memLp : MemLp function 2 (functionMeasure a)
  derivative_memLp : MemLp derivative 2 (derivativeMeasure a)

def ClassicalPair.coordinates {w a : ℝ} (P : ClassicalPair w a) :
    FunctionL2 a × DerivativeL2 a :=
  (P.function_memLp.toLp P.function, P.derivative_memLp.toLp P.derivative)

def classicalHorizontalGraph (w a : ℝ) : Set (FunctionL2 a × DerivativeL2 a) :=
  Set.range (ClassicalPair.coordinates (w := w) (a := a))

/-- Closure in the two physical L² spaces, not a postulated weak graph. -/
def closedHorizontalGraph (w a : ℝ) : Set (FunctionL2 a × DerivativeL2 a) :=
  closure (classicalHorizontalGraph w a)

theorem classical_tail_bound {w a Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (haY : a ≤ Y) (P : ClassicalPair w a) :
    ‖tailRestriction a Y haY P.coordinates.1‖ ^ 2 ≤
      (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * ‖P.coordinates.2‖ ^ 2 := by
  have hD := P.derivative_memLp.mono_measure (derivativeMeasure_mono haY)
  have hwD := hD.const_smul (w : ℂ)
  have hwDint : Integrable (fun z => ‖(w : ℂ) * P.derivative z‖ ^ 2)
      (derivativeMeasure Y) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using
      (memLp_two_iff_integrable_sq_norm hwD.aestronglyMeasurable).mp hwD
  have hbound := strict_cusp_tail_mass_of_horizontal_energy Y hY
    P.function (fun z => (w : ℂ) * P.derivative z)
    P.continuous_function (continuous_const.mul P.continuous_derivative)
    (fun y hy t _ => P.hasDeriv y (lt_of_le_of_lt haY hy) t)
    (fun y hy => P.mean_zero y (lt_of_le_of_lt haY hy)) hwDint
  have hnorm (z : CuspCylinder) :
      ‖(w : ℂ) * P.derivative z‖ ^ 2 = w ^ 2 * ‖P.derivative z‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw]
    ring
  simp_rw [hnorm] at hbound
  rw [integral_const_mul] at hbound
  have hDint := (memLp_two_iff_integrable_sq_norm
    P.derivative_memLp.aestronglyMeasurable).mp P.derivative_memLp
  have hDle : (∫ z, ‖P.derivative z‖ ^ 2 ∂derivativeMeasure Y) ≤
      ∫ z, ‖P.derivative z‖ ^ 2 ∂derivativeMeasure a :=
    integral_mono_measure (derivativeMeasure_mono haY)
      (Filter.Eventually.of_forall fun z => sq_nonneg _) hDint
  have hFae : tailRestriction a Y haY P.coordinates.1 =ᵐ[functionMeasure Y]
      P.function := by
    refine (tailRestriction_ae a Y haY P.coordinates.1).trans ?_
    exact (Measure.absolutelyContinuous_of_le (functionMeasure_mono haY)).ae_eq
      P.function_memLp.coeFn_toLp
  have hFnorm : ‖tailRestriction a Y haY P.coordinates.1‖ ^ 2 =
      ∫ z, ‖P.function z‖ ^ 2 ∂functionMeasure Y := by
    rw [norm_sq_integral]
    exact integral_congr_ae (hFae.fun_comp fun x : ℂ => ‖x‖ ^ 2)
  rw [hFnorm, show ‖P.coordinates.2‖ ^ 2 =
    ∫ z, ‖P.derivative z‖ ^ 2 ∂derivativeMeasure a from
      norm_toLp_sq P.derivative P.derivative_memLp]
  calc
    _ ≤ (4 * Real.pi ^ 2 * Y ^ 2)⁻¹ *
        (w ^ 2 * ∫ z, ‖P.derivative z‖ ^ 2 ∂derivativeMeasure Y) := hbound.2
    _ = (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) *
        (∫ z, ‖P.derivative z‖ ^ 2 ∂derivativeMeasure Y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hDle (by positivity)

/-- The sharp cusp-tail estimate survives actual graph closure. -/
theorem closed_horizontal_tail_bound {w a Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (haY : a ≤ Y) {u : FunctionL2 a} {d : DerivativeL2 a}
    (h : (u, d) ∈ closedHorizontalGraph w a) :
    ‖tailRestriction a Y haY u‖ ^ 2 ≤
      (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * ‖d‖ ^ 2 := by
  let S : Set (FunctionL2 a × DerivativeL2 a) :=
    {p | ‖tailRestriction a Y haY p.1‖ ^ 2 ≤
      (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) * ‖p.2‖ ^ 2}
  have hS : IsClosed S := isClosed_le
    (((tailRestriction a Y haY).continuous.comp continuous_fst).norm.pow 2)
    (continuous_const.mul (continuous_snd.norm.pow 2))
  have hin : classicalHorizontalGraph w a ⊆ S := by
    rintro _ ⟨P, rfl⟩
    exact classical_tail_bound hw hY haY P
  exact closure_minimal hin hS h

/-- The same closed-graph estimate in literal integral notation, including
the horizontal boundary y=Y. Representatives are harmless by the actual
absolute-continuity restriction map. -/
theorem closed_horizontal_tail_integral {w a Y : ℝ} (hw : 0 < w) (hY : 0 < Y)
    (haY : a ≤ Y) {u : FunctionL2 a} {d : DerivativeL2 a}
    (h : (u, d) ∈ closedHorizontalGraph w a) :
    (∫ z in {z : CuspCylinder | Y ≤ (z.2 : ℝ)}, ‖u z‖ ^ 2 ∂cylinderMeasure) ≤
      (w ^ 2 / (4 * Real.pi ^ 2 * Y ^ 2)) *
        (∫ z in strictCylinderTail a, ‖d z‖ ^ 2 ∂rawCylinderMeasure) := by
  have hbound := closed_horizontal_tail_bound hw hY haY h
  have hnorm : ‖tailRestriction a Y haY u‖ ^ 2 =
      ∫ z, ‖u z‖ ^ 2 ∂functionMeasure Y := by
    rw [norm_sq_integral]
    exact integral_congr_ae ((tailRestriction_ae a Y haY u).fun_comp
      fun x : ℂ => ‖x‖ ^ 2)
  rw [hnorm, norm_sq_integral, functionMeasure_eq_closed_tail Y hY] at hbound
  exact hbound

end ImbalancedChen.Part3.ClosedHorizontalCuspTail20261026a
