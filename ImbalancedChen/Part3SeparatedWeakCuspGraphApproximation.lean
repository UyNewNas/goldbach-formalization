import ImbalancedChen.Part3CircleWeakDerivativeGraphApproximation
import ImbalancedChen.Part3ClosedHorizontalCuspTail
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A concrete cylinder weak-to-classical graph inclusion for separated height
profiles. The horizontal pair is distributional, not assumed classical.
Its Fourier approximants are multiplied by the SAME continuous height
profile. Actual product integrals give convergence in dy/y^2 for values
and dy for horizontal derivatives, hence membership in the previously
constructed classical graph closure and its sharp cusp-tail estimate.

This includes every compact smooth height profile satisfying the two
explicit MemLp conditions. The result is not yet density for arbitrary
height-dependent weak pairs; finite/general height coefficient density and
distributional slicing remain separate obligations.
-/

noncomputable section
namespace ImbalancedChen.Part3.SeparatedWeakCuspGraphApproximation20261026a

open Set MeasureTheory Filter
open scoped Topology
open CuspCylinderMeasure20261024z CuspZeroMeanEnergyOnlyTail20261025a
open CuspZeroMeanSmoothApproximationSourceOnly
open CircleWeakDerivativeGraphApproximation20261026a
open ClosedHorizontalCuspTail20261026a

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
attribute [local instance] Measure.Subtype.measureSpace

local instance positiveHeight_locallyCompact : LocallyCompactSpace PositiveHeight :=
  isOpen_Ioi.locallyCompactSpace

local instance positiveHeightVolume_finiteOnCompacts :
    IsFiniteMeasureOnCompacts (volume : Measure PositiveHeight) :=
  IsFiniteMeasureOnCompacts.comap' volume continuous_subtype_val
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi)

local instance positiveHeightVolume_locallyFinite :
    IsLocallyFiniteMeasure (volume : Measure PositiveHeight) := inferInstance

local instance positiveHeightVolume_sigmaFinite :
    SigmaFinite (volume : Measure PositiveHeight) := inferInstance

private theorem norm_sq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (u : Lp ℂ 2 μ) :
    ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  have h := L2.inner_def (𝕜 := ℂ) u u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  rw [integral_ofReal] at h
  exact Complex.ofReal_injective h

section Product
variable (μ : Measure PositiveHeight) [SFinite μ]
variable (μC : Measure CuspCylinder)
variable (hμ : μC = (AddCircle.haarAddCircle (T := (1:ℝ))).prod μ)

def tensorFunction (u : CircleL2) (v : Lp ℂ 2 μ) (z : CuspCylinder) : ℂ :=
  u z.1 * v z.2

theorem tensorFunction_memLp (u : CircleL2) (v : Lp ℂ 2 μ) :
    MemLp (tensorFunction μ u v) 2 μC := by
  rw [hμ]
  have hu := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp
    (Lp.memLp u)
  have hv := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp
    (Lp.memLp v)
  apply (memLp_two_iff_integrable_sq_norm
    ((Lp.aestronglyMeasurable u).comp_fst.mul
      (Lp.aestronglyMeasurable v).comp_snd)).mpr
  simpa only [tensorFunction, norm_mul, mul_pow] using hu.mul_prod hv

def tensorVector (u : CircleL2) (v : Lp ℂ 2 μ) : Lp ℂ 2 μC :=
  (tensorFunction_memLp μ μC hμ u v).toLp (tensorFunction μ u v)

theorem tensorVector_ae (u : CircleL2) (v : Lp ℂ 2 μ) :
    (tensorVector μ μC hμ u v : CuspCylinder → ℂ) =ᵐ[μC]
      tensorFunction μ u v := (tensorFunction_memLp μ μC hμ u v).coeFn_toLp

/-- Exact product norm, including the true height-measure normalization. -/
theorem tensorVector_norm (u : CircleL2) (v : Lp ℂ 2 μ) :
    ‖tensorVector μ μC hμ u v‖ = ‖u‖ * ‖v‖ := by
  have heq : ‖tensorVector μ μC hμ u v‖^2 = ‖u‖^2 * ‖v‖^2 := by
    rw [norm_sq_integral]
    calc
      _ = ∫ z : CuspCylinder, ‖u z.1‖^2 * ‖v z.2‖^2 ∂μC := by
        apply integral_congr_ae
        filter_upwards [tensorVector_ae μ μC hμ u v] with z hz
        rw [hz, tensorFunction, norm_mul, mul_pow]
      _ = _ := by rw [hμ, integral_prod_mul, ← norm_sq_integral, ← norm_sq_integral]
  nlinarith [norm_nonneg (tensorVector μ μC hμ u v),
    mul_nonneg (norm_nonneg u) (norm_nonneg v)]

theorem tensorVector_add (u₁ u₂ : CircleL2) (v : Lp ℂ 2 μ) :
    tensorVector μ μC hμ (u₁+u₂) v =
      tensorVector μ μC hμ u₁ v + tensorVector μ μC hμ u₂ v := by
  apply Lp.ext
  have hs : ∀ᵐ z : CuspCylinder ∂μC, (u₁+u₂) z.1 = u₁ z.1+u₂ z.1 := by
    rw [hμ]
    exact (quasiMeasurePreserving_fst (μ := AddCircle.haarAddCircle) (ν := μ)).ae
      (Lp.coeFn_add u₁ u₂)
  filter_upwards [tensorVector_ae μ μC hμ (u₁+u₂) v,
    tensorVector_ae μ μC hμ u₁ v, tensorVector_ae μ μC hμ u₂ v,
    Lp.coeFn_add (tensorVector μ μC hμ u₁ v) (tensorVector μ μC hμ u₂ v), hs]
    with z h₁ h₂ h₃ h₄ h₅
  simp only [Pi.add_apply] at h₄
  rw [h₁, h₄, h₂, h₃]
  simp only [tensorFunction, h₅, add_mul]

theorem tensorVector_smul (c : ℂ) (u : CircleL2) (v : Lp ℂ 2 μ) :
    tensorVector μ μC hμ (c • u) v = c • tensorVector μ μC hμ u v := by
  apply Lp.ext
  have hs : ∀ᵐ z : CuspCylinder ∂μC, (c • u) z.1 = c • u z.1 := by
    rw [hμ]
    exact (quasiMeasurePreserving_fst (μ := AddCircle.haarAddCircle) (ν := μ)).ae
      (Lp.coeFn_smul c u)
  filter_upwards [tensorVector_ae μ μC hμ (c • u) v,
    tensorVector_ae μ μC hμ u v,
    Lp.coeFn_smul c (tensorVector μ μC hμ u v), hs] with z h₁ h₂ h₃ h₄
  simp only [Pi.smul_apply] at h₃
  rw [h₁, h₃, h₂]
  simp only [tensorFunction, h₄, smul_eq_mul, mul_assoc]

def circleHeightTensor (v : Lp ℂ 2 μ) : CircleL2 →L[ℂ] Lp ℂ 2 μC :=
  LinearMap.mkContinuous
    { toFun := fun u => tensorVector μ μC hμ u v
      map_add' := fun u₁ u₂ => tensorVector_add μ μC hμ u₁ u₂ v
      map_smul' := fun c u => tensorVector_smul μ μC hμ c u v }
    ‖v‖ (fun u => by rw [tensorVector_norm]; exact le_of_eq (mul_comm _ _))

end Product

def functionHeightMeasure (a : ℝ) := heightMeasure.restrict (strictHeightTail a)
def derivativeHeightMeasure (a : ℝ) :=
  (volume : Measure PositiveHeight).restrict (strictHeightTail a)

theorem functionMeasure_product (a : ℝ) :
    functionMeasure a = AddCircle.haarAddCircle.prod (functionHeightMeasure a) := by
  simpa only [functionMeasure, functionHeightMeasure, cylinderMeasure,
    strictCylinderTail, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := AddCircle.haarAddCircle)
      (ν := heightMeasure) Set.univ (strictHeightTail a)).symm

theorem derivativeMeasure_product (a : ℝ) :
    derivativeMeasure a = AddCircle.haarAddCircle.prod (derivativeHeightMeasure a) := by
  simpa only [derivativeMeasure, derivativeHeightMeasure, rawCylinderMeasure,
    strictCylinderTail, Measure.restrict_univ] using
    (Measure.prod_restrict (μ := AddCircle.haarAddCircle)
      (ν := (volume : Measure PositiveHeight)) Set.univ (strictHeightTail a)).symm

/-- A concrete height profile with precisely the two physical L2 conditions.
Continuity is sufficient for the existing classical graph; no derivative in
height or assumed horizontal graph membership is stored here. -/
structure HeightProfile (a : ℝ) where
  function : PositiveHeight → ℂ
  continuous : Continuous function
  weighted_memLp : MemLp function 2 (functionHeightMeasure a)
  raw_memLp : MemLp function 2 (derivativeHeightMeasure a)

/-- Compact support in the actual positive-height space supplies both
physical L2 conditions; they are not extra inputs for a compact profile. -/
def HeightProfile.ofCompact (a : ℝ) (η : PositiveHeight → ℂ)
    (hc : Continuous η) (hk : HasCompactSupport η) : HeightProfile a where
  function := η
  continuous := hc
  weighted_memLp := by
    have h : MemLp η 2 heightMeasure := hc.memLp_of_hasCompactSupport hk
    exact h.mono_measure Measure.restrict_le_self
  raw_memLp := by
    have h : MemLp η 2 (volume : Measure PositiveHeight) := hc.memLp_of_hasCompactSupport hk
    exact h.mono_measure Measure.restrict_le_self

def liftValue {a : ℝ} (η : HeightProfile a) : CircleL2 →L[ℂ] FunctionL2 a :=
  circleHeightTensor (functionHeightMeasure a) (functionMeasure a)
    (functionMeasure_product a) (η.weighted_memLp.toLp η.function)

def liftDerivative {a : ℝ} (η : HeightProfile a) : CircleL2 →L[ℂ] DerivativeL2 a :=
  circleHeightTensor (derivativeHeightMeasure a) (derivativeMeasure a)
    (derivativeMeasure_product a) (η.raw_memLp.toLp η.function)

theorem liftValue_ae {a : ℝ} (η : HeightProfile a) (u : CircleL2) :
    (liftValue η u : CuspCylinder → ℂ) =ᵐ[functionMeasure a]
      (fun z => u z.1 * η.function z.2) := by
  have he : ∀ᵐ z : CuspCylinder ∂functionMeasure a,
      η.weighted_memLp.toLp η.function z.2 = η.function z.2 := by
    rw [functionMeasure_product]
    exact (quasiMeasurePreserving_snd).ae η.weighted_memLp.coeFn_toLp
  filter_upwards [tensorVector_ae (functionHeightMeasure a) (functionMeasure a)
    (functionMeasure_product a) u (η.weighted_memLp.toLp η.function), he] with z hz hez
  simpa only [tensorFunction, hez] using hz

theorem liftDerivative_ae {a : ℝ} (η : HeightProfile a) (u : CircleL2) :
    (liftDerivative η u : CuspCylinder → ℂ) =ᵐ[derivativeMeasure a]
      (fun z => u z.1 * η.function z.2) := by
  have he : ∀ᵐ z : CuspCylinder ∂derivativeMeasure a,
      η.raw_memLp.toLp η.function z.2 = η.function z.2 := by
    rw [derivativeMeasure_product]
    exact (quasiMeasurePreserving_snd).ae η.raw_memLp.coeFn_toLp
  filter_upwards [tensorVector_ae (derivativeHeightMeasure a) (derivativeMeasure a)
    (derivativeMeasure_product a) u (η.raw_memLp.toLp η.function), he] with z hz hez
  simpa only [tensorFunction, hez] using hz

private theorem continuous_toLp_ae (φ : C(UnitAddCircle, ℂ)) :
    (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ φ : UnitAddCircle → ℂ)
      =ᵐ[AddCircle.haarAddCircle] φ :=
  ContinuousMap.coeFn_toLp (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) φ

def liftedClassicalPair {a : ℝ} (η : HeightProfile a) (P : ClassicalCirclePair) :
    ClassicalPair 1 a where
  function := fun z => P.function z.1 * η.function z.2
  derivative := fun z => P.derivative z.1 * η.function z.2
  continuous_function := (P.function.continuous.comp continuous_fst).mul
    (η.continuous.comp continuous_snd)
  continuous_derivative := (P.derivative.continuous.comp continuous_fst).mul
    (η.continuous.comp continuous_snd)
  hasDeriv := fun y _ t => by simpa using (P.hasDeriv t).mul_const (η.function y)
  mean_zero := fun y _ => by rw [integral_mul_const, P.mean_zero, zero_mul]
  function_memLp := by
    have he := liftValue_ae η P.coordinates.1
    have hp : ∀ᵐ z : CuspCylinder ∂functionMeasure a,
        P.coordinates.1 z.1 = P.function z.1 := by
      rw [functionMeasure_product]
      exact (quasiMeasurePreserving_fst).ae (continuous_toLp_ae P.function)
    exact (Lp.memLp (liftValue η P.coordinates.1)).congr (he.trans
      (hp.mono fun z hz => by rw [hz]))
  derivative_memLp := by
    have he := liftDerivative_ae η P.coordinates.2
    have hp : ∀ᵐ z : CuspCylinder ∂derivativeMeasure a,
        P.coordinates.2 z.1 = P.derivative z.1 := by
      rw [derivativeMeasure_product]
      exact (quasiMeasurePreserving_fst).ae (continuous_toLp_ae P.derivative)
    exact (Lp.memLp (liftDerivative η P.coordinates.2)).congr (he.trans
      (hp.mono fun z hz => by rw [hz]))

theorem liftedClassicalPair_coordinates {a : ℝ} (η : HeightProfile a)
    (P : ClassicalCirclePair) :
    (liftedClassicalPair η P).coordinates =
      (liftValue η P.coordinates.1, liftDerivative η P.coordinates.2) := by
  apply Prod.ext
  · apply Lp.ext
    have hp : ∀ᵐ z : CuspCylinder ∂functionMeasure a,
        P.coordinates.1 z.1 = P.function z.1 := by
      rw [functionMeasure_product]
      exact (quasiMeasurePreserving_fst).ae (continuous_toLp_ae P.function)
    filter_upwards [(liftedClassicalPair η P).function_memLp.coeFn_toLp,
      liftValue_ae η P.coordinates.1, hp] with z hz hu hpz
    simp only [ClassicalPair.coordinates, liftedClassicalPair] at hz ⊢
    rw [hz, hu, hpz]
  · apply Lp.ext
    have hp : ∀ᵐ z : CuspCylinder ∂derivativeMeasure a,
        P.coordinates.2 z.1 = P.derivative z.1 := by
      rw [derivativeMeasure_product]
      exact (quasiMeasurePreserving_fst).ae (continuous_toLp_ae P.derivative)
    filter_upwards [(liftedClassicalPair η P).derivative_memLp.coeFn_toLp,
      liftDerivative_ae η P.coordinates.2, hp] with z hz hu hpz
    simp only [ClassicalPair.coordinates, liftedClassicalPair] at hz ⊢
    rw [hz, hu, hpz]

/-- A distributional circle pair with an actual height profile belongs to
the closed physical cylinder graph. Both measures are those in 38ac. -/
theorem separated_classical_sequence_tendsto {a : ℝ}
    (η : HeightProfile a) {f g : CircleL2} (hweak : HasWeakCircleDerivative f g)
    (hmean : AddCircle.fourierCoeff f 0 = 0) :
    Tendsto (fun N : ℕ =>
      (liftedClassicalPair η (weakFourierPair hweak N)).coordinates) atTop
      (𝓝 (liftValue η f, liftDerivative η g)) := by
  have hf := (liftValue η).continuous.tendsto f |>.comp
    (window_polynomialL2_tendsto f hmean)
  have hg := (liftDerivative η).continuous.tendsto g |>.comp
    (window_polynomialL2_tendsto g (weak_derivative_zero_coefficient hweak))
  simpa only [liftedClassicalPair_coordinates, weakFourierPair_coordinates] using
    hf.prodMk_nhds hg

theorem separated_weak_pair_mem_closed_horizontal_graph {a : ℝ}
    (η : HeightProfile a) {f g : CircleL2} (hweak : HasWeakCircleDerivative f g)
    (hmean : AddCircle.fourierCoeff f 0 = 0) :
    (liftValue η f, liftDerivative η g) ∈ closedHorizontalGraph 1 a := by
  exact isClosed_closure.mem_of_tendsto
    (separated_classical_sequence_tendsto η hweak hmean) (Eventually.of_forall fun N =>
    subset_closure ⟨liftedClassicalPair η (weakFourierPair hweak N), rfl⟩)

/-- For a smooth real height profile the actual sequence is smooth in
BOTH real coordinates, not merely smooth on each circle slice. -/
theorem separated_polynomial_contDiff (f : CircleL2) (N : ℕ)
    (η : ℝ → ℂ) (hη : ContDiff ℝ ⊤ η) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      polynomial f (window N) (p.1 : UnitAddCircle) * η p.2) := by
  exact ((realLift_contDiff f (window N)).comp contDiff_fst).mul
    (hη.comp contDiff_snd)

/-- The sharp physical weak-pair tail estimate follows from actual closure
membership just proved; it is not an assumption on the weak derivative. -/
theorem separated_weak_cusp_tail {a Y : ℝ} (η : HeightProfile a)
    (hY : 0 < Y) (haY : a ≤ Y) {f g : CircleL2}
    (hweak : HasWeakCircleDerivative f g) (hmean : AddCircle.fourierCoeff f 0 = 0) :
    ‖tailRestriction a Y haY (liftValue η f)‖^2 ≤
      (4 * Real.pi^2 * Y^2)⁻¹ * ‖liftDerivative η g‖^2 := by
  simpa only [one_pow, one_div] using
    closed_horizontal_tail_bound (w := 1) (by norm_num) hY haY
      (separated_weak_pair_mem_closed_horizontal_graph η hweak hmean)

end ImbalancedChen.Part3.SeparatedWeakCuspGraphApproximation20261026a
