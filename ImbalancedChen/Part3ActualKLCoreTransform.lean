import ImbalancedChen.Part3ActualKLCoordinateMeasures
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
The actual compact radial KL transform as a linear map on the physical
L2(dr) core, with values in the literal positive tau density L2 space.
Weighted integrability is proved from the actual compact-test estimate.
Physical representative independence follows from AE equality and actual
continuity of the compact tests. No norm equality, isometry, spectral
measure identification, or extension to all physical L2 is asserted.
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualKLCoreTransform20261025a

noncomputable section
open MeasureTheory Set Filter
open RadialSchrodingerL2Form20261025a
open ActualKLCompactTestIntegrationByParts20261025a
open ActualKLCompactTestWeightedL220261025a ActualKLCoordinateMeasures20261025a

/-- Literal raw KL Hilbert target, with density (2/pi²)tau*sinh(pi*tau)
on tau>0. No automorphic normalization is attached to this space. -/
abbrev RawTauL2 := Lp ℂ 2 tauMeasure

/-- The proved weighted-square estimate gives actual membership in the
L2 space of the native tau measure, rather than a formal transform name. -/
theorem actualKtransform_memLp_tau (T : RadialTest) :
    MemLp (actualKtransform T.function) 2 tauMeasure := by
  apply (memLp_two_iff_integrable_sq_norm
    (actualKtransform_stronglyMeasurable T).aestronglyMeasurable).mpr
  change Integrable (fun tau : ℝ => ‖actualKtransform T.function tau‖ ^ 2)
    (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun tau => ENNReal.ofReal (tauDensity tau)))
  have hw : Measurable (fun tau : ℝ => ENNReal.ofReal (tauDensity tau)) := by
    unfold tauDensity
    fun_prop
  rw [integrable_withDensity_iff_integrable_smul' hw (by simp)]
  apply (actualKtransform_KL_weighted_square_integrable T).congr
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with tau htau
  have hn : 0 ≤ tauDensity tau := actualKLWeight_nonneg htau.le
  change tauDensity tau * ‖actualKtransform T.function tau‖ ^ 2 =
    (ENNReal.ofReal (tauDensity tau)).toReal * ‖actualKtransform T.function tau‖ ^ 2
  rw [ENNReal.toReal_ofReal hn]

/-- The actual compact-test transform, as an L2 vector for raw tauMeasure. -/
def rawKLTestTransform (T : RadialTest) : RawTauL2 :=
  (actualKtransform_memLp_tau T).toLp (actualKtransform T.function)

/-- The chosen L2 representative equals the literal K-integral almost everywhere. -/
theorem rawKLTestTransform_ae (T : RadialTest) :
    (rawKLTestTransform T : ℝ → ℂ) =ᵐ[tauMeasure] actualKtransform T.function :=
  (actualKtransform_memLp_tau T).coeFn_toLp

/-- Explicit core operations avoid imposing new algebraic instances on
the existing RadialTest structure. -/
def testZero : RadialTest where
  function := 0
  smooth := by fun_prop
  compact := by simp

def testAdd (T U : RadialTest) : RadialTest where
  function := T.function + U.function
  smooth := T.smooth.add U.smooth
  compact := T.compact.add U.compact

def testSMul (c : ℂ) (T : RadialTest) : RadialTest where
  function := c • T.function
  smooth := by
    simpa only [Pi.smul_apply] using (contDiff_const.smul T.smooth :
      ContDiff ℝ ∞ (fun r : ℝ => c • T.function r))
  compact := by
    apply HasCompactSupport.intro T.compact.isCompact
    intro r hr
    simp only [Pi.smul_apply, image_eq_zero_of_notMem_tsupport hr, smul_zero]

/-- Actual additivity of the literal integral, with both convergence
hypotheses discharged by the actual compact K-integrand theorem. -/
theorem actualKtransform_testAdd (T U : RadialTest) (tau : ℝ) :
    actualKtransform (testAdd T U).function tau =
      actualKtransform T.function tau + actualKtransform U.function tau := by
  simp only [actualKtransform, testAdd, Pi.add_apply, add_mul]
  exact integral_add
    (actualKtransform_integrable T.function T.smooth.continuous T.compact tau)
    (actualKtransform_integrable U.function U.smooth.continuous U.compact tau)

/-- Actual complex scalar linearity of the same integral. -/
theorem actualKtransform_testSMul (c : ℂ) (T : RadialTest) (tau : ℝ) :
    actualKtransform (testSMul c T).function tau =
      c • actualKtransform T.function tau := by
  simp only [actualKtransform, testSMul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun r => by ring

theorem rawKLTestTransform_add (T U : RadialTest) :
    rawKLTestTransform (testAdd T U) = rawKLTestTransform T + rawKLTestTransform U := by
  apply Lp.ext
  filter_upwards [rawKLTestTransform_ae (testAdd T U),
    Lp.coeFn_add (rawKLTestTransform T) (rawKLTestTransform U),
    rawKLTestTransform_ae T, rawKLTestTransform_ae U] with tau hA hsum hT hU
  rw [hA, hsum]
  change actualKtransform (testAdd T U).function tau =
    rawKLTestTransform T tau + rawKLTestTransform U tau
  rw [hT, hU]
  exact actualKtransform_testAdd T U tau

theorem rawKLTestTransform_smul (c : ℂ) (T : RadialTest) :
    rawKLTestTransform (testSMul c T) = c • rawKLTestTransform T := by
  apply Lp.ext
  filter_upwards [rawKLTestTransform_ae (testSMul c T),
    Lp.coeFn_smul c (rawKLTestTransform T), rawKLTestTransform_ae T] with tau hS hsmul hT
  rw [hS, hsmul]
  change actualKtransform (testSMul c T).function tau = c • rawKLTestTransform T tau
  rw [hT]
  exact actualKtransform_testSMul c T tau

/-- Equality of physical L2 classes of actual continuous core tests
forces pointwise equality of their genuine functions. -/
theorem test_function_eq_of_physical_eq {T U : RadialTest}
    (h : radialCoreL2 T = radialCoreL2 U) : T.function = U.function := by
  have hae : T.function =ᵐ[(volume : Measure ℝ)] U.function :=
    (T.function_memLp.toLp_eq_toLp_iff U.function_memLp).mp h
  exact MeasureTheory.eq_of_ae_eq hae T.smooth.continuous U.smooth.continuous

/-- The raw transform depends only on the physical L2 class of a core test. -/
theorem rawKLTestTransform_eq_of_physical_eq {T U : RadialTest}
    (h : radialCoreL2 T = radialCoreL2 U) : rawKLTestTransform T = rawKLTestTransform U := by
  have he := test_function_eq_of_physical_eq h
  apply Lp.ext
  filter_upwards [rawKLTestTransform_ae T, rawKLTestTransform_ae U] with tau hT hU
  rw [hT, hU, he]

private theorem physical_zero : radialCoreL2 testZero = 0 := by
  change testZero.function_memLp.toLp (0 : ℝ → ℂ) = 0
  exact MemLp.toLp_zero _

private theorem physical_add (T U : RadialTest) :
    radialCoreL2 (testAdd T U) = radialCoreL2 T + radialCoreL2 U := by
  exact T.function_memLp.toLp_add U.function_memLp

private theorem physical_smul (c : ℂ) (T : RadialTest) :
    radialCoreL2 (testSMul c T) = c • radialCoreL2 T := by
  exact MemLp.toLp_const_smul c T.function_memLp

/-- The physical compact smooth core itself, as a submodule of the actual
logarithmic physical Hilbert space L2(dr), with no extra representative data. -/
def compactPhysicalCore : Submodule ℂ RadialL2 where
  carrier := Set.range radialCoreL2
  zero_mem' := ⟨testZero, physical_zero⟩
  add_mem' := by
    rintro F G ⟨T, rfl⟩ ⟨U, rfl⟩
    exact ⟨testAdd T U, physical_add T U⟩
  smul_mem' := by
    intro c F
    rintro ⟨T, rfl⟩
    exact ⟨testSMul c T, physical_smul c T⟩

/-- This is the already proved actual dense physical core. No transform
norm statement is used to prove density. -/
theorem compactPhysicalCore_dense : Dense (compactPhysicalCore : Set RadialL2) :=
  radialCoreL2_range_dense

def physicalCoreVector (T : RadialTest) : compactPhysicalCore :=
  ⟨radialCoreL2 T, T, rfl⟩

/-- A representative is used only to evaluate the literal integral;
the theorem above has already removed its effect on the resulting vector. -/
def coreRepresentative (F : compactPhysicalCore) : RadialTest := Classical.choose F.property

theorem coreRepresentative_spec (F : compactPhysicalCore) :
    radialCoreL2 (coreRepresentative F) = (F : RadialL2) := Classical.choose_spec F.property

/-- The genuine raw KL core linear map. This is a map on physical L2
vectors, not on a redundant representative package. No extension is taken. -/
def actualCoreKLTransform : compactPhysicalCore →ₗ[ℂ] RawTauL2 where
  toFun F := rawKLTestTransform (coreRepresentative F)
  map_add' F G := by
    have hp : radialCoreL2 (coreRepresentative (F + G)) =
        radialCoreL2 (testAdd (coreRepresentative F) (coreRepresentative G)) := by
      calc
        _ = ((F + G : compactPhysicalCore) : RadialL2) := coreRepresentative_spec _
        _ = (F : RadialL2) + (G : RadialL2) := rfl
        _ = _ := by rw [physical_add, coreRepresentative_spec, coreRepresentative_spec]
    exact (rawKLTestTransform_eq_of_physical_eq hp).trans
      (rawKLTestTransform_add (coreRepresentative F) (coreRepresentative G))
  map_smul' c F := by
    have hp : radialCoreL2 (coreRepresentative (c • F)) =
        radialCoreL2 (testSMul c (coreRepresentative F)) := by
      calc
        _ = ((c • F : compactPhysicalCore) : RadialL2) := coreRepresentative_spec _
        _ = c • (F : RadialL2) := rfl
        _ = _ := by rw [physical_smul, coreRepresentative_spec]
    exact (rawKLTestTransform_eq_of_physical_eq hp).trans
      (rawKLTestTransform_smul c (coreRepresentative F))

/-- The core map agrees with the original test transform for every test,
regardless of which representative was chosen from its physical class. -/
theorem actualCoreKLTransform_on_test (T : RadialTest) :
    actualCoreKLTransform (physicalCoreVector T) = rawKLTestTransform T := by
  apply rawKLTestTransform_eq_of_physical_eq
  exact coreRepresentative_spec (physicalCoreVector T)

/-- AE integral representation for an arbitrary vector in the actual core. -/
theorem actualCoreKLTransform_ae (F : compactPhysicalCore) :
    (actualCoreKLTransform F : ℝ → ℂ) =ᵐ[tauMeasure]
      actualKtransform (coreRepresentative F).function :=
  rawKLTestTransform_ae (coreRepresentative F)

/-- In particular, the concrete core vector of T has the literal K_i*tau
integral as its tau-measure AE representative. -/
theorem actualCoreKLTransform_on_test_ae (T : RadialTest) :
    (actualCoreKLTransform (physicalCoreVector T) : ℝ → ℂ) =ᵐ[tauMeasure]
      actualKtransform T.function := by
  rw [actualCoreKLTransform_on_test]
  exact rawKLTestTransform_ae T

end
end ImbalancedChen.Part3.ActualKLCoreTransform20261025a
