import ImbalancedChen.Part3Gamma0CompletedLocalizedChartValue
import ImbalancedChen.Part3Gamma0ChartCutoffGeometricBudget
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite LINEAR Fourier features of the ORIGINAL quotient L2 function,
in every actual inverse-class chart. The test y^2/(width*height) cancels
the physical hyperbolic density; its character is evaluated in the
actual affine rectangle coordinates. Thus these are planar normalized
Fourier coefficients, not evaluations of a chosen smooth representative.
The finite signed index covers exactly the genuine two-dimensional box.
Its codomain dimension is index(Gamma0 N)*(2*M+1)^2, with no rank estimate
or finite-dimensional approximation supplied as a hypothesis.

The constructed 686 cutoff has a concrete specialization here. No
polynomial derivative bound on its chosen profiles is asserted. The
generic actual localized map also accepts another supplied compact
cutoff without changing either mode count or inverse-class orientation.
-/

namespace ImbalancedChen.Part3.Gamma0FiniteFourierFeatures20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane BigOperators
open Gamma0ActualSmoothQuotientCore20261025a Gamma0ActualEnergyCompletion20261025a
open Gamma0FiniteChartReconstruction20261026b Gamma0FiniteMeasureCarrier20261024z
open Gamma0CompletedLocalizedChartValue20261026b
open Gamma0CompactQuotientPullbackLinear20261025a
open Gamma0ChartCutoffGeometricBudget20261026b Gamma0TruncatedChartCutoff20261026b
open Gamma0LocalizedChartPointwiseEnergy20261026b
open PositiveRectangleAffineNormalization20261026b
open ProductCircleFiniteBoxRellich20261026a LocalRectangleFourierTail20261026a

abbrev RectangleMode (M : ℕ) := Fin (2*M+1) × Fin (2*M+1)
abbrev FeatureIndex (N : ℕ) [NeZero N] (M : ℕ) := ChartIndex N × RectangleMode M
abbrev FeatureSpace (N : ℕ) [NeZero N] (M : ℕ) := FeatureIndex N M → ℂ

def modeFrequency (M : ℕ) (a : RectangleMode M) : Frequency :=
  fun j => if j = 0 then (a.1.val : ℤ)-(M : ℤ) else (a.2.val : ℤ)-(M : ℤ)

theorem modeFrequency_mem_box (M : ℕ) (a : RectangleMode M) :
    modeFrequency M a ∈ box M := by
  apply Fintype.mem_piFinset.mpr
  intro j
  apply Finset.mem_Icc.mpr
  have ha := a.1.isLt
  have hb := a.2.isLt
  fin_cases j <;> simp [modeFrequency] <;> omega

theorem modeFrequency_covers_box (M : ℕ) (k : Frequency) (hk : k ∈ box M) :
    ∃ a : RectangleMode M, modeFrequency M a = k := by
  have hk0 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk 0)
  have hk1 := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hk 1)
  let a : Fin (2*M+1) := ⟨(k 0+(M : ℤ)).toNat, by omega⟩
  let b : Fin (2*M+1) := ⟨(k 1+(M : ℤ)).toNat, by omega⟩
  refine ⟨(a,b), ?_⟩
  funext j
  fin_cases j <;> simp [modeFrequency, a, b] <;> omega

theorem modeFrequency_injective (M : ℕ) : Function.Injective (modeFrequency M) := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have hh0 : (a.1.val : ℤ)-(M : ℤ) = (b.1.val : ℤ)-(M : ℤ) := by
    simpa [modeFrequency] using h0
  have hh1 : (a.2.val : ℤ)-(M : ℤ) = (b.2.val : ℤ)-(M : ℤ) := by
    simpa [modeFrequency] using h1
  apply Prod.ext <;> apply Fin.ext
  · omega
  · omega

theorem featureIndex_card (N : ℕ) [NeZero N] (M : ℕ) :
    Fintype.card (FeatureIndex N M) = (CongruenceSubgroup.Gamma0 N).index*(2*M+1)^2 := by
  simp only [FeatureIndex, RectangleMode, Fintype.card_prod, Fintype.card_fin]
  rw [chartIndex_card]
  ring

theorem featureSpace_finrank (N : ℕ) [NeZero N] (M : ℕ) :
    Module.finrank ℂ (FeatureSpace N M) = (CongruenceSubgroup.Gamma0 N).index*(2*M+1)^2 := by
  rw [Module.finrank_fintype_fun_eq_card, featureIndex_card]

/-- Positive Fourier character; the inner product conjugates it to the
negative character in the actual Fourier coefficient. -/
def rectangleCharacter (R : Rectangle) (k : Frequency) (z : UpperHalfPlane) : ℂ :=
  AddCircle.fourier (k 0) (((z.re-R.left)/R.width : ℝ) : UnitAddCircle) *
    AddCircle.fourier (k 1) (((z.im-R.bottom)/R.height : ℝ) : UnitAddCircle)

theorem rectangleCharacter_continuous (R : Rectangle) (k : Frequency) :
    Continuous (rectangleCharacter R k) := by
  apply Continuous.mul
  · exact (AddCircle.fourier (k 0)).continuous.comp (by fun_prop)
  · exact (AddCircle.fourier (k 1)).continuous.comp (by fun_prop)

def fourierTest (R : Rectangle) (k : Frequency) (z : UpperHalfPlane) : ℂ :=
  ((z.im^2/(R.width*R.height) : ℝ) : ℂ) * rectangleCharacter R k z

theorem fourierTest_continuous (R : Rectangle) (k : Frequency) :
    Continuous (fourierTest R k) := by
  exact (by fun_prop : Continuous (fun z : UpperHalfPlane =>
    ((z.im^2/(R.width*R.height) : ℝ) : ℂ))).mul (rectangleCharacter_continuous R k)

theorem fourierTest_memLp (R : Rectangle) (k : Frequency)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    MemLp (fourierTest R k) 2 ((volume : Measure UpperHalfPlane).restrict K) := by
  letI : IsFiniteMeasure ((volume : Measure UpperHalfPlane).restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  obtain ⟨b,hb⟩ := hK.bddAbove_image (fourierTest_continuous R k).norm.continuousOn
  apply MemLp.of_bound (fourierTest_continuous R k).aestronglyMeasurable (max b 0)
  filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
  exact (hb ⟨z,hz,rfl⟩).trans (le_max_left _ _)

def fourierTestL2 (R : Rectangle) (k : Frequency)
    {K : Set UpperHalfPlane} (hK : IsCompact K) : LocalScalarL2 K :=
  (fourierTest_memLp R k hK).toLp (fourierTest R k)

/-- Genuine inverse-class chart coefficient on ORIGINAL quotient L2. -/
def actualChartFourierCoefficient (N : ℕ) [NeZero N] (R : Rectangle)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B)
    (i : ChartIndex N) (k : Frequency) : QuotientL2 N →L[ℂ] ℂ :=
  (innerSL ℂ (fourierTestL2 R k hK)).comp
    ((cutoffMultiplyCLM ρ hc B hB).comp (chartPullbackCLM N hK (chartClass N i)))

theorem actualChartFourierCoefficient_integral (N : ℕ) [NeZero N] (R : Rectangle)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B)
    (i : ChartIndex N) (k : Frequency) (u : QuotientL2 N) :
    actualChartFourierCoefficient N R hK ρ hc B hB i k u =
      ∫ z in K, inner ℂ (fourierTest R k z)
        (ρ z * u (Gamma0QuotientCellPushforward20261025a.orbitProjection N
          (chartMatrix N i • z))) := by
  change inner ℂ (fourierTestL2 R k hK)
    (cutoffMultiply ρ hc B hB (chartPullbackCLM N hK (chartClass N i) u)) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(fourierTest_memLp R k hK).coeFn_toLp,
    cutoffMultiply_coe_ae ρ hc B hB (chartPullbackCLM N hK (chartClass N i) u),
    chartPullbackCLM_coe_ae N hK (chartClass N i) u] with z htest hmul hpull
  rw [htest, hmul, hpull]
  rfl

def actualFourierFeatures (N : ℕ) [NeZero N] (R : Rectangle)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (M : ℕ) :
    QuotientL2 N →L[ℂ] FeatureSpace N M :=
  ContinuousLinearMap.pi (fun a => actualChartFourierCoefficient N R hK ρ hc B hB
    a.1 (modeFrequency M a.2))

def actualEnergyFourierFeatures (N : ℕ) [NeZero N] (R : Rectangle)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (M : ℕ) :
    EnergyCompletion N →L[ℂ] FeatureSpace N M :=
  (actualFourierFeatures N R hK ρ hc B hB M).comp (physicalProjection N)

theorem actualFourierFeatures_eq_zero_iff (N : ℕ) [NeZero N] (R : Rectangle)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (M : ℕ) (u : QuotientL2 N) :
    actualFourierFeatures N R hK ρ hc B hB M u = 0 ↔
      ∀ i k, k ∈ box M → actualChartFourierCoefficient N R hK ρ hc B hB i k u = 0 := by
  constructor
  · intro hu i k hk
    obtain ⟨a,ha⟩ := modeFrequency_covers_box M k hk
    have h := congrFun hu (i,a)
    simpa only [actualFourierFeatures, ContinuousLinearMap.pi_apply, ha, Pi.zero_apply] using h
  · intro hu
    funext a
    exact hu a.1 (modeFrequency M a.2) (modeFrequency_mem_box M a.2)

theorem actualFourierFeatures_range_finrank_le (N : ℕ) [NeZero N] (R : Rectangle)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (ρ : UpperHalfPlane → ℂ)
    (hc : Continuous ρ) (B : ℝ) (hB : ∀ z, ‖ρ z‖ ≤ B) (M : ℕ) :
    Module.finrank ℂ (actualFourierFeatures N R hK ρ hc B hB M).toLinearMap.range ≤
      (CongruenceSubgroup.Gamma0 N).index*(2*M+1)^2 := by
  rw [← featureSpace_finrank N M]
  exact Submodule.finrank_le _

theorem featureCutoff_continuous (Y : ℝ) (hY : 1 ≤ Y) : Continuous (upperCutoff Y hY) :=
  (planarCutoff_smooth Y hY).continuous.comp
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)

/-- The earlier actually constructed cutoff, with no assumed plateau or
geometric cover, specializes the feature map on the original quotient. -/
def standardFourierFeatures (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 ≤ Y) (M : ℕ) :
    QuotientL2 N →L[ℂ] FeatureSpace N M :=
  actualFourierFeatures N (cutoffRectangle Y hY) (cutoffCompactSet_isCompact Y hY)
    (upperCutoff Y hY) (featureCutoff_continuous Y hY) 1 (upperCutoff_norm_le_one Y hY) M

end
end ImbalancedChen.Part3.Gamma0FiniteFourierFeatures20261026b
