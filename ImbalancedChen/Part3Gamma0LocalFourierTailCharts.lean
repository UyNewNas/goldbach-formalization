import ImbalancedChen.Part3LocalRectangleFourierTail
import ImbalancedChen.Part3ActualGamma0MaassDescent
import ImbalancedChen.Part3Gamma0FiniteMeasureCarrier

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The local Fourier tail primitive on the ACTUAL finite Gamma0 class charts.
Each chart is the actual inverse-class-representative Mobius pullback,
multiplied by a native C2 chart cutoff. Its C2 regularity and endpoint
condition are proved, not supplied as Fourier/Rellich hypotheses. Summing
over every genuine finite class retains exactly the Gamma0 index factor.

This is a quantitative finite-cover chart interface. It does not assert
that the independently truncated coordinate slices assemble into a finite
rank quotient approximant. That assembly, a partition reconstruction,
and extension to the completed H1 energy domain remain OPEN.
-/

namespace ImbalancedChen.Part3.Gamma0LocalFourierTailCharts20261026a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane BigOperators ENNReal
open LocalRectangleFourierTail20261026a
open Gamma0FiniteMeasureCarrier20261024z
open Gamma0CompactTensorPoincareC2Core20261025a
open ActualGamma0MaassDescent20261025a MaassWeakOperatorCore20261024zz

local instance (N : ℕ) [NeZero N] : Fintype (gamma0Classes N) :=
  (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex

/-- Actual finite-cover chart pullback. No abstract chart action or
assumed quotient compact embedding is substituted for these matrices. -/
def localizedClassChart (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (q : gamma0Classes N) (z : UpperHalfPlane) : ℂ :=
  ρ z * f (inverseClassRep N q • z)

theorem localizedClassChart_C2 (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart) (q : gamma0Classes N) :
    ContDiffOn ℝ 2 (extendUpper (localizedClassChart N f ρ q)) positiveChart := by
  intro p hp
  let g := inverseClassRep N q
  have hopen : IsOpen positiveChart := isOpen_lt continuous_const continuous_snd
  have hgp : 0 < (mobiusChart g p).2 := by
    rw [mobiusChart_eq_actual g hp]
    exact (g • chartLift p).im_pos
  have hfAt : ContDiffAt ℝ 2
      (fun r => extendUpper f (mobiusChart g r)) p :=
    ((hf _ hgp).contDiffAt (hopen.mem_nhds hgp)).comp p
      (mobiusChart_contDiffAt g hp)
  have hρAt := (hρ p hp).contDiffAt (hopen.mem_nhds hp)
  have heq : extendUpper (localizedClassChart N f ρ q) =ᶠ[𝓝 p]
      (fun r => extendUpper ρ r * extendUpper f (mobiusChart g r)) := by
    filter_upwards [hopen.mem_nhds hp] with r hr
    rw [extendUpper_chartLift _ r hr, extendUpper_chartLift ρ r hr,
      extendUpper_mobiusChart f g r hr]
    rfl
  exact ((hρAt.mul hfAt).congr_of_eventuallyEq heq).contDiffWithinAt

theorem localizedClassChart_support (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (hs : Function.support ρ ⊆ {z | z.re ∈ Ioo (0 : ℝ) 1}) (q : gamma0Classes N) :
    Function.support (localizedClassChart N f ρ q) ⊆ {z | z.re ∈ Ioo (0 : ℝ) 1} := by
  intro z hz
  apply hs
  intro hzero
  apply hz
  simp only [localizedClassChart, hzero, zero_mul]

def chartTailMass (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (a b : ℝ) (K : ℕ) (q : gamma0Classes N) : ℝ≥0∞ :=
  ∫⁻ y in Icc a b, ENNReal.ofReal ((y⁻¹)^2) * ENNReal.ofReal
    (sliceErrorSquare (extendUpper (localizedClassChart N f ρ q))
      (native_horizontal_slice_C2 _ (localizedClassChart_C2 N f ρ hf hρ q)) K y)

def chartHorizontalEnergy (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (a b : ℝ) (q : gamma0Classes N) : ℝ≥0∞ :=
  ∫⁻ y in Icc a b, ENNReal.ofReal
    (sliceDerivativeEnergy (extendUpper (localizedClassChart N f ρ q)) y)

/-- The right side is the literal derivative energy of the localized
actual Mobius chart functions. No tail bound is input to this theorem. -/
theorem finite_cover_horizontal_tail (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support ρ ⊆ {z | z.re ∈ Ioo (0 : ℝ) 1})
    (a b : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) :
    (∑ q : gamma0Classes N, chartTailMass N f ρ hf hρ a b K q) ≤
      ENNReal.ofReal ((a⁻¹)^2 * tailConstant K) *
        ∑ q : gamma0Classes N, chartHorizontalEnergy N f ρ a b q := by
  calc
    _ ≤ ∑ q : gamma0Classes N, ENNReal.ofReal ((a⁻¹)^2 * tailConstant K) *
        chartHorizontalEnergy N f ρ a b q := by
      apply Finset.sum_le_sum
      intro q _
      exact native_hyperbolic_rectangle_tail (localizedClassChart N f ρ q)
        (localizedClassChart_C2 N f ρ hf hρ q)
        (localizedClassChart_support N f ρ hs q) a b ha K hK
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A uniform per-chart energy budget retains the ACTUAL finite index.
This factor may not be dropped by treating infinity as the only cusp. -/
theorem finite_cover_horizontal_tail_index (N : ℕ) [NeZero N] (f ρ : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    (hρ : ContDiffOn ℝ 2 (extendUpper ρ) positiveChart)
    (hs : Function.support ρ ⊆ {z | z.re ∈ Ioo (0 : ℝ) 1})
    (a b : ℝ) (ha : 0 < a) (K : ℕ) (hK : 0 < K) (B : ℝ≥0∞)
    (hB : ∀ q : gamma0Classes N, chartHorizontalEnergy N f ρ a b q ≤ B) :
    (∑ q : gamma0Classes N, chartTailMass N f ρ hf hρ a b K q) ≤
      ENNReal.ofReal ((a⁻¹)^2 * tailConstant K) *
        ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * B := by
  apply (finite_cover_horizontal_tail N f ρ hf hρ hs a b ha K hK).trans
  have hsum : (∑ q : gamma0Classes N, chartHorizontalEnergy N f ρ a b q) ≤
      ((CongruenceSubgroup.Gamma0 N).index : ℝ≥0∞) * B := by
    calc
      _ ≤ ∑ _q : gamma0Classes N, B := Finset.sum_le_sum (fun q _ => hB q)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, gamma0Classes_card_eq_index]
  simpa only [mul_assoc] using mul_le_mul_left' hsum
    (ENNReal.ofReal ((a⁻¹)^2 * tailConstant K))

end
end ImbalancedChen.Part3.Gamma0LocalFourierTailCharts20261026a
