import ImbalancedChen.Part3ActualCylinderFourierCoefficients
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Compact smooth tests detect a genuine vector in L²((0,∞),dy/y²).
The proof moves the measure, not derivatives or charts, to the real line.
Local integrability on the open positive half-line is proved from L² and
finite measure on compact positive-height sets. The distributional
fundamental lemma is applied only after this local integrability proof.
-/
namespace ImbalancedChen.Part3.CuspCompactHeightTestDetection20261026b
noncomputable section
open Set Function MeasureTheory Filter
open scoped ContDiff
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a

attribute [local instance] Measure.Subtype.measureSpace

def heightZeroExtension (f : PositiveHeight → ℂ) : ℝ → ℂ :=
  Function.extend ((↑) : PositiveHeight → ℝ) f 0

@[simp] theorem heightZeroExtension_coe (f : PositiveHeight → ℂ)
    (y : PositiveHeight) : heightZeroExtension f (y : ℝ) = f y :=
  Subtype.coe_injective.extend_apply f 0 y

def coordinateHeightMeasure : Measure ℝ :=
  Measure.map ((↑) : PositiveHeight → ℝ) heightMeasure

private def heightEmbedding :
    MeasurableEmbedding ((↑) : PositiveHeight → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Ioi

/-- Pulling a compact subset of the open half-line back to the subtype
preserves compactness. In particular no neighbourhood of height zero is
silently asserted to have finite hyperbolic measure. -/
theorem positiveHeight_preimage_isCompact {K : Set ℝ}
    (hK : IsCompact K) (hpos : K ⊆ Ioi (0 : ℝ)) :
    IsCompact (((↑) : PositiveHeight → ℝ) ⁻¹' K) := by
  rw [Subtype.isCompact_iff]
  have he : ((↑) : PositiveHeight → ℝ) ''
      (((↑) : PositiveHeight → ℝ) ⁻¹' K) = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hpos hx⟩, hx, rfl⟩
  rwa [he]

theorem coordinateHeightMeasure_compact_lt_top {K : Set ℝ}
    (hK : IsCompact K) (hpos : K ⊆ Ioi (0 : ℝ)) :
    coordinateHeightMeasure K < ∞ := by
  rw [coordinateHeightMeasure, Measure.map_apply measurable_subtype_coe hK.measurableSet]
  exact (positiveHeight_preimage_isCompact hK hpos).measure_lt_top

theorem heightZeroExtension_memLp (u : HeightL2) :
    MemLp (heightZeroExtension u) 2 coordinateHeightMeasure := by
  rw [coordinateHeightMeasure, heightEmbedding.memLp_map_measure_iff]
  simpa only [Function.comp_def, heightZeroExtension_coe] using Lp.memLp u

/-- The necessary local L¹ hypothesis is obtained from actual height L²
on each compact subset away from zero. -/
theorem heightZeroExtension_locallyIntegrable (u : HeightL2) :
    LocallyIntegrableOn (heightZeroExtension u) (Ioi (0 : ℝ))
      coordinateHeightMeasure := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hpos hK
  letI : IsFiniteMeasure (coordinateHeightMeasure.restrict K) :=
    ⟨by simpa using coordinateHeightMeasure_compact_lt_top hK hpos⟩
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    ((heightZeroExtension_memLp u).restrict K)

/-- Every actual smooth compact positive-height scalar test belongs to the
native height L² space. This fact is proved, rather than required of tests. -/
theorem heightTest_memLp {β : ℝ → ℝ} (hβ : Continuous β)
    (hc : HasCompactSupport β) (hs : tsupport β ⊆ Ioi (0 : ℝ)) :
    MemLp (fun y : PositiveHeight => (β (y : ℝ) : ℂ)) 2 heightMeasure := by
  have hK := positiveHeight_preimage_isCompact hc hs
  have hcont : Continuous (fun y : PositiveHeight => (β (y : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hβ.comp continuous_subtype_val)
  have hsupp : support (fun y : PositiveHeight => (β (y : ℝ) : ℂ)) ⊆
      ((↑) : PositiveHeight → ℝ) ⁻¹' tsupport β := by
    intro y hy
    apply subset_closure
    simpa only [mem_support, Complex.ofReal_eq_zero] using hy
  have hc' : HasCompactSupport (fun y : PositiveHeight => (β (y : ℝ) : ℂ)) :=
    hK.of_isClosed_subset isClosed_tsupport
      (closure_minimal hsupp hK.isClosed)
  exact hcont.memLp_of_hasCompactSupport hc'

/-- The compact-height fundamental lemma for the literal dy/y² space.
Only real smooth compact tests supported at positive height are needed. -/
theorem eq_zero_of_compact_height_tests (u : HeightL2)
    (htest : ∀ β : ℝ → ℝ, ContDiff ℝ ∞ β → HasCompactSupport β →
      tsupport β ⊆ Ioi (0 : ℝ) →
      (∫ y : PositiveHeight, β (y : ℝ) • u y ∂heightMeasure) = 0) :
    u = 0 := by
  have hz : ∀ᵐ t ∂coordinateHeightMeasure,
      t ∈ Ioi (0 : ℝ) → heightZeroExtension u t = 0 := by
    apply isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (heightZeroExtension_locallyIntegrable u)
    intro β hβ hc hs
    rw [coordinateHeightMeasure, heightEmbedding.integral_map]
    simpa only [heightZeroExtension_coe] using htest β hβ hc hs
  have hy : ∀ᵐ y ∂heightMeasure, u y = 0 := by
    have hh := heightEmbedding.ae_map_iff.mp hz
    filter_upwards [hh] with y h
    simpa only [heightZeroExtension_coe] using h y.property
  apply Lp.ext
  exact hy.trans (Lp.coeFn_zero ℂ 2 heightMeasure).symm

end
end ImbalancedChen.Part3.CuspCompactHeightTestDetection20261026b
