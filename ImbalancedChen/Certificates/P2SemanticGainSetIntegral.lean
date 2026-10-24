import ImbalancedChen.Certificates.P2PairedSupportFubini
import ImbalancedChen.Certificates.P2ContinuousFibreFubini
import ImbalancedChen.P2PairedSemanticGainEnclosure
import Mathlib.Analysis.Normed.Group.Bounded

/-!
SOURCE ONLY; uncompiled. Imports denote the intended installation of the
adjacent candidates, not compiled suppliers.

The density below is the literal actual Buchstab extra gain times the
original Chen-quarter weight. It is continuous and bounded on the actual
positive compact box, integrable on every adopted support and on their
finite disjoint union. No target integral, enclosure, integrability, or
historical-domain identity is a premise.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral

noncomputable section

open MeasureTheory Set
open scoped BigOperators Interval
open P2HistoricalFibreBinding
open P2AdoptedUnion

/-- The original Chen-quarter weight, with K/4 occurring exactly once. -/
def weight (x : Point) : ℝ :=
  pairedChenQuarterWeight (K : ℝ) (x 0) (x 1) (x 2) (x 3)

/-- Actual omega at the literal paired residual, minus its half baseline. -/
def gain (x : Point) : ℝ :=
  pairedSemanticBuchstabGain (x 0) (x 1) (x 2) (x 3)

/-- Genuine semantic density G_B W_E; this is not a constant surrogate. -/
def semanticKernel (x : Point) : ℝ := weight x * gain x

def buchstabKernel (x : Point) : ℝ := weight x *
  LiLiuPrereqBuchstab.buchstab ((1 - x 0 - x 1 - x 2 - x 3) / x 2)

def halfBaselineKernel (x : Point) : ℝ := weight x * (1 / 2)

theorem buchstabKernel_sub_halfBaselineKernel (x : Point) :
    buchstabKernel x - halfBaselineKernel x = semanticKernel x := by
  unfold buchstabKernel halfBaselineKernel semanticKernel gain pairedSemanticBuchstabGain
  ring

theorem weight_eq_raw (x : Point) :
    weight x = ((K : ℝ) / 4) * rawKernel x := by
  rw [weight, rawKernel, pairedFibreKernel_eq]
  unfold pairedChenQuarterWeight
  ring

theorem continuousOn_weight : ContinuousOn weight box := by
  have hEq : weight = fun x => ((K : ℝ) / 4) * rawKernel x :=
    funext weight_eq_raw
  rw [hEq]
  exact continuousOn_const.mul continuousOn_rawKernel

theorem continuousOn_gain : ContinuousOn gain box := by
  have hc (i : Fin 4) : ContinuousOn (fun x : Point => x i) box :=
    (continuous_apply i).continuousOn
  have harg : ContinuousOn
      (fun x : Point => (1 - x 0 - x 1 - x 2 - x 3) / x 2) box :=
    ((((continuousOn_const.sub (hc 0)).sub (hc 1)).sub (hc 2)).sub (hc 3)).div
      (hc 2) (fun x hx => (coordinates_pos hx 2).ne')
  exact (LiLiuPrereqBuchstab.continuous_buchstab.comp_continuousOn harg).sub
    continuousOn_const

theorem continuousOn_semanticKernel : ContinuousOn semanticKernel box :=
  continuousOn_weight.mul continuousOn_gain

theorem continuousOn_halfBaselineKernel : ContinuousOn halfBaselineKernel box :=
  continuousOn_weight.mul continuousOn_const

theorem continuousOn_buchstabKernel : ContinuousOn buchstabKernel box := by
  have hEq : buchstabKernel = fun x => semanticKernel x + halfBaselineKernel x := by
    funext x
    have hx := buchstabKernel_sub_halfBaselineKernel x
    linarith
  rw [hEq]
  exact continuousOn_semanticKernel.add continuousOn_halfBaselineKernel

/-- A genuine finite uniform bound follows from continuity and compactness. -/
theorem semanticKernel_bounded :
    ∃ C : ℝ, ∀ x ∈ box, ‖semanticKernel x‖ ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc.image_of_continuousOn continuousOn_semanticKernel).isBounded.exists_norm_le
  exact ⟨C, fun x hx => hC _ ⟨x, hx, rfl⟩⟩

theorem semanticKernel_bounded_region :
    ∃ C : ℝ, ∀ x ∈ region, ‖semanticKernel x‖ ≤ C := by
  obtain ⟨C, hC⟩ := semanticKernel_bounded
  exact ⟨C, fun x hx => hC x (region_subset_box hx)⟩

theorem integrableOn_semanticKernel_box :
    IntegrableOn semanticKernel box (volume : Measure Point) :=
  continuousOn_semanticKernel.integrableOn_compact isCompact_Icc

theorem integrableOn_semanticKernel_support (r : Row) :
    IntegrableOn semanticKernel (support r) (volume : Measure Point) :=
  integrableOn_semanticKernel_box.mono_set (support_subset_box r)

theorem integrableOn_semanticKernel_region :
    IntegrableOn semanticKernel region (volume : Measure Point) :=
  integrableOn_semanticKernel_box.mono_set region_subset_box

theorem support_kernel_ge_certificate (r : Row) {x : Point}
    (hx : x ∈ support r) : ((K : ℝ) / 80) * rawKernel x ≤ semanticKernel x := by
  have hh := row_fibre_buchstab_extra_kernel r hx
  rw [semanticKernel, weight_eq_raw]
  unfold gain pairedSemanticBuchstabGain
  change ((K : ℝ) / 80) * rawKernel x ≤ _ at hh
  calc
    _ ≤ ((K : ℝ) / 4) *
        (LiLiuPrereqBuchstab.buchstab ((1 - x 0 - x 1 - x 2 - x 3) / x 2) - 1 / 2) *
        rawKernel x := hh
    _ = _ := by ring

theorem region_kernel_ge_certificate {x : Point} (hx : x ∈ region) :
    ((K : ℝ) / 80) * rawKernel x ≤ semanticKernel x := by
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
  exact support_kernel_ge_certificate r hr

theorem semanticKernel_nonneg_region {x : Point} (hx : x ∈ region) :
    0 ≤ semanticKernel x := by
  have hK : (0 : ℝ) ≤ (K : ℝ) / 80 := by norm_num [K]
  exact (mul_nonneg hK (rawKernel_nonneg (region_subset_box hx))).trans
    (region_kernel_ge_certificate hx)

/-- The requested actual product-volume integral over FullMask.region. -/
def unionSemanticIntegral : ℝ := ∫ x : Point in region, semanticKernel x

def unionBuchstabIntegral : ℝ := ∫ x : Point in region, buchstabKernel x

def unionHalfBaselineIntegral : ℝ := ∫ x : Point in region, halfBaselineKernel x

/-- Literal subtraction of the new and old genuine union integrals. -/
theorem unionBuchstabIntegral_sub_halfBaseline :
    unionBuchstabIntegral - unionHalfBaselineIntegral = unionSemanticIntegral := by
  have hB : IntegrableOn buchstabKernel region (volume : Measure Point) :=
    (continuousOn_buchstabKernel.integrableOn_compact isCompact_Icc).mono_set
      region_subset_box
  have hH : IntegrableOn halfBaselineKernel region (volume : Measure Point) :=
    (continuousOn_halfBaselineKernel.integrableOn_compact isCompact_Icc).mono_set
      region_subset_box
  rw [unionBuchstabIntegral, unionHalfBaselineIntegral, unionSemanticIntegral,
    ← integral_sub hB hH]
  exact integral_congr_ae (Filter.Eventually.of_forall
    buchstabKernel_sub_halfBaselineKernel)

theorem unionSemanticIntegral_eq_sum : unionSemanticIntegral =
    ∑ r : Row, ∫ x : Point in support r, semanticKernel x := by
  exact integral_iUnion_fintype support_measurable supports_pairwise_disjoint
    integrableOn_semanticKernel_support

theorem partialSemanticIntegral_eq_sum (s : Finset Row) :
    (∫ x : Point in ⋃ r ∈ s, support r, semanticKernel x) =
      ∑ r ∈ s, ∫ x : Point in support r, semanticKernel x := by
  apply integral_biUnion_finset s (fun r _ => support_measurable r)
  · intro r _ q _ hrq
    exact supports_pairwise_disjoint hrq
  · intro r _
    exact integrableOn_semanticKernel_support r

/-- The seven proved null walls apply to the actual omega density too. -/
theorem closedSupport_semanticIntegral (r : Row) :
    (∫ x : Point in P2AdoptedUnion.closedSupport r, semanticKernel x) =
      ∫ x : Point in support r, semanticKernel x :=
  setIntegral_congr_set (closedSupport_ae_eq_support r)

/-- Specialization of the nonseparable coordinate-Fubini theorem to the
actual omega density. Integrability is proved above, not an input premise. -/
theorem support_semanticIntegral_eq_rowGainIntegral (r : Row) :
    (∫ x : Point in support r, semanticKernel x) =
      P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r := by
  simpa [semanticKernel, weight, gain,
    P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral] using
      P2ContinuousFibreFubini.support_setIntegral_eq_fourfold r semanticKernel
        (integrableOn_semanticKernel_support r)

/-- Equality with the existing actual iterated row sum, with no assumed
coordinate identity, parent injection, or historical-domain identification. -/
theorem unionSemanticIntegral_eq_fullSemanticGain :
    unionSemanticIntegral = P2PairedSemanticGainEnclosure.fullSemanticGain := by
  rw [unionSemanticIntegral_eq_sum]
  unfold P2PairedSemanticGainEnclosure.fullSemanticGain
  exact Finset.sum_congr rfl (fun r _ => support_semanticIntegral_eq_rowGainIntegral r)

/-- The requested original rational endpoint also follows directly from
the existing actual iterated semantic gain comparison. -/
theorem unionSemanticIntegral_lower_via_semanticFubini :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤ unionSemanticIntegral := by
  rw [unionSemanticIntegral_eq_fullSemanticGain]
  exact P2PairedSemanticGainEnclosure.fullSemanticGain_lower

/-- A second route to the lower bound: monotonicity of genuine set integrals.
This does not need the nonseparable semantic coordinate-Fubini bridge. -/
theorem unionSemanticIntegral_ge_constant :
    P2AdoptedUnion.unionIntegral ≤ unionSemanticIntegral := by
  have h := setIntegral_mono_on
    (integrableOn_region.const_mul ((K : ℝ) / 80))
    integrableOn_semanticKernel_region region_measurable
    (fun x hx => region_kernel_ge_certificate hx)
  simpa only [unionIntegral, unionSemanticIntegral, integral_const_mul] using h

theorem unionSemanticIntegral_lower :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤ unionSemanticIntegral :=
  P2PairedSupportFubini.union_actual_enclosure.1.trans unionSemanticIntegral_ge_constant

theorem unionSemanticIntegral_adopted_lower :
    (558583 / 1000000000 : ℝ) ≤ unionSemanticIntegral := by
  have h : (558583 / 1000000000 : ℝ) ≤
      P2AdoptedUnion.unionIntegral := by
    rw [P2PairedSupportFubini.unionIntegral_eq_integral]
    exact adopted_extra_gross_lower
  exact h.trans unionSemanticIntegral_ge_constant

theorem unionSemanticIntegral_pos : 0 < unionSemanticIntegral :=
  lt_of_lt_of_le (by norm_num) unionSemanticIntegral_lower

theorem unionBuchstabIntegral_difference_lower :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤
      unionBuchstabIntegral - unionHalfBaselineIntegral := by
  rw [unionBuchstabIntegral_sub_halfBaseline]
  exact unionSemanticIntegral_lower

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2SemanticGainSetIntegral
