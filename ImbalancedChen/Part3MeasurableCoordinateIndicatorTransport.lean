import ImbalancedChen.Part3CompactCoordinateIndicatorInvariance

/-!
Transport of coordinate-generated indicator invariance from a compact
real coordinate to an arbitrary raw measure space. A measurable coordinate
with a measurable almost-everywhere left inverse induces a SURJECTIVE
native L2 linear isometry. Its measure-preserving inverse and surjectivity
are proved, not assumed. Closed coordinate-invariant submodules are then
transported to the compact-coordinate theorem and back. No finiteness,
raw-transform norm identity, dense-range, or indicator-invariance premise
is used. SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
-/

namespace ImbalancedChen.Part3.MeasurableCoordinateIndicatorTransport20261025a

noncomputable section

open MeasureTheory Set Filter
open ImbalancedChen.Part3.IndicatorInvariantCyclicDensity20261025a

variable {X : Type*} [MeasurableSpace X] {s : Set ℝ} [CompactSpace s]
variable (μ : Measure X) (c : X → s) (hc : Measurable c)

def coordinatePullback : Lp ℂ 2 (μ.map c) →ₗᵢ[ℂ] Lp ℂ 2 μ :=
  Lp.compMeasurePreservingₗᵢ ℂ c ⟨hc, rfl⟩

theorem coordinatePullback_coe_ae (u : Lp ℂ 2 (μ.map c)) :
    coordinatePullback μ c hc u =ᵐ[μ] (fun x => u (c x)) :=
  Lp.coeFn_compMeasurePreserving u ⟨hc, rfl⟩

/-- An almost-everywhere left inverse already transports the actual
pushforward measure back to the original raw measure. -/
theorem inverse_measurePreserving (d : s → X) (hd : Measurable d)
    (hleft : ∀ᵐ x ∂μ, d (c x) = x) : MeasurePreserving d (μ.map c) μ := by
  refine ⟨hd, ?_⟩
  rw [Measure.map_map hd hc, Measure.map_congr hleft, Measure.map_id]

theorem coordinatePullback_surjective (d : s → X) (hd : Measurable d)
    (hleft : ∀ᵐ x ∂μ, d (c x) = x) :
    Function.Surjective (coordinatePullback μ c hc) := by
  intro u
  let hdPres := inverse_measurePreserving μ c hc d hd hleft
  let v : Lp ℂ 2 (μ.map c) := Lp.compMeasurePreserving d hdPres u
  refine ⟨v, ?_⟩
  apply Lp.ext
  have hv : v =ᵐ[μ.map c] (fun t => u (d t)) := Lp.coeFn_compMeasurePreserving u hdPres
  have hvc := ae_of_ae_map hc.aemeasurable hv
  filter_upwards [coordinatePullback_coe_ae μ c hc v, hvc, hleft] with x hU hvx hdx
  rw [hU, hvx, hdx]

/-- This is a literal pointwise intertwining calculation. The raw
operator is supplied with its coefficient formula, not with any Borel
invariance or spectral-density conclusion. -/
theorem coordinatePullback_intertwine
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ u : Lp ℂ 2 μ, T u =ᵐ[μ] (fun x => ((c x : s) : ℝ) • u x))
    (u : Lp ℂ 2 (μ.map c)) :
    coordinatePullback μ c hc
        (CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply (μ.map c) u) =
      T (coordinatePullback μ c hc u) := by
  apply Lp.ext
  have hcompact := ae_of_ae_map hc.aemeasurable
    (CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply_coe_ae (μ.map c) u)
  filter_upwards [coordinatePullback_coe_ae μ c hc
      (CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply (μ.map c) u),
    hcompact, coordinatePullback_coe_ae μ c hc u, hT (coordinatePullback μ c hc u)]
      with x hleft hmult hraw hright
  rw [hleft, hmult, hright, hraw]

theorem coordinatePullback_indicator
    (d : s → X) (hd : Measurable d) (hleft : ∀ᵐ x ∂μ, d (c x) = x)
    (B : Set X) (hB : MeasurableSet B) (u : Lp ℂ 2 (μ.map c)) :
    coordinatePullback μ c hc
        (indicatorMultiplier (μ.map c) (d ⁻¹' B) (hB.preimage hd) u) =
      indicatorMultiplier μ B hB (coordinatePullback μ c hc u) := by
  apply Lp.ext
  have hcompact := ae_of_ae_map hc.aemeasurable
    (indicatorMultiplier_coe_ae (μ.map c) (d ⁻¹' B) (hB.preimage hd) u)
  filter_upwards [coordinatePullback_coe_ae μ c hc
      (indicatorMultiplier (μ.map c) (d ⁻¹' B) (hB.preimage hd) u),
    hcompact, coordinatePullback_coe_ae μ c hc u,
    indicatorMultiplier_coe_ae μ B hB (coordinatePullback μ c hc u), hleft]
      with x hU hcompactx hraw hind hdx
  rw [hU, hcompactx, hind]
  by_cases hx : x ∈ B
  · have hdc : c x ∈ d ⁻¹' B := by simpa only [mem_preimage, hdx] using hx
    simp only [indicator_of_mem hdc, indicator_of_mem hx, hraw]
  · have hdc : c x ∉ d ⁻¹' B := by simpa only [mem_preimage, hdx] using hx
    simp only [indicator_of_notMem hdc, indicator_of_notMem hx]

/-- Main raw-measure implication: actual coordinate invariance of a
closed L2 submodule entails every raw measurable indicator invariance. -/
theorem indicatorMultiplier_mem
    (d : s → X) (hd : Measurable d) (hleft : ∀ᵐ x ∂μ, d (c x) = x)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ u : Lp ℂ 2 μ, T u =ᵐ[μ] (fun x => ((c x : s) : ℝ) • u x))
    (S : Submodule ℂ (Lp ℂ 2 μ)) (hclosed : IsClosed (S : Set (Lp ℂ 2 μ)))
    (hstable : ∀ u, u ∈ S → T u ∈ S)
    (B : Set X) (hB : MeasurableSet B) (u : Lp ℂ 2 μ) (hu : u ∈ S) :
    indicatorMultiplier μ B hB u ∈ S := by
  let K : Submodule ℂ (Lp ℂ 2 (μ.map c)) :=
    S.comap (coordinatePullback μ c hc).toLinearMap
  have hKclosed : IsClosed (K : Set (Lp ℂ 2 (μ.map c))) :=
    hclosed.preimage (coordinatePullback μ c hc).continuous
  have hKstable : ∀ v, v ∈ K →
      CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply (μ.map c) v ∈ K := by
    intro v hv
    change coordinatePullback μ c hc
      (CompactCoordinateIndicatorInvariance20261025a.coordinateMultiply (μ.map c) v) ∈ S
    rw [coordinatePullback_intertwine μ c hc T hT]
    exact hstable _ hv
  obtain ⟨v, rfl⟩ := coordinatePullback_surjective μ c hc d hd hleft u
  have hmem : indicatorMultiplier (μ.map c) (d ⁻¹' B) (hB.preimage hd) v ∈ K :=
    CompactCoordinateIndicatorInvariance20261025a.indicatorMultiplier_mem
      (μ.map c) K hKclosed hKstable (d ⁻¹' B) (hB.preimage hd) v hu
  change coordinatePullback μ c hc
    (indicatorMultiplier (μ.map c) (d ⁻¹' B) (hB.preimage hd) v) ∈ S at hmem
  rw [coordinatePullback_indicator μ c hc d hd hleft B hB v] at hmem
  exact hmem

/-- The actual single-vector fullness criterion can now be applied
using coordinate invariance, with no separate indicator premise. -/
theorem closed_coordinate_invariant_eq_top
    (d : s → X) (hd : Measurable d) (hleft : ∀ᵐ x ∂μ, d (c x) = x)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hT : ∀ u : Lp ℂ 2 μ, T u =ᵐ[μ] (fun x => ((c x : s) : ℝ) • u x))
    (S : Submodule ℂ (Lp ℂ 2 μ)) (hclosed : IsClosed (S : Set (Lp ℂ 2 μ)))
    (hstable : ∀ u, u ∈ S → T u ∈ S)
    (u : Lp ℂ 2 μ) (hu : u ∈ S) (hnonzero : ∀ᵐ x ∂μ, u x ≠ 0) : S = ⊤ :=
  closed_indicator_invariant_eq_top μ S hclosed
    (fun B hB v hv => indicatorMultiplier_mem μ c hc d hd hleft T hT S hclosed hstable B hB v hv)
    u hu hnonzero

end

end ImbalancedChen.Part3.MeasurableCoordinateIndicatorTransport20261025a
