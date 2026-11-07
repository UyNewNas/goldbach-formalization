import ImbalancedChen.Part3Gamma0QuotientCellPushforward
import ImbalancedChen.Part3Gamma0CarrierInteriorUniqueness

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Removing the explicit translated modular boundaries gives an actual
Gamma0 carrier on which the orbit projection is injective. This removal
changes neither the canonical volume restriction nor its quotient
pushforward. Thus the finite carrier has an explicit full-measure set of
unique orbit representatives. No measurable inverse or arbitrary-domain
independence theorem is asserted.
-/

namespace ImbalancedChen.Part3.Gamma0CarrierAESection20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane Pointwise
open ImbalancedChen.Part3.ModularFundamentalFiniteMeasure20261024z
open ImbalancedChen.Part3.Gamma0FiniteCarrierExactMeasure20261024zz
open ImbalancedChen.Part3.Gamma0FiniteMeasureCarrier20261024z
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierInteriorUniqueness20261025a

/-- The old concrete carrier with the explicit null boundary union removed. -/
def reducedCarrier (N : ℕ) [NeZero N] : Set UpperHalfPlane :=
  gamma0Carrier N \ gamma0BoundaryCarrier N

theorem reducedCarrier_subset_carrier (N : ℕ) [NeZero N] :
    reducedCarrier N ⊆ gamma0Carrier N := sdiff_subset

theorem reducedCarrier_subset_open (N : ℕ) [NeZero N] :
    reducedCarrier N ⊆ gamma0OpenCarrier N := by
  intro z hz
  by_contra hnot
  exact hz.2 (carrier_sdiff_open_subset_boundary N ⟨hz.1, hnot⟩)

/-- Measurability of the explicit exceptional boundary union. -/
theorem gamma0BoundaryCarrier_measurable (N : ℕ) [NeZero N] :
    MeasurableSet (gamma0BoundaryCarrier N) := by
  letI : Fintype (gamma0Classes N) :=
    (CongruenceSubgroup.Gamma0 N).fintypeQuotientOfFiniteIndex
  unfold gamma0BoundaryCarrier
  apply MeasurableSet.iUnion
  intro q
  change MeasurableSet
    ((SpecialLinearGroup.mapGL ℝ (inverseClassRep N q)) • modularFDBoundary)
  exact (modularFD_measurable.diff ModularGroup.isOpen_fdo.measurableSet).const_smul _

theorem reducedCarrier_measurable (N : ℕ) [NeZero N] :
    MeasurableSet (reducedCarrier N) :=
  (gamma0Carrier_measurable N).diff (gamma0BoundaryCarrier_measurable N)
/-- Equality of actual quotient representatives forces equality of points
when the first representative is in the open carrier and the second is
anywhere in the original closed carrier. Central ambiguity acts trivially. -/
theorem orbitProjection_eq_iff_open_closed (N : ℕ) [NeZero N]
    {z w : UpperHalfPlane} (hz : z ∈ gamma0OpenCarrier N)
    (hw : w ∈ gamma0Carrier N) :
    orbitProjection N z = orbitProjection N w ↔ z = w := by
  constructor
  · intro hq
    have horbit :
        MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) UpperHalfPlane w z :=
      Quotient.exact hq.symm
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp horbit
    have hγz : γ • z ∈ gamma0Carrier N := by
      rw [hγ]
      exact hw
    have hc := gamma0_open_to_closed_center N γ hz hγz
    have hfix : γ • z = z :=
      (sl2_fixed_all_iff (γ : SL(2, ℤ))).mpr hc z
    exact hfix.symm.trans hγ
  · rintro rfl
    rfl

/-- A literal injective orbit projection on the concrete reduced carrier. -/
theorem orbitProjection_injOn_reducedCarrier (N : ℕ) [NeZero N] :
    InjOn (orbitProjection N) (reducedCarrier N) := by
  intro z hz w hw hq
  exact (orbitProjection_eq_iff_open_closed N
    (reducedCarrier_subset_open N hz) hw.1).mp hq

/-- The chosen representatives omit only a canonical-volume null set. -/
theorem reducedCarrier_ae_eq_carrier (N : ℕ) [NeZero N] :
    reducedCarrier N =ᵐ[(volume : Measure UpperHalfPlane)] gamma0Carrier N := by
  have hboundary : ∀ᵐ z ∂(volume : Measure UpperHalfPlane),
      z ∉ gamma0BoundaryCarrier N := by
    apply ae_iff.mpr
    simpa only [not_not] using gamma0BoundaryCarrier_null N
  filter_upwards [hboundary] with z hz
  simp [reducedCarrier, hz]

/-- An explicit full-measure injective representative set for the actual
Gamma0 orbit projection; neither a hypothetical section nor an FD premise. -/
theorem orbitProjection_carrier_ae_injective (N : ℕ) [NeZero N] :
    ∃ s : Set UpperHalfPlane,
      s ⊆ gamma0Carrier N ∧
      MeasurableSet s ∧
      s =ᵐ[(volume : Measure UpperHalfPlane)] gamma0Carrier N ∧
      InjOn (orbitProjection N) s :=
  ⟨reducedCarrier N, reducedCarrier_subset_carrier N, reducedCarrier_measurable N,
    reducedCarrier_ae_eq_carrier N, orbitProjection_injOn_reducedCarrier N⟩

/-- Null boundary removal preserves the actual quotient measure, not only
its total mass. This connects representative uniqueness to the earlier
spatial pushforward construction. -/
theorem reducedCarrier_pushforward_eq (N : ℕ) [NeZero N] :
    cellPushforward N (reducedCarrier N) = carrierPushforward N :=
  cellPushforward_congr N (reducedCarrier_ae_eq_carrier N)

/-- Quotient-observable integrals can therefore be computed using these
unique representatives with no change of spatial normalization. -/
theorem lintegral_reducedCarrier (N : ℕ) [NeZero N]
    (F : Gamma0OrbitSpace N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q, F q ∂carrierPushforward N) =
      ∫⁻ z in reducedCarrier N, F (orbitProjection N z) := by
  rw [← reducedCarrier_pushforward_eq N]
  exact lintegral_cellPushforward N (reducedCarrier N) F hF

end
end ImbalancedChen.Part3.Gamma0CarrierAESection20261025a

