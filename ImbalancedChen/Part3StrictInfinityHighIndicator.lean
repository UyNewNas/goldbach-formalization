import ImbalancedChen.Part3PrimeHighCuspQuotientSeparation
import ImbalancedChen.Part3ActualParabolicHighSeedLocalFinite

/-! The strict high-cusp image is the ACTUAL geometric quotient set,
and its indicator is the actual strict parabolic Poincare trace. The
pointwise identity and quotient measurability include Y=1. Canonical
reduced-carrier transport is used only for the explicit quotient AE
Poincare identity, never as a geometric-image premise.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane ENNReal
open ImbalancedChen.Part3.Gamma0ParabolicCosetRows20261025a
open ImbalancedChen.Part3.Gamma0ParabolicEffectiveDecomposition20261025a
open ImbalancedChen.Part3.GammaInfinityTranslationStrip20261025a
open ImbalancedChen.Part3.ActualParabolicHighSeedLocalFinite20261025a
open ImbalancedChen.Part3.Gamma0ActualParabolicUnfolding20261025a
open ImbalancedChen.Part3.Gamma0ActualHighCuspTail20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0CarrierMeasurableInverse20261025a
open ImbalancedChen.Part3.Gamma0QuotientConullTransport20261025a
open ImbalancedChen.Part3.PrimeHighCuspQuotientSeparation20261026b

namespace ImbalancedChen.Part3.StrictInfinityHighIndicator20261026b

theorem strictHighSeed_measurable (Y : ℝ) : Measurable (strictHighSeed Y) :=
  measurable_const.indicator
    ((isOpen_lt continuous_const UpperHalfPlane.continuous_im).measurableSet)

theorem strictHighSeed_periodic (Y : ℝ) (k : ℤ) (z : UpperHalfPlane) :
    strictHighSeed Y (translate k z) = strictHighSeed Y z := by
  simp only [strictHighSeed, Set.indicator, Set.mem_setOf_eq, translate_im]

theorem neighborhood_mem_iff_deck (N : ℕ) (Y : ℝ) (z : UpperHalfPlane) :
    orbitProjection N z ∈ infinityHighNeighborhood N Y ↔
      ∃ g : CongruenceSubgroup.Gamma0 N, Y < (g • z).im := by
  constructor
  · rintro ⟨w, hw, hq⟩
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hq)
    exact ⟨g, by simpa only [hg] using hw⟩
  · rintro ⟨g, hg⟩
    exact ⟨g • z, hg, orbitProjection_smul N g z⟩

theorem neighborhood_mem_iff_parabolic_representative (N : ℕ) (Y : ℝ) (z : UpperHalfPlane) :
    orbitProjection N z ∈ infinityHighNeighborhood N Y ↔
      ∃ q : GammaInfinityCosets N, Y < (parabolicRepresentative N q • z).im := by
  constructor
  · intro hz
    obtain ⟨g, hg⟩ := (neighborhood_mem_iff_deck N Y z).mp hz
    let q : GammaInfinityCosets N := Quotient.mk'' g
    have hperiod : ∀ k : ℤ, ∀ w : UpperHalfPlane, ((k : ℝ) +ᵥ w).im = w.im :=
      fun k w => UpperHalfPlane.vadd_im _ _
    have heq : (Quotient.mk'' (parabolicRepresentative N q) : GammaInfinityCosets N) =
        Quotient.mk'' g := parabolicRepresentative_class N q
    have him := congrArg (periodicSeedOnCosets N (fun w => w.im) hperiod z) heq
    change (parabolicRepresentative N q • z).im = (g • z).im at him
    exact ⟨q, by rw [him]; exact hg⟩
  · rintro ⟨q, hq⟩
    exact (neighborhood_mem_iff_deck N Y z).mpr ⟨parabolicRepresentative N q, hq⟩

/-- Pointwise identity of the genuine trace with the geometric quotient
indicator. The old strict-high uniqueness supplies 0/1 multiplicity. -/
theorem strict_trace_eq_geometric_indicator (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (z : UpperHalfPlane) :
    parabolicTraceNN N (strictHighSeed Y) z =
      (infinityHighNeighborhood N Y).indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z) := by
  classical
  by_cases hz : orbitProjection N z ∈ infinityHighNeighborhood N Y
  · rw [Set.indicator_of_mem hz]
    obtain ⟨q, hq⟩ := (neighborhood_mem_iff_parabolic_representative N Y z).mp hz
    rcases strictHighTrace_zero_or_one N Y hY z with hzero | hone
    · exfalso
      have hqzero := (ENNReal.tsum_eq_zero.mp hzero) q
      have hbad : (1 : ℝ≥0∞) = 0 := by
        simpa only [strictHighSeed, Set.indicator_of_mem hq] using hqzero
      exact one_ne_zero hbad
    · exact hone
  · rw [Set.indicator_of_notMem hz]
    unfold parabolicTraceNN
    apply tsum_eq_zero
    intro q
    exact Set.indicator_of_notMem
      (fun hq => hz ((neighborhood_mem_iff_parabolic_representative N Y z).mpr ⟨q, hq⟩)) _

theorem infinityHighNeighborhood_measurable (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y) :
    MeasurableSet (infinityHighNeighborhood N Y) := by
  apply measurableSet_quotient.mpr
  change MeasurableSet {z : UpperHalfPlane | orbitProjection N z ∈ infinityHighNeighborhood N Y}
  have heq : {z : UpperHalfPlane | orbitProjection N z ∈ infinityHighNeighborhood N Y} =
      {z : UpperHalfPlane | parabolicTraceNN N (strictHighSeed Y) z = 1} := by
    ext z
    rw [strict_trace_eq_geometric_indicator N Y hY z]
    by_cases hz : orbitProjection N z ∈ infinityHighNeighborhood N Y <;> simp [hz]
  rw [heq]
  exact (parabolicTraceNN_measurable N _ (strictHighSeed_measurable Y)).preimage measurableSet_singleton

/-- Native canonical quotient transport: the Poincare extension is equal
AE to the ACTUAL strict geometric neighborhood indicator. -/
theorem strict_poincare_eq_geometric_indicator_ae (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 ≤ Y) :
    parabolicNonnegativePoincare N (strictHighSeed Y) =ᵐ[carrierPushforward N]
      (infinityHighNeighborhood N Y).indicator (fun _ => (1 : ℝ≥0∞)) := by
  filter_upwards [reducedProjection_range_ae N] with q hq
  obtain ⟨z, rfl⟩ := hq
  rw [parabolicNonnegativePoincare_projection]
  exact strict_trace_eq_geometric_indicator N Y hY z

end ImbalancedChen.Part3.StrictInfinityHighIndicator20261026b
