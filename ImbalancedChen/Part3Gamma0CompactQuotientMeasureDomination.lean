import ImbalancedChen.Part3Gamma0CompactGlobalOverlap
import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

LOCAL quotient-measure control on every actual compact subset K of H.
The actual effective Gamma0 compact-hit count is bounded globally by the
proved proper-action compact transporter cardinal. Nonnegative unfolding
of the indicator of K intersected with a quotient event then proves
  map(orbitProjection, volume restricted to K) <= M_K * carrierPushforward.
No local-L2, measure-domination or quotient-normalization target is an
input. The full upper-half-plane pullback is NOT asserted globally L2.
-/

namespace ImbalancedChen.Part3.Gamma0CompactQuotientMeasureDomination20261025a

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane Pointwise BigOperators ENNReal
open ImbalancedChen.Part3.Gamma0EffectiveActionKernel20261024z
open ImbalancedChen.Part3.Gamma0EffectiveFiniteUnfolding20261025a
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.Gamma0CarrierAESection20261025a
open ImbalancedChen.Part3.Gamma0NonnegativePoincareUnfolding20261025a
open ImbalancedChen.Part3.Gamma0CompactGlobalOverlap20261025a

def compactQuotientPushforward (N : ℕ) (K : Set UpperHalfPlane) : Measure (Gamma0OrbitSpace N) :=
  ((volume : Measure UpperHalfPlane).restrict K).map (orbitProjection N)

theorem orbitProjection_effectiveAction (N : ℕ) (q : effectiveGamma0 N) (z : UpperHalfPlane) :
    orbitProjection N (effectiveMatrixAction N q z) = orbitProjection N z :=
  orbitProjection_smul N (effectiveRepresentative N q) z

/-- The indicator trace is the actual effective compact hit count. -/
theorem compact_indicator_trace_le (N : ℕ) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (z : UpperHalfPlane) :
    fullSeedTrace N (K.indicator (fun _ => (1 : ℝ≥0∞))) z ≤ (compactOverlapBound N K : ℝ≥0∞) := by
  have hhit := compact_hits_finite_and_card_le N hK z
  let S := hhit.1.toFinset
  have hcard : S.card ≤ compactOverlapBound N K := by
    rw [← Set.ncard_eq_toFinset_card (compactHitSet N K z) hhit.1]
    exact hhit.2.trans (Nat.le_succ _)
  calc
    fullSeedTrace N (K.indicator (fun _ => (1 : ℝ≥0∞))) z =
        ∑ q ∈ S, K.indicator (fun _ => (1 : ℝ≥0∞)) (effectiveMatrixAction N q z) := by
      apply tsum_eq_sum
      intro q hq
      have hnot : effectiveMatrixAction N q z ∉ K := by
        intro hk
        exact hq (hhit.1.mem_toFinset.mpr hk)
      simp only [Set.indicator_of_notMem hnot]
    _ = ∑ _q ∈ S, (1 : ℝ≥0∞) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hk : effectiveMatrixAction N q z ∈ K := hhit.1.mem_toFinset.mp hq
      simp only [Set.indicator_of_mem hk]
    _ = (S.card : ℝ≥0∞) := by simp
    _ ≤ _ := by exact_mod_cast hcard

def compactEventSeed (N : ℕ) (K : Set UpperHalfPlane) (A : Set (Gamma0OrbitSpace N)) :
    UpperHalfPlane → ℝ≥0∞ := (K ∩ orbitProjection N ⁻¹' A).indicator (fun _ => 1)

theorem compact_event_trace_le (N : ℕ) {K : Set UpperHalfPlane} (hK : IsCompact K)
    (A : Set (Gamma0OrbitSpace N)) (z : UpperHalfPlane) :
    fullSeedTrace N (compactEventSeed N K A) z ≤
      (compactOverlapBound N K : ℝ≥0∞)*A.indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z) := by
  by_cases hA : orbitProjection N z ∈ A
  · have heq (q : effectiveGamma0 N) :
        compactEventSeed N K A (effectiveMatrixAction N q z) =
          K.indicator (fun _ => (1 : ℝ≥0∞)) (effectiveMatrixAction N q z) := by
      by_cases hq : effectiveMatrixAction N q z ∈ K <;>
        simp [compactEventSeed,hq,orbitProjection_effectiveAction,hA]
    calc
      _ = fullSeedTrace N (K.indicator (fun _ => (1 : ℝ≥0∞))) z := tsum_congr heq
      _ ≤ (compactOverlapBound N K : ℝ≥0∞) := compact_indicator_trace_le N hK z
      _ = _ := by simp [hA]
  · have hzero (q : effectiveGamma0 N) : compactEventSeed N K A (effectiveMatrixAction N q z) = 0 := by
      simp [compactEventSeed,orbitProjection_effectiveAction,hA]
    simp only [fullSeedTrace,hzero,tsum_zero,Set.indicator_of_notMem hA,mul_zero]

theorem compactQuotientPushforward_apply_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) {A : Set (Gamma0OrbitSpace N)}
    (hA : MeasurableSet A) :
    compactQuotientPushforward N K A ≤
      (compactOverlapBound N K : ℝ≥0∞)*carrierPushforward N A := by
  have hpre : MeasurableSet (orbitProjection N ⁻¹' A) := (orbitProjection_measurable N) hA
  have hseed : Measurable (compactEventSeed N K A) :=
    measurable_const.indicator (hK.measurableSet.inter hpre)
  have hobs : Measurable (A.indicator (fun _ => (1 : ℝ≥0∞)) ∘ orbitProjection N) :=
    (measurable_const.indicator hA).comp (orbitProjection_measurable N)
  have hmass : compactQuotientPushforward N K A =
      ∫⁻ z, compactEventSeed N K A z ∂(volume : Measure UpperHalfPlane) := by
    rw [compactQuotientPushforward,Measure.map_apply (orbitProjection_measurable N) hA,
      Measure.restrict_apply hpre]
    rw [compactEventSeed,lintegral_indicator_one (hK.measurableSet.inter hpre)]
    rw [Set.inter_comm]
  calc
    compactQuotientPushforward N K A =
        ∫⁻ z in reducedCarrier N, fullSeedTrace N (compactEventSeed N K A) z := by
      rw [hmass]
      exact lintegral_fullSeedTrace N _ hseed
    _ ≤ ∫⁻ z in reducedCarrier N,
        (compactOverlapBound N K : ℝ≥0∞)*A.indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z) :=
      lintegral_mono (fun z => compact_event_trace_le N hK A z)
    _ = (compactOverlapBound N K : ℝ≥0∞)*
        ∫⁻ z in reducedCarrier N, A.indicator (fun _ => (1 : ℝ≥0∞)) (orbitProjection N z) :=
      lintegral_const_mul _ hobs
    _ = (compactOverlapBound N K : ℝ≥0∞)*carrierPushforward N A := by
      rw [← lintegral_reducedCarrier N _ (measurable_const.indicator hA),lintegral_indicator_one hA]

/-- The promised actual local measure domination, with the true compact
proper-action overlap constant and the original canonical quotient measure. -/
theorem compactQuotientPushforward_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    compactQuotientPushforward N K ≤
      (compactOverlapBound N K : ℝ≥0∞) • carrierPushforward N := by
  apply Measure.le_iff.mpr
  intro A hA
  simpa only [Measure.smul_apply,smul_eq_mul] using compactQuotientPushforward_apply_le N hK hA

/-- The actual orbit projection is quasi-measure-preserving on each
compact piece, proved from the local domination rather than assumed. -/
theorem orbitProjection_compact_quasiMeasurePreserving (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    QuasiMeasurePreserving (orbitProjection N)
      ((volume : Measure UpperHalfPlane).restrict K) (carrierPushforward N) :=
  ⟨orbitProjection_measurable N,Measure.absolutelyContinuous_of_le_smul (compactQuotientPushforward_le N hK)⟩

theorem compact_pullback_lintegral_le (N : ℕ) [NeZero N]
    {K : Set UpperHalfPlane} (hK : IsCompact K)
    (F : Gamma0OrbitSpace N → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z in K, F (orbitProjection N z)) ≤
      (compactOverlapBound N K : ℝ≥0∞)*∫⁻ q, F q ∂carrierPushforward N := by
  calc
    _ = ∫⁻ q, F q ∂compactQuotientPushforward N K :=
      (lintegral_map hF (orbitProjection_measurable N)).symm
    _ ≤ ∫⁻ q, F q ∂((compactOverlapBound N K : ℝ≥0∞) • carrierPushforward N) :=
      lintegral_mono_measure (compactQuotientPushforward_le N hK)
    _ = _ := by rw [lintegral_smul_measure]; rfl

end
end ImbalancedChen.Part3.Gamma0CompactQuotientMeasureDomination20261025a
