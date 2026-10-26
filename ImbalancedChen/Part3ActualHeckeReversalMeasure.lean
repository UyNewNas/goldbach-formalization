import ImbalancedChen.Part3ActualHeckeReversalCarrier

-- SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT, 2026-10-27.
-- The actual partial Atkin-Lehner reversal preserves the original
-- canonical prime-level quotient measure. The effective label is unique
-- modulo the FULL action kernel, including the central negative identity.

namespace ImbalancedChen.Part3.ActualHeckeReversalMeasure20261027
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ActualHeckeReversalInvolution20261026b ActualHeckeReversalCarrier20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0CarrierAESection20261025a
open Gamma0QuotientCellPushforward20261025a

variable (N p : ℕ) [NeZero (N*p)] (hp : p.Prime) (hpN : ¬ p ∣ N)

-- Uniqueness is proved for the actual transformed carrier. It is not a
-- presumed abstract fundamental domain or a division by two.
theorem reversal_effective_label_unique {z : UpperHalfPlane}
    {q r : effectiveGamma0 (N*p)}
    (hq : effectiveMatrixAction (N*p) q z ∈ reversalCarrier N p hp hpN)
    (hr : effectiveMatrixAction (N*p) r z ∈ reversalCarrier N p hp hpN) : q = r := by
  let a := effectiveRepresentative (N*p) q
  let b := effectiveRepresentative (N*p) r
  have hmove : (b*a⁻¹) • effectiveMatrixAction (N*p) q z =
      effectiveMatrixAction (N*p) r z := by
    change (b*a⁻¹) • (a • z) = b • z
    rw [mul_smul, inv_smul_smul]
  have hk : b*a⁻¹ ∈ gamma0ActionKernel (N*p) :=
    reversalCarrier_return_kernel N p hp hpN (b*a⁻¹) hq (by rw [hmove]; exact hr)
  have he : (QuotientGroup.mk b : effectiveGamma0 (N*p)) *
      (QuotientGroup.mk a : effectiveGamma0 (N*p))⁻¹ = 1 := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff (b*a⁻¹)).mpr hk
  exact ((effectiveRepresentative_class (N*p) r).symm.trans
    ((mul_inv_eq_one.mp he).trans (effectiveRepresentative_class (N*p) q))).symm

-- The genuine reversed carrier contributes exactly one effective term
-- to the original Poincare sum on a conull subset of the upper half-plane.
theorem reversal_indicator_trace_ae (f : UpperHalfPlane → ℝ≥0∞)
    (hInv : ∀ g : CongruenceSubgroup.Gamma0 (N*p), ∀ z : UpperHalfPlane,
      f (g • z) = f z) :
    ∀ᵐ z ∂(volume : Measure UpperHalfPlane),
      fullSeedTrace (N*p) ((reversalCarrier N p hp hpN).indicator f) z = f z := by
  filter_upwards [reversalCarrier_orbit_cover N p hp hpN] with z hz
  obtain ⟨g,hg⟩ := hz
  let q : effectiveGamma0 (N*p) := QuotientGroup.mk g
  have hq : effectiveMatrixAction (N*p) q z ∈ reversalCarrier N p hp hpN := by
    have he := same_effective_class_action (N*p) (effectiveRepresentative (N*p) q) g
      (effectiveRepresentative_class (N*p) q) z
    rwa [he]
  unfold fullSeedTrace
  calc
    _ = (reversalCarrier N p hp hpN).indicator f (effectiveMatrixAction (N*p) q z) := by
      apply tsum_eq_single q
      intro r hrq
      exact indicator_of_notMem
        (fun hr => hrq (reversal_effective_label_unique N p hp hpN hr hq)) _
    _ = f z := by
      rw [indicator_of_mem hq]
      exact hInv (effectiveRepresentative (N*p) q) z

theorem reversalCarrier_lintegral_eq_canonical (f : UpperHalfPlane → ℝ≥0∞)
    (hf : Measurable f)
    (hInv : ∀ g : CongruenceSubgroup.Gamma0 (N*p), ∀ z : UpperHalfPlane,
      f (g • z) = f z) :
    (∫⁻ z in reversalCarrier N p hp hpN, f z) =
      ∫⁻ z in reducedCarrier (N*p), f z := by
  calc
    _ = ∫⁻ z : UpperHalfPlane, (reversalCarrier N p hp hpN).indicator f z :=
      (lintegral_indicator (reversalCarrier_measurable N p hp hpN) f).symm
    _ = ∫⁻ z in reducedCarrier (N*p),
        fullSeedTrace (N*p) ((reversalCarrier N p hp hpN).indicator f) z :=
      lintegral_fullSeedTrace (N*p) _ (hf.indicator (reversalCarrier_measurable N p hp hpN))
    _ = _ := lintegral_congr_ae
      (ae_restrict_of_ae (reversal_indicator_trace_ae N p hp hpN f hInv))

-- This equality concerns the existing canonical spatial measure.
theorem reversalCarrier_pushforward :
    cellPushforward (N*p) (reversalCarrier N p hp hpN) = carrierPushforward (N*p) := by
  rw [← reducedCarrier_pushforward_eq (N*p)]
  ext A hA
  unfold cellPushforward
  rw [Measure.map_apply (orbitProjection_measurable (N*p)) hA,
    Measure.map_apply (orbitProjection_measurable (N*p)) hA]
  let f : UpperHalfPlane → ℝ≥0∞ := (orbitProjection (N*p) ⁻¹' A).indicator (fun _ => 1)
  have hpre : MeasurableSet (orbitProjection (N*p) ⁻¹' A) :=
    (orbitProjection_measurable (N*p)) hA
  have hf : Measurable f := measurable_const.indicator hpre
  have hInv : ∀ g : CongruenceSubgroup.Gamma0 (N*p), ∀ z : UpperHalfPlane,
      f (g • z) = f z := by
    intro g z
    simp only [f, Set.indicator, mem_preimage, orbitProjection_smul]
  simpa only [f, lintegral_indicator hpre, lintegral_one, Measure.restrict_apply_univ] using
    reversalCarrier_lintegral_eq_canonical N p hp hpN f hf hInv

-- Whole-plane invariance is used only after proving canonical carrier
-- comparison by the single effective label argument above.
theorem quotientReversal_map_measure :
    (carrierPushforward (N*p)).map (quotientReversal N p hp hpN) =
      carrierPushforward (N*p) := by
  have hmp := (reversalAction_measurePreserving N p hp hpN).restrict_image_emb
    (reversalAction_embedding N p hp hpN) (reducedCarrier (N*p))
  change MeasurePreserving _ ((volume : Measure UpperHalfPlane).restrict (reducedCarrier (N*p)))
    ((volume : Measure UpperHalfPlane).restrict (reversalCarrier N p hp hpN)) at hmp
  calc
    _ = (cellPushforward (N*p) (reducedCarrier (N*p))).map (quotientReversal N p hp hpN) := by
      rw [reducedCarrier_pushforward_eq]
    _ = cellPushforward (N*p) (reversalCarrier N p hp hpN) := by
      unfold cellPushforward
      rw [Measure.map_map (quotientReversal_measurable N p hp hpN) (orbitProjection_measurable (N*p)),
        ← hmp.map_eq, Measure.map_map (orbitProjection_measurable (N*p))
          (reversalAction_embedding N p hp hpN).measurable]
      rfl
    _ = carrierPushforward (N*p) := reversalCarrier_pushforward N p hp hpN

theorem quotientReversal_measurePreserving :
    MeasurePreserving (quotientReversal N p hp hpN)
      (carrierPushforward (N*p)) (carrierPushforward (N*p)) :=
  ⟨quotientReversal_measurable N p hp hpN, quotientReversal_map_measure N p hp hpN⟩

end
end ImbalancedChen.Part3.ActualHeckeReversalMeasure20261027
