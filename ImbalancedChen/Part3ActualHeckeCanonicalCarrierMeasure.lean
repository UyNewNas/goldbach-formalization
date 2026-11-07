import ImbalancedChen.Part3ActualHeckeCarrierFundamental

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The actual finite Hecke correspondence carrier pushes forward to the
EXISTING canonical Gamma0(N*p) quotient measure. Its actual conull
coverage and actual return-kernel theorem prove exactly one effective
label in the indicator trace. The ORIGINAL canonical nonnegative
unfolding then proves integral equality with the canonical reduced
carrier. No cover measure, norm bound, or arbitrary-domain invariance
premise is supplied.
-/

namespace ImbalancedChen.Part3.ActualHeckeCanonicalCarrierMeasure20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualHeckeCorrespondenceCarrier20261026b ActualHeckeCarrierFundamental20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0CarrierAESection20261025a
open Gamma0QuotientCellPushforward20261025a

theorem correspondence_effective_label_unique (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) {z : ℍ} {q r : effectiveGamma0 (N*p)}
    (hq : effectiveMatrixAction (N*p) q z ∈ correspondenceCarrier N p hp hpN)
    (hr : effectiveMatrixAction (N*p) r z ∈ correspondenceCarrier N p hp hpN) : q = r := by
  let a := effectiveRepresentative (N*p) q
  let b := effectiveRepresentative (N*p) r
  have hmove : (b*a⁻¹) • effectiveMatrixAction (N*p) q z = effectiveMatrixAction (N*p) r z := by
    change (b*a⁻¹) • (a • z) = b • z
    rw [mul_smul, inv_smul_smul]
  have hker : b*a⁻¹ ∈ gamma0ActionKernel (N*p) :=
    correspondence_return_mem_kernel N p hp hpN (b*a⁻¹) hq (by rw [hmove]; exact hr)
  have hquot : (QuotientGroup.mk b : effectiveGamma0 (N*p)) *
      (QuotientGroup.mk a : effectiveGamma0 (N*p))⁻¹ = 1 := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff (b*a⁻¹)).mpr hker
  have hba := mul_inv_eq_one.mp hquot
  exact ((effectiveRepresentative_class (N*p) r).symm.trans
    (hba.trans (effectiveRepresentative_class (N*p) q))).symm

theorem correspondence_unique_effective_label (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) {z : ℍ}
    (hz : z ∈ allCorrespondenceTranslates N p hp hpN) :
    ∃! q : effectiveGamma0 (N*p),
      effectiveMatrixAction (N*p) q z ∈ correspondenceCarrier N p hp hpN := by
  obtain ⟨g,w,hw,hgw⟩ := mem_iUnion.mp hz
  let q : effectiveGamma0 (N*p) := QuotientGroup.mk g⁻¹
  have hact : effectiveMatrixAction (N*p) q z = w := by
    calc
      _ = g⁻¹ • z := same_effective_class_action (N*p) (effectiveRepresentative (N*p) q) g⁻¹
        (effectiveRepresentative_class (N*p) q) z
      _ = w := by rw [← hgw, inv_smul_smul]
  have hq : effectiveMatrixAction (N*p) q z ∈ correspondenceCarrier N p hp hpN := by
    rwa [hact]
  exact ⟨q,hq,fun r hr => correspondence_effective_label_unique N p hp hpN hr hq⟩

/-- The original effective trace of the actual finite-carrier indicator
has exactly one term, and the original invariance law supplies its value. -/
theorem correspondence_indicator_trace (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (f : ℍ → ℝ≥0∞)
    (hInv : ∀ g : CongruenceSubgroup.Gamma0 (N*p), ∀ z : ℍ, f (g • z) = f z)
    {z : ℍ} (hz : z ∈ allCorrespondenceTranslates N p hp hpN) :
    fullSeedTrace (N*p) ((correspondenceCarrier N p hp hpN).indicator f) z = f z := by
  obtain ⟨q,hq,hunique⟩ := correspondence_unique_effective_label N p hp hpN hz
  unfold fullSeedTrace
  calc
    _ = (correspondenceCarrier N p hp hpN).indicator f (effectiveMatrixAction (N*p) q z) := by
      apply tsum_eq_single q
      intro r hrq
      exact indicator_of_notMem (fun hr => hrq (hunique r hr)) _
    _ = f z := by
      rw [indicator_of_mem hq]
      exact hInv (effectiveRepresentative (N*p) q) z

/-- Actual canonical nonnegative unfolding proves carrier independence
for this displayed finite correspondence carrier, with no FD premise. -/
theorem correspondenceCarrier_integral_eq_canonical (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (f : ℍ → ℝ≥0∞) (hf : Measurable f)
    (hInv : ∀ g : CongruenceSubgroup.Gamma0 (N*p), ∀ z : ℍ, f (g • z) = f z) :
    (∫⁻ z in correspondenceCarrier N p hp hpN, f z) = ∫⁻ z in reducedCarrier (N*p), f z := by
  calc
    _ = ∫⁻ z : ℍ, (correspondenceCarrier N p hp hpN).indicator f z :=
      (lintegral_indicator (correspondenceCarrier_measurable N p hp hpN) f).symm
    _ = ∫⁻ z in reducedCarrier (N*p),
        fullSeedTrace (N*p) ((correspondenceCarrier N p hp hpN).indicator f) z :=
      lintegral_fullSeedTrace (N*p) _ (hf.indicator (correspondenceCarrier_measurable N p hp hpN))
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_of_ae (allCorrespondenceTranslates_ae N p hp hpN)] with z hz
      exact correspondence_indicator_trace N p hp hpN f hInv hz

/-- The finite correspondence carrier uses EXACTLY the already-existing
canonical prime-level quotient measure, with no covolume multiplier. -/
theorem correspondenceCarrier_pushforward_eq (N p : ℕ) [NeZero N] [NeZero (N*p)]
    (hp : p.Prime) (hpN : ¬ p ∣ N) :
    cellPushforward (N*p) (correspondenceCarrier N p hp hpN) = carrierPushforward (N*p) := by
  rw [← reducedCarrier_pushforward_eq (N*p)]
  ext A hA
  unfold cellPushforward
  rw [Measure.map_apply (orbitProjection_measurable (N*p)) hA,
    Measure.map_apply (orbitProjection_measurable (N*p)) hA]
  let f : ℍ → ℝ≥0∞ := (orbitProjection (N*p) ⁻¹' A).indicator (fun _ => 1)
  have hpre : MeasurableSet (orbitProjection (N*p) ⁻¹' A) := (orbitProjection_measurable (N*p)) hA
  have hf : Measurable f := measurable_const.indicator hpre
  have hInv : ∀ g : CongruenceSubgroup.Gamma0 (N*p), ∀ z : ℍ, f (g • z) = f z := by
    intro g z
    simp only [f, Set.indicator, mem_preimage, orbitProjection_smul]
  simpa only [f, lintegral_indicator hpre, lintegral_one, Measure.restrict_apply_univ] using
    correspondenceCarrier_integral_eq_canonical N p hp hpN f hf hInv

end
end ImbalancedChen.Part3.ActualHeckeCanonicalCarrierMeasure20261026b
