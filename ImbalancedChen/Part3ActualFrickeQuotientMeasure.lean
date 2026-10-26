import ImbalancedChen.Part3FrickeNormalizer
import ImbalancedChen.Part3ActualPrimeHeckeRealBranch
import ImbalancedChen.Part3Gamma0NonnegativePoincareUnfolding

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Literal Fricke W_N induces an actual involutive measurable map on the
Gamma0(N) orbit quotient and preserves its EXISTING canonical measure.
The image of the actual reduced carrier is proved to have conull orbit
coverage and only actual +/-I returns. Original canonical nonnegative
unfolding proves its quotient pushforward equals the canonical carrier
measure. Whole-H measure preservation is never treated as a quotient
measure premise.
-/

namespace ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane
open FrickeNormalizer ActualPrimeHeckeRealBranch20261026b
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0NonnegativePoincareUnfolding20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierInteriorUniqueness20261025a Gamma0QuotientCellPushforward20261025a

private theorem realSL_smul_eq (g : SL(2, ℤ)) (z : ℍ) : realSL g • z = g • z :=
  castIntegral_smul g z

theorem fricke_deck_action (N : ℕ) (hN : 0 < N) (g : CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    g • (frickeSL N hN • z) = frickeSL N hN • (frickeGamma0 N g • z) := by
  have hm : realSL (g : SL(2, ℤ))*frickeSL N hN =
      frickeSL N hN*realSL (frickeGamma0 N g : SL(2, ℤ)) := by
    rw [← frickeSL_conjugate_gamma0 N hN g]
    group
  rw [← realSL_smul_eq (g : SL(2, ℤ)), ← mul_smul, hm, mul_smul, realSL_smul_eq]

theorem fricke_commute_deck (N : ℕ) (hN : 0 < N) (g : CongruenceSubgroup.Gamma0 N) (z : ℍ) :
    frickeSL N hN • (g • z) = frickeGamma0 N g • (frickeSL N hN • z) := by
  simpa only [frickeGamma0_involutive N hN g] using
    (fricke_deck_action N hN (frickeGamma0 N g) z).symm

def quotientFricke (N : ℕ) (hN : 0 < N) : Gamma0OrbitSpace N → Gamma0OrbitSpace N :=
  Quotient.lift (fun z : ℍ => orbitProjection N (frickeSL N hN • z)) (by
    intro z w hzw
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hzw
    calc
      _ = orbitProjection N (frickeSL N hN • (g • w)) :=
        congrArg (fun u : ℍ => orbitProjection N (frickeSL N hN • u)) hg.symm
      _ = orbitProjection N (frickeGamma0 N g • (frickeSL N hN • w)) :=
        congrArg (orbitProjection N) (fricke_commute_deck N hN g w)
      _ = _ := orbitProjection_smul N (frickeGamma0 N g) _)

theorem quotientFricke_projection (N : ℕ) (hN : 0 < N) (z : ℍ) :
    quotientFricke N hN (orbitProjection N z) = orbitProjection N (frickeSL N hN • z) := rfl

theorem quotientFricke_measurable (N : ℕ) (hN : 0 < N) : Measurable (quotientFricke N hN) :=
  measurable_from_quotient.mpr ((orbitProjection_measurable N).comp
    (continuous_const_smul (frickeSL N hN)).measurable)

theorem quotientFricke_involutive (N : ℕ) (hN : 0 < N) : Function.Involutive (quotientFricke N hN) := by
  intro q
  refine Quotient.inductionOn q (fun z => ?_)
  simp only [quotientFricke_projection, frickeSL_action_involutive N hN z]

def frickeCarrier (N : ℕ) [NeZero N] (hN : 0 < N) : Set ℍ :=
  (fun z : ℍ => frickeSL N hN • z) '' reducedCarrier N

theorem frickeAction_embedding (N : ℕ) (hN : 0 < N) :
    MeasurableEmbedding (fun z : ℍ => frickeSL N hN • z) := by
  change MeasurableEmbedding (fun z : ℍ => SpecialLinearGroup.mapGL ℝ (frickeSL N hN) • z)
  exact measurableEmbedding_const_smul _

theorem frickeCarrier_measurable (N : ℕ) [NeZero N] (hN : 0 < N) :
    MeasurableSet (frickeCarrier N hN) :=
  (frickeAction_embedding N hN).measurableSet_image.mpr (reducedCarrier_measurable N)

theorem frickeCarrier_return_kernel (N : ℕ) [NeZero N] (hN : 0 < N)
    (g : CongruenceSubgroup.Gamma0 N) {z : ℍ}
    (hz : z ∈ frickeCarrier N hN) (hgz : g • z ∈ frickeCarrier N hN) :
    g ∈ gamma0ActionKernel N := by
  obtain ⟨x,hx,hxz⟩ := hz
  obtain ⟨y,hy,hyz⟩ := hgz
  have hm : frickeGamma0 N g • x = y := by
    apply (frickeSL_action_involutive N hN).injective
    rw [← fricke_deck_action N hN g x, hxz, hyz]
  have hfr : frickeGamma0 N g ∈ gamma0ActionKernel N :=
    gamma0_open_to_closed_mem_kernel N (frickeGamma0 N g) (reducedCarrier_subset_open N hx)
      (by rw [hm]; exact hy.1)
  apply (gamma0_actionKernel_iff N g).mpr
  apply (sl2_fixed_all_iff (g : SL(2, ℤ))).mp
  intro w
  have hfix := (sl2_fixed_all_iff (frickeGamma0 N g : SL(2, ℤ))).mpr
    ((gamma0_actionKernel_iff N (frickeGamma0 N g)).mp hfr) (frickeSL N hN • w)
  have hd := fricke_deck_action N hN g (frickeSL N hN • w)
  rw [hfix, frickeSL_action_involutive N hN w] at hd
  exact hd

theorem frickeCarrier_orbit_cover (N : ℕ) [NeZero N] (hN : 0 < N) :
    ∀ᵐ z ∂(volume : Measure ℍ), ∃ g : CongruenceSubgroup.Gamma0 N, g • z ∈ frickeCarrier N hN := by
  have hnull : (volume : Measure ℍ)
      ((fun z : ℍ => frickeSL N hN • z) ⁻¹' (allEffectiveCells N)ᶜ) = 0 := by
    rw [(frickeSL_measurePreserving N hN).measure_preimage (allEffectiveCells_measurable N).compl]
    exact allEffectiveCells_compl_null N
  have hae : ∀ᵐ z ∂(volume : Measure ℍ), frickeSL N hN • z ∈ allEffectiveCells N := by
    apply ae_iff.mpr
    exact hnull
  filter_upwards [hae] with z hz
  obtain ⟨q,x,hx,hxz⟩ := mem_iUnion.mp hz
  let a := effectiveRepresentative N q
  have hz' : z = frickeGamma0 N a • (frickeSL N hN • x) := by
    calc
      z = frickeSL N hN • (frickeSL N hN • z) := (frickeSL_action_involutive N hN z).symm
      _ = frickeSL N hN • (a • x) := congrArg (fun u : ℍ => frickeSL N hN • u) hxz.symm
      _ = _ := fricke_commute_deck N hN a x
  refine ⟨(frickeGamma0 N a)⁻¹, ?_⟩
  rw [hz', inv_smul_smul]
  exact ⟨x,hx,rfl⟩

private theorem canonical_compare (N : ℕ) [NeZero N] (C : Set ℍ) (hC : MeasurableSet C)
    (hret : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, z ∈ C → g • z ∈ C → g ∈ gamma0ActionKernel N)
    (hcover : ∀ᵐ z ∂(volume : Measure ℍ), ∃ g : CongruenceSubgroup.Gamma0 N, g • z ∈ C)
    (f : ℍ → ℝ≥0∞) (hf : Measurable f)
    (hInv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, f (g • z) = f z) :
    (∫⁻ z in C, f z) = ∫⁻ z in reducedCarrier N, f z := by
  have htrace : ∀ᵐ z ∂(volume : Measure ℍ), fullSeedTrace N (C.indicator f) z = f z := by
    filter_upwards [hcover] with z hz
    obtain ⟨g,hg⟩ := hz
    let q : effectiveGamma0 N := QuotientGroup.mk g
    have hq : effectiveMatrixAction N q z ∈ C := by
      have heq := same_effective_class_action N (effectiveRepresentative N q) g
        (effectiveRepresentative_class N q) z
      rwa [heq]
    have huniq : ∀ r : effectiveGamma0 N, effectiveMatrixAction N r z ∈ C → r = q := by
      intro r hr
      let a := effectiveRepresentative N q
      let b := effectiveRepresentative N r
      have hmove : (b*a⁻¹) • effectiveMatrixAction N q z = effectiveMatrixAction N r z := by
        change (b*a⁻¹) • (a • z) = b • z
        rw [mul_smul, inv_smul_smul]
      have hk := hret (b*a⁻¹) _ hq (by rw [hmove]; exact hr)
      have hquot : (QuotientGroup.mk b : effectiveGamma0 N)*(QuotientGroup.mk a : effectiveGamma0 N)⁻¹ = 1 := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq_one_iff _).mpr hk
      exact (effectiveRepresentative_class N r).symm.trans
        ((mul_inv_eq_one.mp hquot).trans (effectiveRepresentative_class N q))
    unfold fullSeedTrace
    calc
      _ = C.indicator f (effectiveMatrixAction N q z) := by
        apply tsum_eq_single q
        intro r hrq
        exact indicator_of_notMem (fun hr => hrq (huniq r hr)) _
      _ = f z := by rw [indicator_of_mem hq]; exact hInv (effectiveRepresentative N q) z
  calc
    _ = ∫⁻ z : ℍ, C.indicator f z := (lintegral_indicator hC f).symm
    _ = ∫⁻ z in reducedCarrier N, fullSeedTrace N (C.indicator f) z :=
      lintegral_fullSeedTrace N _ (hf.indicator hC)
    _ = _ := lintegral_congr_ae (ae_restrict_of_ae htrace)

theorem frickeCarrier_pushforward (N : ℕ) [NeZero N] (hN : 0 < N) :
    cellPushforward N (frickeCarrier N hN) = carrierPushforward N := by
  rw [← reducedCarrier_pushforward_eq N]
  ext A hA
  unfold cellPushforward
  rw [Measure.map_apply (orbitProjection_measurable N) hA,
    Measure.map_apply (orbitProjection_measurable N) hA]
  let f : ℍ → ℝ≥0∞ := (orbitProjection N ⁻¹' A).indicator (fun _ => 1)
  have hpre := (orbitProjection_measurable N) hA
  have hf : Measurable f := measurable_const.indicator hpre
  have hInv : ∀ g : CongruenceSubgroup.Gamma0 N, ∀ z : ℍ, f (g • z) = f z := by
    intro g z
    simp only [f, Set.indicator, mem_preimage, orbitProjection_smul]
  simpa only [f, lintegral_indicator hpre, lintegral_one, Measure.restrict_apply_univ] using
    canonical_compare N (frickeCarrier N hN) (frickeCarrier_measurable N hN)
      (fun g z hz hgz => frickeCarrier_return_kernel N hN g hz hgz)
      (frickeCarrier_orbit_cover N hN) f hf hInv

/-- FULL canonical quotient Fricke measure preservation, derived from
actual transformed-carrier geometry and original canonical unfolding. -/
theorem quotientFricke_map_measure (N : ℕ) [NeZero N] (hN : 0 < N) :
    (carrierPushforward N).map (quotientFricke N hN) = carrierPushforward N := by
  have hmp := (frickeSL_measurePreserving N hN).restrict_image_emb
    (frickeAction_embedding N hN) (reducedCarrier N)
  change MeasurePreserving _ ((volume : Measure ℍ).restrict (reducedCarrier N))
    ((volume : Measure ℍ).restrict (frickeCarrier N hN)) at hmp
  calc
    _ = (cellPushforward N (reducedCarrier N)).map (quotientFricke N hN) := by
      rw [reducedCarrier_pushforward_eq]
    _ = cellPushforward N (frickeCarrier N hN) := by
      unfold cellPushforward
      rw [Measure.map_map (quotientFricke_measurable N hN) (orbitProjection_measurable N),
        ← hmp.map_eq, Measure.map_map (orbitProjection_measurable N) (frickeAction_embedding N hN).measurable]
      rfl
    _ = carrierPushforward N := frickeCarrier_pushforward N hN

end
end ImbalancedChen.Part3.ActualFrickeQuotientMeasure20261026b
