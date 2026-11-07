import ImbalancedChen.Part3CompactH1MobiusWeakTransport
import ImbalancedChen.Part3CoordinateLocalH1CompactProducts

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual local H1 Mobius transport for a merely locally L2 raw function.
A legal compact smooth cutoff equal to one on a neighborhood of the
actual compact image produces a genuine global compact H1 jet. Its value
and both derivatives are proved to be the original raw fields on that
image. The established compact-H1 weak chain rule then transfers back to
the raw fields, with all source L2 and L1 claims proved. The plateau is
ordinary explicit geometry, not a transported-gradient assumption.
-/

namespace ImbalancedChen.Part3.RawLocalH1MobiusPlateauTransport20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open WeakH1ProductMollifierDerivative20261026a LocalWeakH1CutoffProduct20261026b
open ActualPullbackLocalH1Transfer20261026b PlanarLocalWeakGradientExtraction20261026b
open ActualMobiusPairChartL2Transport20261026b CompactH1MobiusWeakTransport20261026b

theorem raw_local_H1_mobius_transport {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    {F χ : Plane → ℂ} (hlocal : HasCoordinateLocalH1On Ω F)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (A a b : ℝ) (ha : 0 < a) (hχbox : tsupport χ ⊆ planeBox A a b)
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    (hone : ∀ q ∈ mobiusChart g '' K, χ =ᶠ[𝓝 q] (fun _ => (1 : ℂ))) :
    ∃ gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2,
      (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
        ((∫ p, star (ψ p)*gx p) = -(∫ p, star (directional ex ψ p)*F p)) ∧
        ((∫ p, star (ψ p)*gy p) = -(∫ p, star (directional ey ψ p)*F p))) ∧
      MemLp (fun p => F (mobiusChart g p)) 2 ((volume : Measure Plane).restrict K) ∧
      MemLp (pairRawJetX g gx gy) 2 ((volume : Measure Plane).restrict K) ∧
      MemLp (pairRawJetY g gx gy) 2 ((volume : Measure Plane).restrict K) ∧
      ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ K →
        ((∫ p, star (ψ p)*pairRawJetX g gx gy p) =
          -(∫ p, star (directional ex ψ p)*F (mobiusChart g p))) ∧
        ((∫ p, star (ψ p)*pairRawJetY g gx gy p) =
          -(∫ p, star (directional ey ψ p)*F (mobiusChart g p))) := by
  obtain ⟨hF,gx,gy,hgrad⟩ := hlocal
  have hG : MemLp (Ω.indicator F) 2 volume := (memLp_indicator_iff_restrict hΩ).2 hF
  have hgrad0 : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ((∫ p, star (ψ p)*gx p) = -(∫ p, star (directional ex ψ p)*Ω.indicator F p)) ∧
      ((∫ p, star (ψ p)*gy p) = -(∫ p, star (directional ey ψ p)*Ω.indicator F p)) := by
    intro ψ hψ hc hs
    have hmass (v : Plane) : (∫ p, star (directional v ψ p)*Ω.indicator F p) =
        ∫ p, star (directional v ψ p)*F p := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun p => by
        by_cases hp : p ∈ Ω
        · rw [Set.indicator_of_mem hp]
        · have hn : p ∉ tsupport ψ := fun ht => hp (hs ht)
          have hd : directional v ψ p = 0 := by
            simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
          simp only [hd,star_zero,zero_mul])
    obtain ⟨hx,hy⟩ := hgrad ψ hψ hc hs
    exact ⟨by simpa only [hmass ex] using hx,by simpa only [hmass ey] using hy⟩
  let J := cutoffJet hG gx gy hχ hχc hχΩ hgrad0
  have hsupports := cutoffJet_supports hG gx gy hχ hχc hχΩ hgrad0
  have hpoint (q : Plane) (hq : q ∈ mobiusChart g '' K) :
      J.value q = F q ∧ J.dx q = gx q ∧ J.dy q = gy q := by
    have he := hone q hq
    have hχq : χ q = 1 := he.eq_of_nhds
    have hqΩ : q ∈ Ω := hχΩ (subset_closure (show q ∈ Function.support χ from by simp [hχq]))
    have hd (v : Plane) : directional v χ q = 0 := by
      unfold directional
      rw [he.fderiv_eq]
      simp
    simp only [J,cutoffJet,productDerivative,Set.indicator_of_mem hqΩ,hχq,hd,
      zero_mul,one_mul,zero_add,true_and]
  have hxcompact : HasCompactSupport J.dx :=
    hχc.of_isClosed_subset (isClosed_tsupport _) hsupports.2.1
  have hycompact : HasCompactSupport J.dy :=
    hχc.of_isClosed_subset (isClosed_tsupport _) hsupports.2.2
  obtain ⟨hJv,hJx,hJy,htransport⟩ := compactH1_mobius_weak_transport J hxcompact hycompact
    A a b ha (hsupports.1.trans hχbox) g hK hKp
  have hvalue (p : Plane) (hp : p ∈ K) : J.value (mobiusChart g p) = F (mobiusChart g p) :=
    (hpoint _ ⟨p,hp,rfl⟩).1
  have hxpoint (p : Plane) (hp : p ∈ K) :
      pairRawJetX g J.dx J.dy p = pairRawJetX g gx gy p := by
    obtain ⟨hv,hx,hy⟩ := hpoint _ ⟨p,hp,rfl⟩
    simp only [pairRawJetX,hx,hy]
  have hypoint (p : Plane) (hp : p ∈ K) :
      pairRawJetY g J.dx J.dy p = pairRawJetY g gx gy p := by
    obtain ⟨hv,hx,hy⟩ := hpoint _ ⟨p,hp,rfl⟩
    simp only [pairRawJetY,hx,hy]
  have hvalueLp : MemLp (fun p => F (mobiusChart g p)) 2 ((volume : Measure Plane).restrict K) :=
    hJv.ae_eq ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall hvalue))
  have hXLp : MemLp (pairRawJetX g gx gy) 2 ((volume : Measure Plane).restrict K) :=
    hJx.ae_eq ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall hxpoint))
  have hYLp : MemLp (pairRawJetY g gx gy) 2 ((volume : Measure Plane).restrict K) :=
    hJy.ae_eq ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall hypoint))
  refine ⟨gx,gy,hgrad,hvalueLp,hXLp,hYLp,?_⟩
  intro ψ hψ hc hs
  have hright (v : Plane) : (∫ p, star (directional v ψ p)*J.value (mobiusChart g p)) =
      ∫ p, star (directional v ψ p)*F (mobiusChart g p) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [hvalue p hp]
      · have hn : p ∉ tsupport ψ := fun ht => hp (hs ht)
        have hd : directional v ψ p = 0 := by
          simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
        simp only [hd,star_zero,zero_mul])
  have hleftX : (∫ p, star (ψ p)*pairRawJetX g J.dx J.dy p) =
      ∫ p, star (ψ p)*pairRawJetX g gx gy p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [hxpoint p hp]
      · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht)),star_zero,zero_mul])
  have hleftY : (∫ p, star (ψ p)*pairRawJetY g J.dx J.dy p) =
      ∫ p, star (ψ p)*pairRawJetY g gx gy p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [hypoint p hp]
      · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht)),star_zero,zero_mul])
  obtain ⟨hX,hY⟩ := htransport ψ hψ hc hs
  exact ⟨by simpa only [hleftX,hright ex] using hX,
    by simpa only [hleftY,hright ey] using hY⟩

end
end ImbalancedChen.Part3.RawLocalH1MobiusPlateauTransport20261026b
