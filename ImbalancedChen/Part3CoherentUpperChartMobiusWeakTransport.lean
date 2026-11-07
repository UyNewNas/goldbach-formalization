import ImbalancedChen.Part3CoherentUpperChartH1CompactProduct
import ImbalancedChen.Part3CompactH1MobiusWeakTransport
import ImbalancedChen.Part3ActualMobiusImageCutoffPlateau

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Every coherent whole-upper-chart weak gradient transports through the
actual Mobius map on every positive compact chart. The actual image
plateau and all support/height data are PRODUCED from compact geometry.
The compact H1 jet retains the SAME literal raw gradient functions.
No cutoff, approximation, weak chain rule or gradient-covariance premise
remains. Ordinary L2 is required only on compact positive sets.
-/

namespace ImbalancedChen.Part3.CoherentUpperChartMobiusWeakTransport20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open LocalWeakH1CutoffProduct20261026b WeakH1ProductMollifierDerivative20261026a
open CoherentUpperChartH1CompactProduct20261026b CompactH1MobiusWeakTransport20261026b
open ActualMobiusPairChartL2Transport20261026b ActualMobiusImageCutoffPlateau20261026b
open CanonicalTensorHyperbolicLaplacianForm20261024z

theorem coherent_upperChart_mobius_weak_transport (F Gx Gy : Plane → ℂ)
    (hb : ∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp F 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gx 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gy 2 ((volume : Measure Plane).restrict K))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p)*Gx p) = -(∫ p, star (directional ex ψ p)*F p)) ∧
      ((∫ p, star (ψ p)*Gy p) = -(∫ p, star (directional ey ψ p)*F p)))
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) :
    MemLp (fun p => F (mobiusChart g p)) 2 ((volume : Measure Plane).restrict K) ∧
    MemLp (pairRawJetX g Gx Gy) 2 ((volume : Measure Plane).restrict K) ∧
    MemLp (pairRawJetY g Gx Gy) 2 ((volume : Measure Plane).restrict K) ∧
    ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ K →
      ((∫ p, star (ψ p)*pairRawJetX g Gx Gy p) =
        -(∫ p, star (directional ex ψ p)*F (mobiusChart g p))) ∧
      ((∫ p, star (ψ p)*pairRawJetY g Gx Gy p) =
        -(∫ p, star (directional ey ψ p)*F (mobiusChart g p))) := by
  obtain ⟨Ω,χ,A,a,b,hΩ,hΩm,hΩp,hχ,hχc,hχΩ,ha,hχbox,hone⟩ :=
    exists_mobius_image_cutoff_plateau g hK hKp
  obtain ⟨J,hJv,hJx,hJy,hSv,hSx,hSy⟩ := exists_coherent_compact_H1_product F Gx Gy hb hw
    hχ hχc (hχΩ.trans hΩp)
  have hJxc : HasCompactSupport J.dx := hχc.of_isClosed_subset (isClosed_tsupport _) hSx
  have hJyc : HasCompactSupport J.dy := hχc.of_isClosed_subset (isClosed_tsupport _) hSy
  have hpoint (q : Plane) (hq : q ∈ mobiusChart g '' K) :
      J.value q = F q ∧ J.dx q = Gx q ∧ J.dy q = Gy q := by
    have he := hone q hq
    have hχq : χ q = 1 := he.eq_of_nhds
    have hd (v : Plane) : directional v χ q = 0 := by
      unfold directional
      rw [he.fderiv_eq]
      simp
    rw [hJv,hJx,hJy]
    simp only [productDerivative,hχq,hd,zero_mul,one_mul,zero_add,and_self]
  obtain ⟨hv,hx,hy,ht⟩ := compactH1_mobius_weak_transport J hJxc hJyc A a b ha
    (hSv.trans hχbox) g hK hKp
  have heV (p : Plane) (hp : p ∈ K) : J.value (mobiusChart g p) = F (mobiusChart g p) :=
    (hpoint _ ⟨p,hp,rfl⟩).1
  have heX (p : Plane) (hp : p ∈ K) : pairRawJetX g J.dx J.dy p = pairRawJetX g Gx Gy p := by
    obtain ⟨hv,hx,hy⟩ := hpoint _ ⟨p,hp,rfl⟩
    simp only [pairRawJetX,hx,hy]
  have heY (p : Plane) (hp : p ∈ K) : pairRawJetY g J.dx J.dy p = pairRawJetY g Gx Gy p := by
    obtain ⟨hv,hx,hy⟩ := hpoint _ ⟨p,hp,rfl⟩
    simp only [pairRawJetY,hx,hy]
  refine ⟨hv.ae_eq ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall heV)),
    hx.ae_eq ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall heX)),
    hy.ae_eq ((ae_restrict_iff' hK.measurableSet).mpr (Eventually.of_forall heY)),?_⟩
  intro ψ hψ hc hs
  have hmass (v : Plane) : (∫ p, star (directional v ψ p)*J.value (mobiusChart g p)) =
      ∫ p, star (directional v ψ p)*F (mobiusChart g p) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [heV p hp]
      · have hn : p ∉ tsupport ψ := fun ht => hp (hs ht)
        have hd : directional v ψ p = 0 := by
          simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
        simp only [hd,star_zero,zero_mul])
  have hpairX : (∫ p, star (ψ p)*pairRawJetX g J.dx J.dy p) =
      ∫ p, star (ψ p)*pairRawJetX g Gx Gy p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [heX p hp]
      · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht)),star_zero,zero_mul])
  have hpairY : (∫ p, star (ψ p)*pairRawJetY g J.dx J.dy p) =
      ∫ p, star (ψ p)*pairRawJetY g Gx Gy p := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [heY p hp]
      · simp only [image_eq_zero_of_notMem_tsupport (fun ht => hp (hs ht)),star_zero,zero_mul])
  obtain ⟨hX,hY⟩ := ht ψ hψ hc hs
  exact ⟨by simpa only [hpairX,hmass ex] using hX,
    by simpa only [hpairY,hmass ey] using hY⟩

end
end ImbalancedChen.Part3.CoherentUpperChartMobiusWeakTransport20261026b
