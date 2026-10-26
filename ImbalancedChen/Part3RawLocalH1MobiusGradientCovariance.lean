import ImbalancedChen.Part3RawLocalH1MobiusPlateauTransport
import ImbalancedChen.Part3LocalSmoothWeakDerivativeUniqueness

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Weak gradients of a raw orbit-invariant locally H1 function transform by
the actual transpose-Jacobian. Actual weak transport is proved upstream;
here all-test local uniqueness identifies it with the original source
derivative. Only VALUE invariance is an input. For the actual quotient
pullback that value invariance is derived from Gamma orbit projection.
No form-domain membership, gradient equivariance or energy invariance is
assumed or inferred without the weak-test argument.
-/

namespace ImbalancedChen.Part3.RawLocalH1MobiusGradientCovariance20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open ActualPullbackLocalH1Transfer20261026b PlanarLocalWeakGradientExtraction20261026b
open ActualMobiusPairChartL2Transport20261026b RawLocalH1MobiusPlateauTransport20261026b
open LocalSmoothWeakDerivativeUniqueness20261026b Gamma0QuotientCellPushforward20261025a
open Gamma0ActualSmoothQuotientCore20261025a CanonicalPlanarL2UnitarySourceOnly

def RawWeakGradientOn (Ω : Set Plane) (F : Plane → ℂ)
    (gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2) : Prop :=
  ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
    ((∫ p, star (ψ p)*gx p) = -(∫ p, star (directional ex ψ p)*F p)) ∧
    ((∫ p, star (ψ p)*gy p) = -(∫ p, star (directional ey ψ p)*F p))

private theorem local_integrable_of_compact_L2 {K U : Set Plane}
    (hK : IsCompact K) (hU : IsOpen U) (hUK : U ⊆ K) {R : Plane → ℂ}
    (hR : MemLp R 2 ((volume : Measure Plane).restrict K)) : LocallyIntegrableOn R U volume := by
  have hi : MemLp (K.indicator R) 2 volume := (memLp_indicator_iff_restrict hK.measurableSet).2 hR
  have hl := (hi.locallyIntegrable (by norm_num)).locallyIntegrableOn U
  apply hl.congr
  exact (ae_restrict_iff' hU.measurableSet).mpr (Eventually.of_forall
    (fun p hp => by rw [Set.indicator_of_mem (hUK hp)]))

theorem raw_local_gradient_covariance {Ω Ωs U : Set Plane}
    (hΩ : MeasurableSet Ω) (hU : IsOpen U) {F χ : Plane → ℂ}
    (hlocal : HasCoordinateLocalH1On Ω F)
    (sx sy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hsource : RawWeakGradientOn Ωs F sx sy)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (A a b : ℝ) (ha : 0 < a) (hχbox : tsupport χ ⊆ planeBox A a b)
    (g : SL(2, ℤ)) {K : Set Plane} (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2)
    (hUK : U ⊆ K) (hUs : U ⊆ Ωs)
    (hone : ∀ q ∈ mobiusChart g '' K, χ =ᶠ[𝓝 q] (fun _ => (1 : ℂ)))
    (hvalue : ∀ p ∈ K, F (mobiusChart g p) = F p) :
    ∃ gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2,
      RawWeakGradientOn Ω F gx gy ∧
      (∀ᵐ p ∂(volume : Measure Plane), p ∈ U →
        sx p = pairRawJetX g gx gy p ∧ sy p = pairRawJetY g gx gy p) := by
  obtain ⟨gx,gy,hgrad,hv,hX,hY,htransport⟩ := raw_local_H1_mobius_transport hΩ hlocal
    hχ hχc hχΩ A a b ha hχbox g hK hKp hone
  have hliX := local_integrable_of_compact_L2 hK hU hUK hX
  have hliY := local_integrable_of_compact_L2 hK hU hUK hY
  have hliSx := ((Lp.memLp sx).locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hliSy := ((Lp.memLp sy).locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hmass {ψ : Plane → ℂ} (hs : tsupport ψ ⊆ U) (v : Plane) :
      (∫ p, star (directional v ψ p)*F p) =
        ∫ p, star (directional v ψ p)*F (mobiusChart g p) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by
      by_cases hp : p ∈ K
      · rw [hvalue p hp]
      · have hn : p ∉ tsupport ψ := fun ht => hp (hUK (hs ht))
        have hd : directional v ψ p = 0 := by
          simp only [directional,fderiv_of_notMem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]
        simp only [hd,star_zero,zero_mul])
  have hx : ∀ᵐ p ∂(volume : Measure Plane), p ∈ U → sx p = pairRawJetX g gx gy p := by
    apply local_ae_eq_of_smooth_test_pairings hU hliSx hliX
    intro ψ hψ hc hs
    obtain ⟨hsrc,_⟩ := hsource ψ hψ hc (hs.trans hUs)
    obtain ⟨htrans,_⟩ := htransport ψ hψ hc (hs.trans hUK)
    calc
      _ = -(∫ p, star (directional ex ψ p)*F p) := hsrc
      _ = -(∫ p, star (directional ex ψ p)*F (mobiusChart g p)) := congrArg Neg.neg (hmass hs ex)
      _ = _ := htrans.symm
  have hy : ∀ᵐ p ∂(volume : Measure Plane), p ∈ U → sy p = pairRawJetY g gx gy p := by
    apply local_ae_eq_of_smooth_test_pairings hU hliSy hliY
    intro ψ hψ hc hs
    obtain ⟨_,hsrc⟩ := hsource ψ hψ hc (hs.trans hUs)
    obtain ⟨_,htrans⟩ := htransport ψ hψ hc (hs.trans hUK)
    calc
      _ = -(∫ p, star (directional ey ψ p)*F p) := hsrc
      _ = -(∫ p, star (directional ey ψ p)*F (mobiusChart g p)) := congrArg Neg.neg (hmass hs ey)
      _ = _ := htrans.symm
  refine ⟨gx,gy,hgrad,?_⟩
  filter_upwards [hx,hy] with p hp hq
  intro hpU
  exact ⟨hp hpU,hq hpU⟩

/-- The raw VALUE invariance is a property of the actual quotient map,
with the exact existing rational chart, not an automorphy premise. -/
theorem actualPlanePullback_mobius_gamma0 (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (gamma : CongruenceSubgroup.Gamma0 N) {p : Plane} (hp : 0 < p.2) :
    actualPlanePullback N f (mobiusChart (gamma : SL(2, ℤ)) p) = actualPlanePullback N f p := by
  let z := chartLift p
  have hz : chartMap z = p := by
    rw [chartLift_of_positive hp]
    rfl
  have hmap : mobiusChart (gamma : SL(2, ℤ)) p = chartMap (gamma • z) :=
    mobiusChart_eq_actual (gamma : SL(2, ℤ)) hp
  calc
    _ = actualPlanePullback N f (chartMap (gamma • z)) := by rw [hmap]
    _ = f (orbitProjection N (gamma • z)) := actualPlanePullback_at_upper N f _
    _ = f (orbitProjection N z) := by rw [orbitProjection_smul]
    _ = actualPlanePullback N f (chartMap z) := (actualPlanePullback_at_upper N f z).symm
    _ = _ := by rw [hz]

end
end ImbalancedChen.Part3.RawLocalH1MobiusGradientCovariance20261026b
