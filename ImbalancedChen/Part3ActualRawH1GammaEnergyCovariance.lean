import ImbalancedChen.Part3RawLocalH1MobiusGradientCovariance
import ImbalancedChen.Part3ActualMobiusRawJetL2Transport

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual raw Gamma quotient weak gradients have AE hyperbolic energy
covariance on every legal pair of local charts. The weak-gradient chain
is proved upstream from genuine H1 density and actual Jacobian transport;
value invariance here is proved from the orbit quotient. Exact actual
height compensation then cancels the conformal factor for the RAW fields.
No form-domain membership or energy-invariance premise appears.
-/

namespace ImbalancedChen.Part3.ActualRawH1GammaEnergyCovariance20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a MaassWeakOperatorCore20261024zz
open CompactProductKernelSixJet20261025a CompactC2ProductMollifier20261026a
open ActualPullbackLocalH1Transfer20261026b PlanarLocalWeakGradientExtraction20261026b
open ActualMobiusPairChartL2Transport20261026b ActualMobiusRawJetL2Transport20261026b
open ActualMobiusConformalTwoJet20261025a RawLocalH1MobiusGradientCovariance20261026b
open Gamma0ActualSmoothQuotientCore20261025a

def rawHyperbolicEnergy (gx gy : Plane → ℂ) (p : Plane) : ℝ :=
  p.2^2*(‖gx p‖^2+‖gy p‖^2)

/-- Exact compensation for arbitrary raw jets, with the genuine actual
rational chart and the genuine (cz+d)^-2 first-derivative factor. -/
theorem pairRawJet_hyperbolic_energy (g : SL(2, ℤ)) (gx gy : Plane → ℂ)
    {p : Plane} (hp : 0 < p.2) :
    rawHyperbolicEnergy (pairRawJetX g gx gy) (pairRawJetY g gx gy) p =
      rawHyperbolicEnergy gx gy (mobiusChart g p) := by
  let z : UpperHalfPlane := ⟨complexOfPair p,hp⟩
  have hz : chartLift p = z := by rw [chartLift_of_positive hp]; rfl
  have hmap := mobiusChart_eq_actual g hp
  rw [hz] at hmap
  have hi : (mobiusChart g p).2 = (g • z).im := congrArg Prod.snd hmap
  have hh : p.2^2*Complex.normSq (factor g (complexOfPair p)) = (mobiusChart g p).2^2 := by
    rw [hi]
    exact height_sq_mul_normSq_factor g z
  unfold rawHyperbolicEnergy pairRawJetX pairRawJetY
  rw [conformal_raw_jet_norm_sq,← mul_assoc,hh]

/-- The actual quotient VALUE invariance forces local raw-gradient and
hyperbolic-energy covariance by the proved weak-test uniqueness argument.
The supplied local regularity is ordinary raw H1, not a form-domain claim. -/
theorem actual_raw_local_gradient_energy_covariance (N : ℕ) [NeZero N]
    (f : QuotientL2 N) {Ω Ωs U : Set Plane} (hΩ : MeasurableSet Ω) (hU : IsOpen U)
    (hlocal : HasCoordinateLocalH1On Ω (actualPlanePullback N f))
    (sx sy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2)
    (hsource : RawWeakGradientOn Ωs (actualPlanePullback N f) sx sy)
    {χ : Plane → ℂ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω)
    (A a b : ℝ) (ha : 0 < a) (hχbox : tsupport χ ⊆ planeBox A a b)
    (gamma : CongruenceSubgroup.Gamma0 N) {K : Set Plane}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) (hUK : U ⊆ K) (hUs : U ⊆ Ωs)
    (hone : ∀ q ∈ mobiusChart (gamma : SL(2, ℤ)) '' K,
      χ =ᶠ[𝓝 q] (fun _ => (1 : ℂ))) :
    ∃ gx gy : PlanarLocalWeakGradientExtraction20261026b.PlaneL2,
      RawWeakGradientOn Ω (actualPlanePullback N f) gx gy ∧
      (∀ᵐ p ∂(volume : Measure Plane), p ∈ U →
        (sx p = pairRawJetX (gamma : SL(2, ℤ)) gx gy p ∧
          sy p = pairRawJetY (gamma : SL(2, ℤ)) gx gy p) ∧
        rawHyperbolicEnergy sx sy p = rawHyperbolicEnergy gx gy
          (mobiusChart (gamma : SL(2, ℤ)) p)) := by
  obtain ⟨gx,gy,hgrad,hcov⟩ := raw_local_gradient_covariance hΩ hU hlocal sx sy hsource
    hχ hχc hχΩ A a b ha hχbox (gamma : SL(2, ℤ)) hK hKp hUK hUs hone
    (fun p hp => actualPlanePullback_mobius_gamma0 N f gamma (hKp p hp))
  refine ⟨gx,gy,hgrad,?_⟩
  filter_upwards [hcov] with p hp
  intro hpU
  obtain ⟨hx,hy⟩ := hp hpU
  refine ⟨⟨hx,hy⟩,?_⟩
  change p.2^2*(‖sx p‖^2+‖sy p‖^2) = _
  rw [hx,hy]
  exact pairRawJet_hyperbolic_energy (gamma : SL(2, ℤ)) gx gy (hKp p (hUK hpU))

end
end ImbalancedChen.Part3.ActualRawH1GammaEnergyCovariance20261026b
