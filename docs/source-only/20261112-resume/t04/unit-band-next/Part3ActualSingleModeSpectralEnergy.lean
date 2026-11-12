import ImbalancedChen.Part3ActualUnitBandSeedBudget
import ImbalancedChen.Part3OriginalMarkedWeakAdjoint
import Batteries.Tactic.OpenPrivate

/-! Compact-test Bessel inequalities at the actual quotient measure.
The ordinary continuous coefficients here use the manuscript's two
observation frames, and every singular incoming cusp of the same level. -/
namespace ImbalancedChen.Part3.ActualSingleModeSpectralEnergy20261112

noncomputable section
open Set Filter MeasureTheory Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualSignedPoincareEnvelope20261112 ActualUnitBandHeightSeeds20261112 ActualUnitBandSeedBudget20261112
open ActualContinuousResolution20261112 ActualMarkedHorocycleSupport20261112
open ActualCuspDenominatorClasses20261110 ActualContinuousPoincarePairing20261110
open ActualCriticalCuspEvaluation20261110 ActualContinuousClassFourier20261110
open OriginalContinuousPoincarePackets20261110 OriginalContinuousCuspGram20261110
open OriginalResidualPoincarePackets20261110 OriginalCuspidalPoincareTrace20261110
open ActualFullCuspEigenbasis20261026b ActualCuspBasisWhittakerCoefficients20261102
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a ActualCharacterCuspExpansion20261110
open NormalizedCuspCompactQuotientLp20261026b
open Gamma0GeneralCuspUnitPeriod20261025a ActualNativeResidualChannel20261110
open NormalizedCuspCompactPoincare20261026b NormalizedCuspCompactFourierFubini20261026b
open CompactCuspParabolicL220261025a AllNormalizedCuspAnnihilator20261026b
open SmoothZeroHeightSeedProfiles20261026b
open private periodized_support from ImbalancedChen.Part3ActualMarkedHorocycleSupport
open private seed_memLp from ImbalancedChen.Part3OriginalCuspidalPoincareTrace
open private seed_zero from ImbalancedChen.Part3OriginalResidualPoincarePackets
open private integrated_native from ImbalancedChen.Part3OriginalMarkedWeakAdjoint

private theorem discrete_coordinate (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (hm : m≠0)
    (ξ : SmoothHeightSeed) (i : actualCuspBasisIndex N (NeZero.pos N)) :
    inner ℂ (framedVector N g m ξ.toFun ξ.continuous ξ.compact ξ.positive)
      (actualCuspHilbertBasis N (NeZero.pos N) i : QuotientL2 N)=
      orderProbe m ξ.toFun (basisOrder N (NeZero.pos N) i)*basisR N (NeZero.pos N) i g m := by
  let f := physicalFrameSeed N (NeZero.pos N) g m ξ.toFun
  let B : QuotientL2 N := actualCuspHilbertBasis N (NeZero.pos N) i
  have h := framePoincare_pairing_eq_fourier N (NeZero.pos N) g m ξ.toFun ξ.continuous ξ.compact ξ.positive B B.memLp
  calc
    _ = ∫ q,star (complexPoincare N f q)*B q ∂carrierPushforward N := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [framedVector_ae N g m ξ.toFun ξ.continuous ξ.compact ξ.positive] with q hq
      simp only [RCLike.inner_apply',hq,Complex.star_def,B,f]
    _ = _ := by
      rw [h,orderProbe,← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [basisModes_ae_original N (NeZero.pos N) i g,ae_restrict_mem measurableSet_Ioi] with y hy hpos
      rw [← hy m,basisMode_eq_normalizedR N (NeZero.pos N) i g hm hpos]
      simp only [orderRadial,Complex.real_smul]
      ring

theorem compact_discrete (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (hm : m≠0)
    (ξ : SmoothHeightSeed) (S : Finset (actualCuspBasisIndex N (NeZero.pos N))) :
    (∑ i∈S,‖orderProbe m ξ.toFun (basisOrder N (NeZero.pos N) i)*basisR N (NeZero.pos N) i g m‖^2)≤
      ‖framedVector N g m ξ.toFun ξ.continuous ξ.compact ξ.positive‖^2 := by
  classical
  let B := actualCuspHilbertBasis N (NeZero.pos N)
  let V := framedVector N g m ξ.toFun ξ.continuous ξ.compact ξ.positive
  have orth : Orthonormal ℂ (fun i => (B i : QuotientL2 N)) := orthonormal_iff_ite.mpr (fun i j =>
    (orthonormal_iff_ite.mp B.orthonormal) i j)
  have H := orth.sum_inner_products_le (s := S) V
  simpa only [← discrete_coordinate N g m hm ξ,norm_inner_symm (𝕜 := ℂ) (x := V)] using H

def continuousMass (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (t : ℝ) : ℝ :=
  (4*Real.pi)⁻¹ * ∑ a : Parameters N,‖nativeR a one m t‖^2

theorem continuousMass_nonneg (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (t : ℝ) :
    0≤continuousMass N one m t := mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem compact_continuous (N : ℕ) [NeZero N] (one : Bool) (m : ℤ) (hm : m≠0)
    (ξ : SmoothHeightSeed) :
    let K := fun t : ℝ => ‖orderProbe m ξ.toFun ((t:ℂ)*I)‖^2*continuousMass N one m t
    Integrable K ∧ (∫ t,K t)≤‖framedVector N (originalFrame one) m ξ.toFun ξ.continuous ξ.compact ξ.positive‖^2 := by
  let g := originalFrame one
  let X := originalPoincare N one m ξ.toFun
  have hx : MemLp X 2 (carrierPushforward N) := seed_memLp N one m ξ.toFun ξ.continuous ξ.compact ξ.positive
  let V := hx.toLp X
  let F := framedVector N g m ξ.toFun ξ.continuous ξ.compact ξ.positive
  have E : X=complexPoincare N (physicalFrameSeed N (NeZero.pos N) g m ξ.toFun) :=
    original_eq_framed N one m ξ.toFun ξ.compact ξ.positive
  have FV : V=F := by
    apply Lp.ext
    apply hx.coeFn_toLp.trans
    rw [E]
    exact (framedVector_ae N g m ξ.toFun ξ.continuous ξ.compact ξ.positive).symm
  have cx : supportedInQuotientCompact N X := by
    rw [E]
    exact ⟨_,(cuspSupportK_isCompact ξ.toFun ξ.compact ξ.positive).image (frameAction_continuous N _ g),
      periodized_support N _ (physicalFrameSeed_support N _ g m ξ.toFun)⟩
  have z : (ℂ ∙ constantL2 N).starProjection V=0 := by
    rw [actual_residual_projection N (nativeFrameOrbit N g),integral_congr_ae hx.coeFn_toLp,
      seed_zero N one m hm ξ.toFun ξ.continuous ξ.compact ξ.positive,mul_zero,zero_smul]
  let K := fun t : ℝ => ‖orderProbe m ξ.toFun ((t:ℂ)*I)‖^2*continuousMass N one m t
  let G := fun t => nativeProduct N (fun a => spectrum N X a t) (fun a => spectrum N X a t)
  have phys := integrated_native N hx hx cx cx z z
  have spec (a : Parameters N) (t : ℝ) : spectrum N X a t=orderProbe m ξ.toFun ((t:ℂ)*I)*nativeR a one m t := by
    have eqorder : criticalPoint t-1/2=(t:ℂ)*I := by unfold criticalPoint; ring
    simpa only [spectrum,X,show radialProbe m ξ.toFun t=orderProbe m ξ.toFun (criticalPoint t-1/2) from rfl,
      eqorder] using (original_spatial_pairing a one m hm ξ.toFun ξ.continuous ξ.compact ξ.positive t).2
  have ident (t : ℝ) : G t=(K t:ℂ) := by
    let P := orderProbe m ξ.toFun ((t:ℂ)*I)
    have row (a : Parameters N) : star (spectrum N X a t)*spectrum N X a t/(4*(Real.pi:ℂ)) =
        (‖P‖^2*((4*Real.pi)⁻¹*‖nativeR a one m t‖^2):ℝ) := by
      rw [mul_comm (star _) _,Complex.mul_conj',spec,norm_mul,mul_pow]
      push_cast
      dsimp only [P]
      ring
    simpa only [G,nativeProduct,row,← Complex.ofReal_sum,K,continuousMass,Finset.mul_sum]
  have reeq (t : ℝ) : (G t).re=K t := by rw [ident,Complex.ofReal_re]
  have hG : Integrable G := phys.1
  refine ⟨hG.re.congr (ae_of_all _ reeq),?_⟩
  have I := phys.2
  rw [nativeSynthesis_analysis_eq_projection] at I
  calc
    (∫ t,K t) = (∫ t,G t).re := by
      rw [← integral_re hG]
      exact integral_congr_ae (ae_of_all _ (fun t => (reeq t).symm))
    _ = (inner ℂ V ((centeredSpace N).starProjection V)).re := by rw [I]
    _ ≤ ‖V‖^2 := (Complex.re_le_norm _).trans ((norm_inner_le_norm V _).trans (by
      rw [sq]; exact mul_le_mul_of_nonneg_left ((centeredSpace N).norm_starProjection_apply_le V) (norm_nonneg _)))
    _ = ‖F‖^2 := by rw [FV]

end
end ImbalancedChen.Part3.ActualSingleModeSpectralEnergy20261112
