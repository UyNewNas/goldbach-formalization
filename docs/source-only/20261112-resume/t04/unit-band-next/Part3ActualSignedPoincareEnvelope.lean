import ImbalancedChen.Part3OriginalProjectedContinuousCovariance
import ImbalancedChen.Part3Gamma0CompactTensorPoincareLocalFinite
import Batteries.Tactic.OpenPrivate

/-! Domination of an actual signed Poincaré series by its positive
zero-mode envelope at the very same normalized observation frame. -/
namespace ImbalancedChen.Part3.ActualSignedPoincareEnvelope20261112

noncomputable section
open Set Filter MeasureTheory Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane BigOperators Topology
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactSeedQuotientL2Budget20261025a CompactCuspParabolicL220261025a
open GammaInfinityTranslationStrip20261025a ActualInfinityKloostermanSeed20261025a
open NormalizedCuspCompactQuotientLp20261026b NormalizedCuspCompactPoincare20261026b
open NormalizedCuspCompactFourierFubini20261026b AllNormalizedCuspAnnihilator20261026b
open SmoothZeroHeightSeedProfiles20261026b OriginalFrameZeroSeedMellin20261027 NativeCuspCompactMellinSynthesis20261027
open ActualIncompleteEisensteinTransform20261110 ActualIncompleteResidualContour20261110
open ActualIncompleteMellinFactors20261110 ActualHorocycleSynthesisBound20261112
open ActualResidualVolumeNormalization20261110

def framedVector (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hp : tsupport ψ ⊆ Ioi (0 : ℝ)) : QuotientL2 N :=
  (framePoincare_memLp_two N (NeZero.pos N) g m ψ hψ hc hp).toLp _

theorem framedVector_ae (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hp : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    framedVector N g m ψ hψ hc hp =ᵐ[carrierPushforward N]
      complexPoincare N (physicalFrameSeed N (NeZero.pos N) g m ψ) :=
  (framePoincare_memLp_two N (NeZero.pos N) g m ψ hψ hc hp).coeFn_toLp

theorem framed_pointwise (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (ψ : ℝ → ℂ)
    (η : SmoothHeightSeed) (realη : ∀ y,η.toFun y=(‖η.toFun y‖ : ℂ))
    (maj : ∀ y,‖ψ y‖≤‖η.toFun y‖) (q : Gamma0OrbitSpace N) :
    ‖complexPoincare N (physicalFrameSeed N (NeZero.pos N) g m ψ) q‖ ≤
      ‖zeroPoincare N g η.toHeightSeed q‖ := by
  classical
  let F := physicalFrameSeed N (NeZero.pos N) g m ψ
  let G := physicalFrameSeed N (NeZero.pos N) g 0 η.toFun
  have R0 (z : ℍ) : cuspStripSeed 0 η.toFun z=(‖cuspStripSeed 0 η.toFun z‖ : ℂ) := by
    by_cases hz : z∈strip
    · simpa [cuspStripSeed,hz,fourierRadialSeed] using realη z.im
    · simp [cuspStripSeed,hz]
  have R (z : ℍ) : G z=(‖G z‖ : ℂ) := R0 _
  have D0 (z : ℍ) : ‖cuspStripSeed m ψ z‖≤‖cuspStripSeed 0 η.toFun z‖ := by
    by_cases hz : z∈strip
    · simpa only [cuspStripSeed,indicator_of_mem hz,fourierRadialSeed_norm] using maj z.im
    · simp [cuspStripSeed,hz]
  have D (z : ℍ) : ‖F z‖≤‖G z‖ := D0 _
  change ‖complexPoincare N F q‖≤‖complexPoincare N G q‖
  by_cases hq : q ∈ Set.range (reducedProjection N)
  · obtain ⟨z,rfl⟩ := hq
    obtain ⟨U,hU,S,hS⟩ := compact_seed_locally_finite N G
      ((cuspSupportK_isCompact η.toFun η.compact η.positive).image (frameAction_continuous N _ g))
      (physicalFrameSeed_support N _ g 0 η.toFun) (z : ℍ)
    have HG (b) (hb : b∉S) : translatedSeed N G b z=0 := hS z (mem_of_mem_nhds hU) b hb
    have HF (b) (hb : b∉S) : translatedSeed N F b z=0 := by
      apply norm_eq_zero.mp
      exact le_antisymm ((D _).trans_eq (by change ‖translatedSeed N G b z‖=0; rw [HG b hb,norm_zero])) (norm_nonneg _)
    rw [complexPoincare_projection,complexPoincare_projection,complexSeedTrace,complexSeedTrace,
      tsum_eq_sum HF,tsum_eq_sum HG]
    have pos : (∑ b∈S,translatedSeed N G b z) = ((∑ b∈S,‖translatedSeed N G b z‖ : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl (fun b _ => R _)
    rw [pos,Complex.norm_real,Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun b _ => D _))
  · rw [complexPoincare_off_section N F hq,complexPoincare_off_section N G hq]

/-- All normalized frames and integer modes. The coefficient of the
mean term is supplied by the actual constant residue of this level. -/
theorem signed_envelope_norm_sq (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (m : ℤ) (ψ : ℝ → ℂ)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hp : tsupport ψ ⊆ Ioi (0 : ℝ))
    (η : SmoothHeightSeed) (realη : ∀ y,η.toFun y=(‖η.toFun y‖ : ℂ)) (maj : ∀ y,‖ψ y‖≤‖η.toFun y‖) :
    ‖framedVector N g m ψ hψ hc hp‖^2≤2*‖logVector η‖^2+|actualVolume N|⁻¹*‖moment η.toHeightSeed 0‖^2 := by
  let v := framedVector N g m ψ hψ hc hp
  let Z := frameZeroSeedL2 N (NeZero.pos N) g η.toHeightSeed
  have bound : ‖v‖≤‖Z‖ := Lp.norm_le_norm_of_ae_le (by
    filter_upwards [framedVector_ae N g m ψ hψ hc hp,original_frameZeroSeedL2_ae_representative N (NeZero.pos N) g η] with q a b
    rw [show v q=_ from a,show Z q=_ from b]
    exact framed_pointwise N g m ψ η realη maj q)
  have A := centered_inner N Z Z
  change inner ℂ (centeredSeed N g η) (centeredSeed N g η)=_ at A
  rw [← residue_is_physical N g g η η,inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at A
  have E : ‖Z‖^2 ≤ ‖centeredSeed N g η‖^2+‖residue N η η‖ := by
    have J := congrArg Complex.re A
    simp only [Complex.sub_re,← Complex.ofReal_pow,Complex.ofReal_re] at J
    linarith only [J,Complex.re_le_norm (residue N η η)]
  have c := centered_bound N g η
  have cs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr c
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at cs
  have J : ‖moment η.toHeightSeed 0‖=‖heightMellin η.toHeightSeed 1‖ := by
    rw [moment_conjugated,star_zero,sub_zero,norm_star]
  have res : ‖residue N η η‖=|actualVolume N|⁻¹*‖moment η.toHeightSeed 0‖^2 := by
    rw [residue,norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,← J]
    ring
  exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr bound).trans
    (E.trans (by rw [res]; linarith only [cs]))

end
end ImbalancedChen.Part3.ActualSignedPoincareEnvelope20261112
