import ImbalancedChen.Part3ActualLogHorocycleAdjoint
import ImbalancedChen.Part3Gamma0ActualHighCuspTail
import ImbalancedChen.Part3Gamma0DegeneracyMap
import ImbalancedChen.Part3OriginalResidualPoincarePackets

/-! Each literal finite packet vanishes in all sufficiently high
horocycles of each native frame. The estimate uses the actual integral
bottom-left entry, the normalized width and the compact support in H. -/
namespace ImbalancedChen.Part3.ActualMarkedHorocycleSupport20261112

noncomputable section
open Set Filter MeasureTheory Complex UpperHalfPlane Matrix
open scoped MatrixGroups UpperHalfPlane Pointwise BigOperators
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0CarrierMeasurableInverse20261025a Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0EffectiveActionKernel20261024z Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0GeneralCuspWidth20261025a Gamma0GeneralCuspUnitPeriod20261025a
open Gamma0DegeneracyMapSourceOnly Gamma0ActualHighCuspTail20261025a
open Gamma0ParabolicBottomRow20261025a CompactCuspParabolicL220261025a
open Gamma0CompactSeedQuotientL2Budget20261025a
open NormalizedCuspCompactQuotientLp20261026b NormalizedCuspCompactPoincare20261026b
open NormalizedCuspCompactFourierFubini20261026b NormalizedCuspFourierRepresentative20261026b
open ActualContinuousPoincarePairing20261110 OriginalContinuousPoincarePackets20261110
open ActualHorocycleSynthesisBound20261112 ActualLogHorocycleAdjoint20261112
open Gamma0ActualConstantMode20261025a

def supportedInQuotientCompact (N : ℕ) (V : Gamma0OrbitSpace N → ℂ) : Prop :=
  ∃ K : Set ℍ, IsCompact K ∧ Function.support V ⊆ orbitProjection N '' K

private theorem periodized_support (N : ℕ) [NeZero N] (f : ℍ → ℂ) {K : Set ℍ}
    (hK : Function.support f ⊆ K) :
    Function.support (complexPoincare N f) ⊆ orbitProjection N '' K := by
  intro q hq
  by_cases H : q ∈ range (reducedProjection N)
  · obtain ⟨z,rfl⟩ := H
    rw [Function.mem_support,complexPoincare_projection] at hq
    have ex : ∃ c : effectiveGamma0 N, translatedSeed N f c z ≠ 0 := by
      by_contra e
      push_neg at e
      exact hq (by simp [complexSeedTrace,e])
    obtain ⟨c,hc⟩ := ex
    exact ⟨effectiveMatrixAction N c z,hK hc,orbitProjection_smul N (effectiveRepresentative N c) z⟩
  · exact False.elim (hq (complexPoincare_off_section N f H))

theorem marked_support (N : ℕ) [NeZero N] (one : Bool) (S : Finset ℕ) (w : ℕ → ℂ)
    (ind : ℕ → ℤ) (hn : ∀ b ∈ S,ind b ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) (hp : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    supportedInQuotientCompact N (packet N one S w ind ψ) := by
  classical
  let g := originalFrame one
  let K := fun b => frameAction N (NeZero.pos N) g '' cuspSupportK (scaledSeed (ind b) ψ)
  have cK (b : ℕ) (hb : b ∈ S) : IsCompact (K b) := by
    obtain ⟨_,c,p⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hp
    exact (cuspSupportK_isCompact _ c p).image (frameAction_continuous N _ _)
  refine ⟨⋃ b ∈ S,K b,S.finite_toSet.isCompact_biUnion (fun b hb => cK b hb),?_⟩
  intro q hq
  have ex : ∃ b ∈ S,originalPoincare N one (ind b) (scaledSeed (ind b) ψ) q ≠ 0 := by
    by_contra e
    push_neg at e
    exact hq (by unfold packet; apply Finset.sum_eq_zero; intro b hb; rw [e b hb,mul_zero])
  obtain ⟨b,hb,u⟩ := ex
  obtain ⟨_,c,p⟩ := scaled_test (ind b) (hn b hb) ψ hψ hc hp
  rw [original_eq_framed N one (ind b) _ c p] at u
  obtain ⟨z,hz,hq'⟩ := periodized_support N _ (physicalFrameSeed_support N _ g (ind b) _) u
  exact ⟨z,mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,hz⟩⟩,hq'⟩

private theorem high_outside (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {K : Set ℍ} (hK : IsCompact K) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : ℍ, Y < z.im →
      orbitProjection N (frameAction N (NeZero.pos N) g z) ∉ orbitProjection N '' K := by
  rcases K.eq_empty_or_nonempty with e|ne
  · exact ⟨1,zero_lt_one,by simp [e]⟩
  obtain ⟨lo,hlo,L⟩ := hK.exists_isMinOn ne UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨hi,hhi,H⟩ := hK.exists_isMaxOn ne UpperHalfPlane.continuous_im.continuousOn
  let w := cuspWidth N g
  have hw := cuspWidth_pos N (NeZero.pos N) g
  have hwr : 0 < (w : ℝ) := by exact_mod_cast hw
  let Y := max hi.im lo.im⁻¹/(w : ℝ)
  refine ⟨Y,div_pos (lt_of_lt_of_le hi.im_pos (le_max_left _ _)) hwr,?_⟩
  intro z hz he
  obtain ⟨v,hv,e⟩ := he
  obtain ⟨γ,hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact e :
    MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ v (frameAction N (NeZero.pos N) g z))
  let u := widthDiagonal w hw • z
  let A := (γ : SL(2,ℤ))*g
  have av : A • u=v := by
    rw [← hγ]
    change ((γ : SL(2,ℤ))*g) • (widthDiagonal w hw • z) =
      (γ : SL(2,ℤ)) • ((integralReal g*widthDiagonal w hw) • z)
    rw [mul_smul,mul_smul,integralReal_smul]
  have imU : u.im = (w : ℝ)*z.im := by
    change (degeneracyDiagonal w hw • z).im = _
    simpa only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero] using
      congrArg Complex.im (degeneracyDiagonal_smul_coe w hw z)
  have Z : max hi.im lo.im⁻¹ < u.im := by
    rw [imU,mul_comm]
    exact (div_lt_iff₀ hwr).mp hz
  by_cases a : A 1 0=0
  · obtain ⟨k,h|h⟩ := (lowerLeft_zero_iff_signed_translation A).mp a
    all_goals
      have I : v.im=u.im := by rw [← av,h]; simp [UpperHalfPlane.SL_neg_smul,UpperHalfPlane.modular_T_zpow_smul]
      have T := (le_max_left hi.im lo.im⁻¹).trans_lt Z
      rw [← I] at T
      exact (not_lt_of_ge (isMaxOn_iff.mp H v hv)) T
  · have J := im_smul_mul_im_le_one A a u
    rw [av] at J
    have C := (inv_lt_iff_one_lt_mul₀ lo.im_pos).mp ((le_max_right _ _).trans_lt Z)
    nlinarith only [J,C,mul_le_mul_of_nonneg_right (isMinOn_iff.mp L v hv) u.im_pos.le]

theorem compact_logMean_cutoff (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {V : Gamma0OrbitSpace N → ℂ}
    (hV : supportedInQuotientCompact N V) :
    ∃ A : ℝ, ∀ u : ℝ, A < u → logMean N g V u = 0 := by
  obtain ⟨K,hK,hs⟩ := hV
  obtain ⟨Y,hY,H⟩ := high_outside N g hK
  refine ⟨Real.log Y,?_⟩
  intro u hu
  have e : Y < Real.exp u := (Real.log_lt_iff_lt_exp hY).mp hu
  rw [logMean,frameFourier_positive_height _ _ _ _ _ (Real.exp_pos _)]
  have Z (x : ℝ) : V (orbitProjection N (frameAction N _ g (⟨⟨x,Real.exp u⟩,Real.exp_pos u⟩ : ℍ)))=0 := by
    by_contra h
    exact H _ e (hs h)
  simp only [Z,mul_zero,integral_zero]

theorem ae_exp_positive {p : ℝ → Prop} (H : ∀ᵐ y : ℝ, 0 < y → p y) :
    ∀ᵐ u : ℝ, p (Real.exp u) := by
  let S := {y : ℝ | ¬(0 < y → p y)}
  have hs : volume S=0 := ae_iff.mp H
  have pos : S ⊆ Ioi (0 : ℝ) := by
    intro y hy
    by_contra e
    exact hy (fun h => False.elim (e h))
  have d : DifferentiableOn ℝ Real.log S := fun y hy =>
    (Real.differentiableAt_log (pos hy).ne').differentiableWithinAt
  apply ae_iff.mpr
  apply measure_mono_null _ (addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume d hs)
  intro u hu
  exact ⟨Real.exp u,fun e => hu (e (Real.exp_pos u)),Real.log_exp u⟩

theorem logMean_congr (N : ℕ) [NeZero N] (g : SL(2,ℤ))
    {F G : Gamma0OrbitSpace N → ℂ} (hF : MemLp F 2 (carrierPushforward N))
    (hG : MemLp G 2 (carrierPushforward N)) (e : F =ᵐ[carrierPushforward N] G) :
    logMean N g F =ᵐ[volume] logMean N g G := by
  filter_upwards [ae_exp_positive (frameFourier_ae_eq_of_quotient_ae_eq N _ g hF hG e 0)] with u hu
  unfold logMean
  rw [hu]

/-- The full-line log-height adjoint for the actual, uncentered
representative of a nonzero signed packet. Its old volume-calibrated
residual projection vanishes. -/
theorem mean_zero_adjoint (N : ℕ) [NeZero N] (g : SL(2,ℤ)) {F : Gamma0OrbitSpace N → ℂ}
    (hf : MemLp F 2 (carrierPushforward N))
    (hzero : (ℂ ∙ constantL2 N).starProjection (hf.toLp F)=0) :
    (synthesis N g).adjoint (hf.toLp F) =ᵐ[volume] logMean N g F := by
  have Z : removeConstant N (hf.toLp F)=hf.toLp F := by
    change hf.toLp F-(ℂ ∙ constantL2 N).starProjection (hf.toLp F) = _
    rw [hzero,sub_zero]
  have H := log_adjoint_ae N g (hf.toLp F)
  rw [Z] at H
  exact H.trans (logMean_congr N g _ hf hf.coeFn_toLp)

end
end ImbalancedChen.Part3.ActualMarkedHorocycleSupport20261112
