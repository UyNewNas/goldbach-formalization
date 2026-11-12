import ImbalancedChen.Part3ActualContinuousResolution
import ImbalancedChen.Part3ActualMarkedHorocycleSupport
import Batteries.Tactic.OpenPrivate

/-! Identification inside the original quotient: the residual-free
incomplete Eisenstein space is the orthogonal complement of the constant
line and of the full geometric all-frame cusp subspace. -/
namespace ImbalancedChen.Part3.ActualContinuousPhysicalComplement20261112

noncomputable section
open Set Filter Topology MeasureTheory Complex Matrix
open scoped MatrixGroups UpperHalfPlane BigOperators Distributions
open ActualContinuousResolution20261112 ActualHorocycleSynthesisBound20261112
open ActualLogHorocycleAdjoint20261112 ActualMarkedHorocycleSupport20261112
open AngularFourierUnitary20261026b SmoothZeroHeightSeedProfiles20261026b
open AllNormalizedCuspAnnihilator20261026b ActualInfinityCuspAnnihilator20261026b
open NormalizedCuspCompactFourierFubini20261026b NormalizedCuspCompactPoincare20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open private mean_local from ImbalancedChen.Part3ActualLogHorocycleAdjoint
open private exp_substitution from ImbalancedChen.Part3ActualIncompleteMellinFactors

private theorem log_test_unique {F G : ℝ → ℂ} (hF : LocallyIntegrable F) (hG : LocallyIntegrable G)
    (H : ∀ f : LogTest, (∫ u,star (f u)*F u)=∫ u,star (f u)*G u) : F =ᵐ[volume] G := by
  apply ae_eq_of_integral_contDiff_smul_eq hF hG
  intro φ hd hc
  let f : LogTest := ⟨fun u => (φ u : ℂ),Complex.ofRealCLM.contDiff.comp hd,hc.comp_left (by simp),subset_univ _⟩
  simpa only [f,Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using H f

private theorem raw_tests_cuspidal (N : ℕ) [NeZero N] (v : QuotientL2 N)
    (H : ∀ (g : SL(2,ℤ)) (f : LogTest),inner ℂ (frameZeroSeedL2 N (NeZero.pos N) g (fromLog f).toHeightSeed) v=0) :
    v ∈ allFrameCuspSubspace N (NeZero.pos N) := by
  apply (mem_allFrameCuspSubspace_iff N _ v).mpr
  intro g ψ
  have Z : logMean N g v =ᵐ[volume] (fun _ : ℝ => (0 : ℂ)) :=
    log_test_unique (mean_local N g v) continuous_const.locallyIntegrable (fun f => by
      rw [← (tested_logMean N g v f).2,H]
      simp)
  rw [frameZeroSeedL2,framePoincareL2_inner_eq_fourier,exp_substitution]
  apply integral_eq_zero_of_ae
  filter_upwards [Z] with u hu
  have J : frameFourier N (NeZero.pos N) g v 0 (Real.exp u)=0 :=
    (mul_eq_zero.mp hu).resolve_left (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  simp only [J,mul_zero,smul_zero]

private theorem centered_test (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (ψ : SmoothHeightSeed) (v : QuotientL2 N) :
    inner ℂ (centeredSeed N g ψ) v =
      inner ℂ (frameZeroSeedL2 N (NeZero.pos N) g ψ.toHeightSeed) (removeConstant N v) := by
  let C := ℂ ∙ constantL2 N
  let p := frameZeroSeedL2 N (NeZero.pos N) g ψ.toHeightSeed
  change inner ℂ (p-C.starProjection p) v=inner ℂ p (v-C.starProjection v)
  rw [inner_sub_left,C.inner_starProjection_left_eq_right,inner_sub_right]

theorem centered_perp_iff_centered_cusp (N : ℕ) [NeZero N] (v : QuotientL2 N) :
    v ∈ (centeredSpace N)ᗮ ↔ removeConstant N v ∈ allFrameCuspSubspace N (NeZero.pos N) := by
  rw [centered_perp_iff]
  constructor
  · intro H
    exact raw_tests_cuspidal N _ (fun g f => (centered_test N g (fromLog f) v).symm.trans (H g _))
  · intro H g ψ
    rw [centered_test]
    exact (mem_allFrameCuspSubspace_iff N _ _).mp H g ψ.toHeightSeed

private def constantProfile (u : ℝ) : ℂ := (Real.exp (-(u/2)) : ℂ)

private theorem log_constant (N : ℕ) [NeZero N] (g : SL(2,ℤ)) :
    logMean N g (constantL2 N) =ᵐ[volume] constantProfile := by
  apply (logMean_congr N g (constantL2 N).memLp (constant_memLp_two N) (constant_memLp_two N).coeFn_toLp).trans
  exact ae_of_all _ (fun u => by
    have J : frameFourier N (NeZero.pos N) g (fun _ => (1 : ℂ)) 0 (Real.exp u)=1 := by
      rw [frameFourier_positive_height _ _ _ _ _ (Real.exp_pos _),integral_Ico_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le zero_le_one]
      simp
    simp only [logMean,J,mul_one,constantProfile])

private theorem constant_test (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (f : LogTest) :
    inner ℂ (frameZeroSeedL2 N (NeZero.pos N) g (fromLog f).toHeightSeed) (constantL2 N) =
      ∫ u,star (f u)*constantProfile u := by
  rw [(tested_logMean N g (constantL2 N) f).2]
  apply integral_congr_ae
  filter_upwards [log_constant N g] with u hu
  rw [hu]

private theorem no_constant_tail {c : ℂ} (H : MemLp (fun u => -c*constantProfile u) 2 volume) : c=0 := by
  have hI := (memLp_two_iff_integrable_sq_norm H.1).mp H
  have J : IntegrableOn (fun _ : ℝ => ‖c‖^2) (Iic (0 : ℝ)) := by
    apply hI.integrableOn.mono' aestronglyMeasurable_const
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    rw [Real.norm_of_nonneg (sq_nonneg _),norm_mul,norm_neg,constantProfile,Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact le_mul_of_one_le_right (norm_nonneg _) (Real.one_le_exp (by
      change u ≤ 0 at hu
      linarith))
  simpa only [integrableOn_const_iff,Real.volume_Iic,lt_self_iff_false,or_false,enorm_eq_zero,
    sq_eq_zero_iff,norm_eq_zero] using J

/-- A cuspidal vector is globally orthogonal to the actual constant.
If its residual component were c·1, the bounded zero-mode adjoint would
have the logarithmic profile -c exp(-u/2) on the whole line. -/
theorem cusp_constant_projection (N : ℕ) [NeZero N] {v : QuotientL2 N}
    (hv : v ∈ allFrameCuspSubspace N (NeZero.pos N)) : (ℂ ∙ constantL2 N).starProjection v=0 := by
  let C := ℂ ∙ constantL2 N
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (C.starProjection_apply_mem v)
  let g : SL(2,ℤ) := 1
  let A := (synthesis N g).adjoint v
  have H (f : LogTest) : (∫ u,star (f u)*A u) = ∫ u,star (f u)*(-c*constantProfile u) := by
    let p := frameZeroSeedL2 N (NeZero.pos N) g (fromLog f).toHeightSeed
    have E : inner ℂ p v=0 := (mem_allFrameCuspSubspace_iff N _ v).mp hv g _
    calc
      _ = inner ℂ (testEmbedding f) A := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [test_ae f] with u hu
        simp only [RCLike.inner_apply',← Complex.star_def,hu]
      _ = inner ℂ (centeredSeed N g (fromLog f)) v := by
        rw [← synthesis_test,ContinuousLinearMap.adjoint_inner_right]
      _ = -c*inner ℂ p (constantL2 N) := by
        change inner ℂ (p-C.starProjection p) v=_
        rw [inner_sub_left,C.inner_starProjection_left_eq_right,E,← hc,inner_smul_right]
        ring
      _ = _ := by
        rw [show inner ℂ p (constantL2 N)=_ from constant_test N g f,← integral_const_mul]
        apply integral_congr_ae
        exact ae_of_all _ (fun _ => by ring)
  have B : A =ᵐ[volume] (fun u => -c*constantProfile u) :=
    log_test_unique (A.memLp.locallyIntegrable (by norm_num))
      (by fun_prop [constantProfile] : Continuous (fun u => -c*constantProfile u)).locallyIntegrable H
  have h0 := no_constant_tail (A.memLp.congr B)
  simpa only [h0,zero_smul] using hc.symm

theorem cusp_le_constant_perp (N : ℕ) [NeZero N] :
    allFrameCuspSubspace N (NeZero.pos N) ≤ (ℂ ∙ constantL2 N)ᗮ :=
  fun _ hv => (Submodule.starProjection_apply_eq_zero_iff _).mp (cusp_constant_projection N hv)

theorem cusp_le_centered_perp (N : ℕ) [NeZero N] :
    allFrameCuspSubspace N (NeZero.pos N) ≤ (centeredSpace N)ᗮ := by
  intro v hv
  apply (centered_perp_iff_centered_cusp N v).mpr
  change v-(ℂ ∙ constantL2 N).starProjection v ∈ _
  simpa only [cusp_constant_projection N hv,sub_zero] using hv

/-- Independent geometric description of the range inside the full
finite-level quotient Hilbert space. All integral cusp frames are tested. -/
theorem centered_eq_physical_complement (N : ℕ) [NeZero N] :
    centeredSpace N = (ℂ ∙ constantL2 N)ᗮ ⊓ (allFrameCuspSubspace N (NeZero.pos N))ᗮ := by
  let C := ℂ ∙ constantL2 N
  let D := allFrameCuspSubspace N (NeZero.pos N)
  have hC : centeredSpace N ≤ Cᗮ := centered_le N C.isClosed_orthogonal (fun g ψ =>
    C.sub_starProjection_mem_orthogonal _)
  apply le_antisymm
  · refine le_inf hC ?_
    intro v hv z hz
    exact inner_eq_zero_symm.mp ((cusp_le_centered_perp N hz) v hv)
  · intro v hv
    have J : v ∈ (centeredSpace N)ᗮᗮ := by
      intro u hu
      have hz : removeConstant N u ∈ D := (centered_perp_iff_centered_cusp N u).mp hu
      have E : u=removeConstant N u+C.starProjection u := (sub_add_cancel _ _).symm
      calc
        inner ℂ u v = inner ℂ (removeConstant N u+C.starProjection u) v := congrArg (fun z => inner ℂ z v) E
        _ = 0 := by rw [inner_add_left,hv.2 _ hz,hv.1 _ (C.starProjection_apply_mem u),add_zero]
    simpa only [Submodule.orthogonal_orthogonal] using J

end
end ImbalancedChen.Part3.ActualContinuousPhysicalComplement20261112
