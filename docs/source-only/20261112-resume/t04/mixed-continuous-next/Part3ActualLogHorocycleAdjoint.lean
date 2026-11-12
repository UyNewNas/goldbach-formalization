import ImbalancedChen.Part3ActualHorocycleSynthesisBound
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Batteries.Tactic.OpenPrivate

/-! The adjoint of bounded, centered, physical zero-mode synthesis is
the literal normalized logarithmic horocycle average. All density and
representative arguments use Lebesgue measure in the log variable. -/
namespace ImbalancedChen.Part3.ActualLogHorocycleAdjoint20261112

noncomputable section
open Set Filter MeasureTheory Complex Matrix
open scoped MatrixGroups UpperHalfPlane Topology Distributions ContDiff
open ActualHorocycleSynthesisBound20261112 AngularFourierUnitary20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open SmoothZeroHeightSeedProfiles20261026b AllNormalizedCuspAnnihilator20261026b
open NormalizedCuspCompactPoincare20261026b NormalizedCuspCompactFourierFubini20261026b
open CompactHeightMellinInversion20261027
open private exp_substitution from ImbalancedChen.Part3ActualIncompleteMellinFactors

abbrev LogTest := 𝓓((⊤ : TopologicalSpace.Opens ℝ),ℂ)

private def back (f : LogTest) (y : ℝ) : ℂ :=
  if 0 < y then (Real.exp (Real.log y/2) : ℂ)*f (Real.log y) else 0

private theorem back_support (f : LogTest) :
    Function.support (back f) ⊆ Real.exp '' tsupport (f : ℝ → ℂ) := by
  intro y hy
  by_cases h : 0 < y
  · refine ⟨Real.log y,subset_tsupport _ ?_,Real.exp_log h⟩
    intro e
    exact hy (by simp [back,h,e])
  · exact False.elim (hy (by simp [back,h]))

def fromLog (f : LogTest) : SmoothHeightSeed := by
  let K := Real.exp '' tsupport (f : ℝ → ℂ)
  have hK : IsCompact K := f.hasCompactSupport.image Real.continuous_exp
  have pos : K ⊆ Ioi (0 : ℝ) := by rintro _ ⟨u,_,rfl⟩; exact Real.exp_pos _
  have ht : tsupport (back f) ⊆ K := closure_minimal (back_support f) hK.isClosed
  have D : ContDiff ℝ ∞ (back f) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases h : 0 < y
    · have E := (Real.contDiffAt_log h.ne').div_const 2
      apply ((Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (Real.contDiff_exp.contDiffAt.comp y E)).mul (f.contDiff.contDiffAt.comp y (Real.contDiffAt_log h.ne'))).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds h] with z hz
      exact if_pos hz
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      have hy : y ∉ K := fun e => h (pos e)
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with z hz
      exact notMem_support.mp (fun e => hz (back_support f e))
  exact ⟨⟨back f,D.continuous,HasCompactSupport.of_support_subset_isCompact hK (back_support f),ht.trans pos⟩,D⟩

@[simp] theorem fromLog_exp (f : LogTest) (u : ℝ) :
    (fromLog f).toFun (Real.exp u) = (Real.exp (u/2) : ℂ)*f u := by
  change back f _ = _
  simp [back,Real.exp_pos]

def testEmbedding : LogTest →ₗ[ℂ] RealL2 where
  toFun f := (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem test_ae (f : LogTest) : testEmbedding f =ᵐ[volume] (f : ℝ → ℂ) :=
  (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).coeFn_toLp

theorem test_dense : DenseRange testEmbedding := by
  apply (Lp.dense_hasCompactSupport_contDiff (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)).mono
  rintro v ⟨f,e,hc,hd⟩
  let φ : LogTest := ⟨f,hd,hc,subset_univ _⟩
  exact ⟨φ,Lp.ext ((test_ae φ).trans e.symm)⟩

theorem logVector_fromLog (f : LogTest) : logVector (fromLog f) = testEmbedding f := by
  apply Lp.ext
  filter_upwards [((logSchwartz (fromLog f) (1/2)).memLp 2).coeFn_toLp,test_ae f] with u hu hv
  rw [show logVector (fromLog f) u = _ from hu,hv,logSchwartz_apply,tiltedLogProfile,fromLog_exp]
  rw [Complex.ofReal_exp,← mul_assoc,← Complex.exp_add]
  push_cast
  ring_nf
  simp

def logMean (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (V : Gamma0OrbitSpace N → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-(u/2)) : ℂ)*frameFourier N (NeZero.pos N) g V 0 (Real.exp u)

private theorem transformed_test (f : LogTest) (F : ℝ → ℂ) (u : ℝ) :
    Real.exp u • (((Real.exp u)⁻¹^2 : ℝ) •
      (star ((fromLog f).toFun (Real.exp u))*F (Real.exp u))) =
      star (f u)*((Real.exp (-(u/2)) : ℂ)*F (Real.exp u)) := by
  have X : Real.exp u*((Real.exp u)⁻¹)^2*Real.exp (u/2) = Real.exp (-(u/2)) := by
    rw [show Real.exp u*((Real.exp u)⁻¹)^2 = (Real.exp u)⁻¹ by field_simp,
      ← Real.exp_neg,← Real.exp_add]
    congr 1 <;> ring
  have Y := congrArg Complex.ofReal X
  push_cast at Y
  simp only [Complex.real_smul,fromLog_exp,star_mul,Complex.star_def,map_mul,Complex.conj_ofReal,
    Complex.ofReal_pow,Complex.ofReal_inv]
  rw [← Y]
  ring

theorem tested_logMean (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (V : QuotientL2 N) (f : LogTest) :
    Integrable (fun u => star (f u)*logMean N g V u) ∧
    inner ℂ (frameZeroSeedL2 N (NeZero.pos N) g (fromLog f).toHeightSeed) V =
      ∫ u,star (f u)*logMean N g V u := by
  let ψ := fromLog f
  let F := frameFourier N (NeZero.pos N) g V 0
  let G := fun y : ℝ => ((y⁻¹)^2 : ℝ) • (star (ψ.toFun y)*F y)
  have H : IntegrableOn G (Ioi (0 : ℝ)) :=
    frameFourier_pairing_integrable N _ g V V.memLp 0 _ ψ.continuous ψ.compact ψ.positive
  have J : Integrable (fun u => Real.exp u • G (Real.exp u)) := by
    have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := Real.exp) (f' := Real.exp)
      measurableSet_univ (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn G
    simpa only [image_univ,Real.range_exp,integrableOn_univ,abs_of_pos (Real.exp_pos _)] using
      h.mp (by simpa only [image_univ,Real.range_exp] using H)
  have E : (fun u => Real.exp u • G (Real.exp u)) = fun u => star (f u)*logMean N g V u :=
    funext (transformed_test f F)
  refine ⟨E ▸ J,?_⟩
  rw [frameZeroSeedL2,framePoincareL2_inner_eq_fourier]
  change (∫ y in Ioi (0 : ℝ),G y) = _
  rw [exp_substitution,E]

private def rawSynthesis (N : ℕ) [NeZero N] (g : SL(2,ℤ)) : LogTest →ₗ[ℂ] QuotientL2 N where
  toFun f := frameZeroSeedL2 N (NeZero.pos N) g (fromLog f).toHeightSeed
  map_add' f h := by
    apply ext_inner_right ℂ
    intro v
    rw [inner_add_left,(tested_logMean N g v (f+h)).2,(tested_logMean N g v f).2,(tested_logMean N g v h).2,
      ← integral_add (tested_logMean N g v f).1 (tested_logMean N g v h).1]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by change star (f u+h u)*_ = _; rw [star_add,add_mul])
  map_smul' c f := by
    apply ext_inner_right ℂ
    intro v
    rw [inner_smul_left,(tested_logMean N g v (c • f)).2,(tested_logMean N g v f).2,← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by change star (c*f u)*_ = _; simp [Complex.star_def]; ring)

private def centeredTests (N : ℕ) [NeZero N] (g : SL(2,ℤ)) : LogTest →ₗ[ℂ] QuotientL2 N :=
  (removeConstant N).toLinearMap.comp (rawSynthesis N g)

private theorem test_bound (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (f : LogTest) :
    ‖centeredTests N g f‖ ≤ Real.sqrt 2*‖testEmbedding f‖ := by
  simpa only [← logVector_fromLog] using centered_bound N g (fromLog f)

/-- Actual bounded centered synthesis from all logarithmic incoming data. -/
def synthesis (N : ℕ) [NeZero N] (g : SL(2,ℤ)) : RealL2 →L[ℂ] QuotientL2 N :=
  (centeredTests N g).extendOfNorm testEmbedding

theorem synthesis_test (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (f : LogTest) :
    synthesis N g (testEmbedding f) = centeredSeed N g (fromLog f) :=
  LinearMap.extendOfNorm_eq test_dense ⟨_,test_bound N g⟩ f

theorem synthesis_norm_le (N : ℕ) [NeZero N] (g : SL(2,ℤ)) :
    ‖synthesis N g‖ ≤ Real.sqrt 2 :=
  LinearMap.opNorm_extendOfNorm_le test_dense (Real.sqrt_nonneg _) (test_bound N g)

private theorem mean_local (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (V : QuotientL2 N) :
    LocallyIntegrable (logMean N g V) := by
  intro u
  let β : ContDiffBump u := ⟨1,2,by norm_num,by norm_num⟩
  let f : LogTest := ⟨fun v => (β v : ℂ),Complex.ofRealCLM.contDiff.comp β.contDiff,
    β.hasCompactSupport.comp_left (by simp),subset_univ _⟩
  refine ⟨Metric.ball u 1,Metric.ball_mem_nhds _ zero_lt_one,?_⟩
  apply (tested_logMean N g V f).1.integrableOn.congr_fun _ measurableSet_ball
  intro v hv
  change star (β v : ℂ)*_ = _
  simp [β.one_of_mem_closedBall (show v ∈ Metric.closedBall u β.rIn from hv.le)]

theorem log_adjoint_ae (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (V : QuotientL2 N) :
    (synthesis N g).adjoint V =ᵐ[volume] logMean N g (removeConstant N V) := by
  let v := (synthesis N g).adjoint V
  have H (f : LogTest) : (∫ u,star (f u)*v u) = ∫ u,star (f u)*logMean N g (removeConstant N V) u := by
    calc
      _ = inner ℂ (testEmbedding f) v := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [test_ae f] with u hu
        simp [RCLike.inner_apply',← Complex.star_def,hu]
      _ = inner ℂ (synthesis N g (testEmbedding f)) V := (synthesis N g).adjoint_inner_right _ _
      _ = _ := by
        rw [synthesis_test,centeredSeed]
        let P := frameZeroSeedL2 N (NeZero.pos N) g (fromLog f).toHeightSeed
        let C := ℂ ∙ constantL2 N
        change inner ℂ (P-C.starProjection P) V = _
        rw [inner_sub_left,C.inner_starProjection_left_eq_right,← inner_sub_right]
        exact (tested_logMean N g (removeConstant N V) f).2
  apply ae_eq_of_integral_contDiff_smul_eq (v.memLp.locallyIntegrable (by norm_num))
    (mean_local N g (removeConstant N V))
  intro φ hd hc
  let f : LogTest := ⟨fun x => (φ x : ℂ),Complex.ofRealCLM.contDiff.comp hd,hc.comp_left (by simp),subset_univ _⟩
  simpa only [f,Complex.star_def,Complex.conj_ofReal,Complex.real_smul] using H f

theorem logMean_memLp (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (V : QuotientL2 N) :
    MemLp (logMean N g (removeConstant N V)) 2 volume :=
  ((synthesis N g).adjoint V).memLp.congr (log_adjoint_ae N g V)

end
end ImbalancedChen.Part3.ActualLogHorocycleAdjoint20261112
