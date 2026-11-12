import ImbalancedChen.Part3ActualMarkedContinuousCoordinates
import ImbalancedChen.Part3ActualZeroModeSpatialGram
import Batteries.Tactic.OpenPrivate

/-! Angular coordinates of each actual centered zero-mode generator.
The comparison uses density only in the ordinary logarithmic Fourier
space. Both spatial vectors keep their original normalized frames. -/
namespace ImbalancedChen.Part3.ActualContinuousGeneratorColumns20261112

noncomputable section
open Set Filter Topology MeasureTheory Matrix Complex
open scoped MatrixGroups UpperHalfPlane BigOperators Classical
open ActualHorocycleSynthesisBound20261112 ActualLogHorocycleAdjoint20261112
open ActualMarkedContinuousCoordinates20261112 ActualZeroModeSpatialGram20261112
open AngularFourierUnitary20261026b SmoothZeroHeightSeedProfiles20261026b
open ActualIncompleteCriticalColumns20261110 ActualIncompleteContinuousGram20261110
open ActualCuspDenominatorClasses20261110 ActualCharacterCuspExpansion20261110
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open private reflectedValue reflected_memLp from ImbalancedChen.Part3ActualHorocycleSynthesisBound

def cuspIndex (N : ℕ) [NeZero N] : Parameters N ≃ CuspRowClass N :=
  (youngCuspEquiv N).trans (nativeCuspEquiv N).symm

theorem cuspIndex_apply (N : ℕ) [NeZero N] (a : Parameters N) :
    cuspIndex N a = frameIndex N (parameterFrame a) := rfl

private def columnVector (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : SmoothHeightSeed) (b : CuspRowClass N) :
    AngularL2 :=
  (if b=frameIndex N h then waveVector ψ else 0)+reflectedVector N b (frameIndex N h) ψ

private theorem columnVector_ae (N : ℕ) [NeZero N] (h : SL(2,ℤ)) (ψ : SmoothHeightSeed) (b : CuspRowClass N) :
    (columnVector N h ψ b : ℝ → ℂ) =ᵐ[angularMeasure] fun t => star (boundaryColumn N h ψ b t) := by
  classical
  have R := (reflected_memLp N b (frameIndex N h) ψ).coeFn_toLp
  by_cases e : b=frameIndex N h
  · filter_upwards [waveVector_ae ψ,R,Lp.coeFn_add (waveVector ψ) (reflectedVector N b (frameIndex N h) ψ)]
      with t hw hr ha
    simp only [columnVector,if_pos e,ha,Pi.add_apply,hw,show reflectedVector N b (frameIndex N h) ψ t = _ from hr,
      reflectedValue,boundaryColumn,star_add,star_mul',star_star]
  · filter_upwards [R] with t hr
    simp only [columnVector,if_neg e,zero_add,boundaryColumn,if_neg e,zero_add,star_mul',star_star,
      show reflectedVector N b (frameIndex N h) ψ t = _ from hr,reflectedValue]

private theorem analysis_seed (N : ℕ) [NeZero N] (a : Parameters N) (h : SL(2,ℤ)) (ψ : SmoothHeightSeed) :
    analysis N a (centeredSeed N h ψ) = columnVector N h ψ (cuspIndex N a) := by
  let X := analysis N a (centeredSeed N h ψ)
  let Y := columnVector N h ψ (cuspIndex N a)
  have onTests (f : LogTest) : inner ℂ X (angularFourierUnitary (testEmbedding f)) =
      inner ℂ Y (angularFourierUnitary (testEmbedding f)) := by
    calc
      _ = inner ℂ ((synthesis N (parameterFrame a)).adjoint (centeredSeed N h ψ)) (testEmbedding f) :=
        angularFourierUnitary.inner_map_map _ _
      _ = inner ℂ (centeredSeed N h ψ) (centeredSeed N (parameterFrame a) (fromLog f)) := by
        rw [ContinuousLinearMap.adjoint_inner_left,synthesis_test]
      _ = _ := by
        have W : waveVector (fromLog f)=angularFourierUnitary (testEmbedding f) := by
          rw [waveVector,logVector_fromLog]
        rw [centered_cross,W]
  apply ext_inner_right ℂ
  intro v
  have H := test_dense.induction_on (angularFourierUnitary.symm v) (p := fun u =>
    inner ℂ X (angularFourierUnitary u) = inner ℂ Y (angularFourierUnitary u))
    (isClosed_eq (continuous_const.inner angularFourierUnitary.continuous)
      (continuous_const.inner angularFourierUnitary.continuous)) onTests
  simpa only [LinearIsometryEquiv.apply_symm_apply] using H

theorem analysis_seed_ae (N : ℕ) [NeZero N] (a : Parameters N) (h : SL(2,ℤ)) (ψ : SmoothHeightSeed) :
    (analysis N a (centeredSeed N h ψ) : ℝ → ℂ) =ᵐ[angularMeasure]
      fun t => star (boundaryColumn N h ψ (cuspIndex N a) t) := by
  rw [analysis_seed]
  exact columnVector_ae N h ψ _

/-- The half sum of the actual AngularL2 scalar products equals the
physical centered inner product on every pair of original generators. -/
theorem analysis_seed_gram (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    inner ℂ (centeredSeed N h ψ) (centeredSeed N g φ) =
      (1/2 : ℂ)*∑ a : Parameters N,
        inner ℂ (analysis N a (centeredSeed N h ψ)) (analysis N a (centeredSeed N g φ)) := by
  classical
  let F := fun b t => boundaryColumn N h ψ b t*star (boundaryColumn N g φ b t)
  have I (b : CuspRowClass N) : Integrable (F b) angularMeasure :=
    ((boundaryColumn_L2 N h ψ b).integrable_mul (boundaryColumn_L2 N g φ b).star).smul_measure ENNReal.ofReal_ne_top
  have A (a : Parameters N) :
      inner ℂ (analysis N a (centeredSeed N h ψ)) (analysis N a (centeredSeed N g φ)) =
        ∫ t,F (cuspIndex N a) t ∂angularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [analysis_seed_ae N a h ψ,analysis_seed_ae N a g φ] with t ht hw
    simp only [RCLike.inner_apply',← Complex.star_def,ht,hw,star_star,F]
  have J := spatial_gram N h g ψ φ
  dsimp only at J
  rw [centeredSeed,centeredSeed,centered_inner,J,add_sub_cancel_right]
  simp_rw [A]
  rw [(cuspIndex N).sum_comp (fun b => ∫ t,F b t ∂angularMeasure),
    ← integral_finsetSum Finset.univ (fun b _ => I b),angularMeasure_integral]
  change ((4*Real.pi)⁻¹ : ℝ) • (∫ t,physicalProduct N h g ψ φ t) =
    (1/2 : ℂ)*(((2*Real.pi)⁻¹ : ℝ) • ∫ t,physicalProduct N h g ψ φ t)
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] <;> ring

end
end ImbalancedChen.Part3.ActualContinuousGeneratorColumns20261112
