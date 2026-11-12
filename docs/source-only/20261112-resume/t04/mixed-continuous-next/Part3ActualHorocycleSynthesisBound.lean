import ImbalancedChen.Part3ActualZeroModeSpatialGram
import ImbalancedChen.Part3HeightMellinUnitary
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The actual residual-free zero-mode Poincaré synthesis bound in each
width-normalized frame. The incoming wave lives in the literal angular
space with measure dt/(2π). The other summand uses the actual diagonal
scattering entry and reflection of this very wave. -/
namespace ImbalancedChen.Part3.ActualHorocycleSynthesisBound20261112

noncomputable section
open Set Filter MeasureTheory Complex Matrix
open scoped MatrixGroups UpperHalfPlane BigOperators FourierTransform SchwartzMap
open Gamma0QuotientCellPushforward20261025a Gamma0ActualConstantMode20261025a
open AllNormalizedCuspAnnihilator20261026b SmoothZeroHeightSeedProfiles20261026b
open AngularFourierUnitary20261026b HeightMellinUnitary20261026b
open CompactHeightMellinInversion20261027 ActualIncompleteCriticalColumns20261110
open ActualIncompleteContinuousGram20261110 ActualCriticalScatteringEntry20261110
open ActualCriticalScatteringUnitarity20261110 ActualCharacterCuspExpansion20261110
open ActualCriticalCuspEvaluation20261110
open ActualZeroModeSpatialGram20261112

def removeConstant (N : ℕ) [NeZero N] : QuotientL2 N →L[ℂ] QuotientL2 N :=
  ContinuousLinearMap.id ℂ _ - (ℂ ∙ constantL2 N).starProjection

def centeredSeed (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (ψ : SmoothHeightSeed) : QuotientL2 N :=
  removeConstant N (frameZeroSeedL2 N (NeZero.pos N) g ψ.toHeightSeed)

theorem centered_inner (N : ℕ) [NeZero N] (V W : QuotientL2 N) :
    inner ℂ (removeConstant N V) (removeConstant N W) =
      inner ℂ V W-inner ℂ V ((ℂ ∙ constantL2 N).starProjection W) := by
  let C := ℂ ∙ constantL2 N
  change inner ℂ (V-C.starProjection V) (W-C.starProjection W) = _
  have H := C.starProjection_inner_eq_zero W (C.starProjection V) (C.starProjection_apply_mem V)
  rw [inner_sub_left,inner_eq_zero_symm.mp H,sub_zero,inner_sub_right]

def logVector (ψ : SmoothHeightSeed) : RealL2 :=
  ((logSchwartz ψ (1/2)).memLp 2).toLp (logSchwartz ψ (1/2))

def waveVector (ψ : SmoothHeightSeed) : AngularL2 := angularFourierUnitary (logVector ψ)

theorem waveVector_ae (ψ : SmoothHeightSeed) :
    waveVector ψ =ᵐ[angularMeasure] wave ψ := by
  have H := angularFourierUnitary_toLp_ae (logSchwartz ψ (1/2)).integrable ((logSchwartz ψ (1/2)).memLp 2)
  apply H.trans
  exact ae_of_all _ (fun t => by
    rw [angularTransform_eq_fourier]
    simp only [wave,mellinAngular,mellinFrequency,SchwartzMap.fourier_coe,div_eq_inv_mul])

private theorem reflected_measure :
    MeasurePreserving (fun t : ℝ => -t) angularMeasure angularMeasure :=
  (Measure.measurePreserving_neg (volume : Measure ℝ)).smul_measure _

private def reverseWave (ψ : SmoothHeightSeed) : AngularL2 :=
  Lp.compMeasurePreserving (fun t : ℝ => -t) reflected_measure (waveVector ψ)

private theorem reverse_ae (ψ : SmoothHeightSeed) :
    reverseWave ψ =ᵐ[angularMeasure] fun t => wave ψ (-t) :=
  (Lp.coeFn_compMeasurePreserving _ reflected_measure).trans
    (reflected_measure.quasiMeasurePreserving.ae_eq_comp (waveVector_ae ψ))

private theorem scattering_cont (N : ℕ) [NeZero N] (a b : CuspRowClass N) :
    Continuous (fun t : ℝ => scatteringMatrix N t a b) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have T := (critical_parameters t).2
  exact ((continuedEntry_regularity N (NeZero.pos N) (classFrame a) (classFrame b)).2 _
    T.1 T.2.2).continuousAt.comp (show Continuous criticalPoint by unfold criticalPoint; fun_prop).continuousAt

private def reflectedValue (N : ℕ) [NeZero N] (a b : CuspRowClass N) (ψ : SmoothHeightSeed) (t : ℝ) :=
  star (scatteringMatrix N t a b)*wave ψ (-t)

private theorem reflected_memLp (N : ℕ) [NeZero N] (a b : CuspRowClass N) (ψ : SmoothHeightSeed) :
    MemLp (reflectedValue N a b ψ) 2 angularMeasure := by
  have H := (reverseWave ψ).memLp.congr (reverse_ae ψ)
  apply H.of_le ((scattering_cont N a b).star.aestronglyMeasurable.mul H.aestronglyMeasurable)
  exact ae_of_all _ (fun t => by
    rw [reflectedValue,norm_mul,norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_le N t a b))

def reflectedVector (N : ℕ) [NeZero N] (a b : CuspRowClass N) (ψ : SmoothHeightSeed) : AngularL2 :=
  (reflected_memLp N a b ψ).toLp _

theorem reflected_norm_le (N : ℕ) [NeZero N] (a b : CuspRowClass N) (ψ : SmoothHeightSeed) :
    ‖reflectedVector N a b ψ‖ ≤ ‖waveVector ψ‖ := by
  have H : ‖reflectedVector N a b ψ‖ ≤ ‖reverseWave ψ‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(reflected_memLp N a b ψ).coeFn_toLp,reverse_ae ψ] with t ht hu
    rw [show reflectedVector N a b ψ t = _ from ht,hu,reflectedValue,norm_mul,norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (entry_norm_le N t a b)
  exact H.trans_eq ((Lp.compMeasurePreservingₗᵢ (𝕜 := ℂ) _ reflected_measure).norm_map _)

/-- The actual centered Gram evaluated as an angular Hilbert pairing.
The full-cusp, full-line dt/(4π) Gram is used before the two reflected
halves are placed in the single Mellin channel. -/
theorem centered_cross (N : ℕ) [NeZero N] (h g : SL(2,ℤ)) (ψ φ : SmoothHeightSeed) :
    inner ℂ (centeredSeed N h ψ) (centeredSeed N g φ) =
      inner ℂ ((if frameIndex N g=frameIndex N h then waveVector ψ else 0)+
        reflectedVector N (frameIndex N g) (frameIndex N h) ψ) (waveVector φ) := by
  classical
  have H := spatial_gram N h g ψ φ
  dsimp only at H
  rw [full_line_normalization] at H
  rw [centeredSeed,centeredSeed,centered_inner, H,add_sub_cancel_right,
    ← angularMeasure_integral,L2.inner_def]
  apply integral_congr_ae
  let b := frameIndex N g
  let c := frameIndex N h
  have W := waveVector_ae ψ
  have J := waveVector_ae φ
  have R := (reflected_memLp N b c ψ).coeFn_toLp
  by_cases e : frameIndex N g=frameIndex N h
  · rw [if_pos e]
    filter_upwards [W,J,R,Lp.coeFn_add (waveVector ψ) (reflectedVector N b c ψ)] with t hw hj hr ha
    rw [gram_critical_eq,boundaryColumn,if_pos e]
    change _ = inner ℂ ((waveVector ψ+reflectedVector N b c ψ) t) (waveVector φ t)
    rw [ha,hj]
    simp only [Pi.add_apply,RCLike.inner_apply',← Complex.star_def,hw,
      show reflectedVector N b c ψ t = _ from hr,reflectedValue,star_add,star_mul,star_star,b,c]
    ring
  · rw [if_neg e,zero_add]
    filter_upwards [J,R] with t hj hr
    rw [gram_critical_eq,boundaryColumn,if_neg e,zero_add]
    change _ = inner ℂ (reflectedVector N b c ψ t) (waveVector φ t)
    simp only [RCLike.inner_apply',← Complex.star_def,hj,show reflectedVector N b c ψ t = _ from hr,
      reflectedValue,star_mul,star_star,b,c]
    ring

theorem centered_bound (N : ℕ) [NeZero N] (g : SL(2,ℤ)) (ψ : SmoothHeightSeed) :
    ‖centeredSeed N g ψ‖ ≤ Real.sqrt 2*‖logVector ψ‖ := by
  let W := waveVector ψ
  let R := reflectedVector N (frameIndex N g) (frameIndex N g) ψ
  have H := centered_cross N g g ψ ψ
  rw [if_pos rfl,inner_self_eq_norm_sq_to_K] at H
  have T : ‖centeredSeed N g ψ‖^2 ≤ (‖W‖+‖R‖)*‖W‖ := by
    calc
      _ = ‖inner ℂ (W+R) W‖ := by rw [← H,norm_pow,Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]
      _ ≤ _ := (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg W))
  have L : ‖R‖ ≤ ‖W‖ := reflected_norm_le _ _ _ _
  have nw : ‖W‖ = ‖logVector ψ‖ := angularFourierUnitary.norm_map _
  have T' := T.trans (mul_le_mul_of_nonneg_right (add_le_add_left L ‖W‖) (norm_nonneg W))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),← nw]
  nlinarith only [T']

end
end ImbalancedChen.Part3.ActualHorocycleSynthesisBound20261112
