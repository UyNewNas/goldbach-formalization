import ImbalancedChen.Part3OriginalHolomorphicFrickeBasis
import ImbalancedChen.Part3ActualFrickeCuspPhase
import ImbalancedChen.Part3OriginalPeterssonPretrace

/-! Fourier transport of the manuscript normalized cuspOne chart,
including its determinant-one slash action and its positive n/N phase. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalHolomorphicFrickePhase20261113
open Complex Matrix SpecialLinearGroup MeasureTheory UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane ModularForm
open OriginalHolomorphicPeterssonSpace20261112 OriginalHolomorphicCuspFrames20261110
open OriginalHolomorphicFrickeBasis20261113 (W action action_function mapGL_realSL)
open Gamma0ActualCuspsSourceOnly (cuspOneMatrix translation_mem_gamma0)
open Gamma0GeneralCuspUnitPeriod20261025a (integralReal normalizedScaling)
open ActualFrickeCuspPhase20261025a (original_cuspOneScaling_eq_fricke)
open P3ActualCuspScalingSourceOnly (translationSL translation)
open NativeHolomorphicFourierNormalization20261102s (holomorphicR_eq_qExpansion)
open FrickeNormalizer (frickeSL realSL)
open P3Period64NativeReconstructionSourceOnly (e norm_e)

def phase (N n : ℕ) : ℂ := e ((n:ℝ)/(N:ℝ))

theorem phase_norm (N n : ℕ) : ‖phase N n‖=1 := norm_e _

private def shift (N : ℕ) := mapGL ℝ (translationSL (N:ℝ))

private theorem frame_one (N r : ℕ) [NeZero N] (f : Forms N r) (w : ℍ) :
    frameForm N (NeZero.pos N) r f cuspOneMatrix w =
      frameForm N (NeZero.pos N) r (action N r f) 1 (shift N • w) := by
  let hN := NeZero.pos N
  have t : mapGL ℝ ModularGroup.T∈levelGroup N :=
    Subgroup.mem_map.mpr ⟨_,by simpa only [zpow_one] using translation_mem_gamma0 N 1,rfl⟩
  have deck := SlashInvariantFormClass.slash_action_eq f _ t
  have factor : frameGL N hN cuspOneMatrix=(mapGL ℝ ModularGroup.T*W N)*shift N := by
    rw [frameGL,original_cuspOneScaling_eq_fricke,map_mul,map_mul,
      show integralReal ModularGroup.T=realSL ModularGroup.T from rfl,mapGL_realSL] <;> rfl
  have d : denom (shift N) w=1 := by simp [shift,translationSL,translation,denom,mapGL_coe_matrix]
  change (⇑f ∣[2*(r:ℤ)] frameGL N hN cuspOneMatrix) w =
    (⇑(action N r f) ∣[2*(r:ℤ)] frameGL N hN 1) (shift N • w)
  rw [factor,SlashAction.slash_mul,SlashAction.slash_mul,deck,(two_actual_frames N hN).1,
    SlashAction.slash_one,action_function,ModularForm.slash_apply,d]
  simp [shift,UpperHalfPlane.σ]

private theorem argument_shift (N : ℕ) (w : ℍ) :
    ((shift N • w:ℍ):ℂ)=(w:ℂ)+(1/(N:ℝ):ℝ) := by
  change (((translationSL (N:ℝ) • w):ℍ):ℂ)=_
  rw [coe_specialLinearGroup_apply]
  simp [translationSL,translation,add_comm]

private theorem q_shift (N n : ℕ) (w : ℍ) :
    Function.Periodic.qParam 1 ((shift N • w : ℍ):ℂ)^n =
      phase N n*Function.Periodic.qParam 1 (w:ℂ)^n := by
  rw [argument_shift]
  simp only [Function.Periodic.qParam,phase,e,div_one,←Complex.exp_nat_mul,←Complex.exp_add]
  push_cast <;> congr 1 <;> ring

theorem frameR_fricke (N r n : ℕ) [NeZero N] (f : Forms N r) :
    frameR N (NeZero.pos N) r f cuspOneMatrix n =
      phase N n*frameR N (NeZero.pos N) r (action N r f) 1 n := by
  let G := frameForm N (NeZero.pos N) r (action N r f) 1
  let F := frameForm N (NeZero.pos N) r f cuspOneMatrix
  let g := frameGroup N (NeZero.pos N) 1
  let fgroup := frameGroup N (NeZero.pos N) cuspOneMatrix
  have u : (1:ℝ)∈g.strictPeriods := normalized_frame_unit_strictPeriod N (NeZero.pos N) 1
  have v : (1:ℝ)∈fgroup.strictPeriods := normalized_frame_unit_strictPeriod N (NeZero.pos N) cuspOneMatrix
  letI : Fact (IsCusp OnePoint.infty g) :=
    ⟨g.isCusp_of_mem_strictPeriods (by norm_num : (0:ℝ)<1) u⟩
  letI : Fact (IsCusp OnePoint.infty fgroup) :=
    ⟨fgroup.isCusp_of_mem_strictPeriods (by norm_num : (0:ℝ)<1) v⟩
  have expansion (w : ℍ) :
      HasSum (fun k => (phase N k*(qExpansion 1 G).coeff k) •
        Function.Periodic.qParam 1 (w:ℂ)^k) (F w) := by
    change HasSum _ (frameForm N (NeZero.pos N) r f cuspOneMatrix w)
    rw [frame_one]
    apply (ModularForm.hasSum_qExpansion G (by norm_num : (0:ℝ)<1) u (shift N • w)).congr_fun
    intro k
    simp only [smul_eq_mul,q_shift]
    ring
  have T := ModularFormClass.qExpansion_coeff_unique (f:=F) (by norm_num : (0:ℝ)<1) v expansion n
  change phase N n*(qExpansion 1 (frameForm N (NeZero.pos N) r (action N r f) 1)).coeff n =
    (qExpansion 1 (frameForm N (NeZero.pos N) r f cuspOneMatrix)).coeff n at T
  simp only [frameR,holomorphicR_eq_qExpansion,←T]
  ring

end ImbalancedChen.Part3.OriginalHolomorphicFrickePhase20261113
end
