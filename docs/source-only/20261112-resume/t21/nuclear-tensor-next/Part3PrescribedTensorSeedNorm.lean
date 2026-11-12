import ImbalancedChen.Part3PrescribedLogTensorExpansion
import ImbalancedChen.Part3ActualUnitBandSeedBudget
import ImbalancedChen.Part3ActualKProfileL2Continuity
import Batteries.Tactic.OpenPrivate

/-! Height translation of the one fixed positive window, at the exact
normalization of the two manuscript Poincaré packets. -/
namespace ImbalancedChen.Part3.PrescribedTensorSeedNorm20261112
noncomputable section
open Set Filter MeasureTheory Complex UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane Topology BigOperators Distributions ContDiff
open PrescribedLogTensorWindows20261112
open ActualSignedPoincareEnvelope20261112 ActualHorocycleSynthesisBound20261112
open ActualLogHorocycleAdjoint20261112 AngularFourierUnitary20261026b
open SmoothZeroHeightSeedProfiles20261026b ActualIncompleteEisensteinTransform20261110
open ActualResidualVolumeNormalization20261110 OriginalContinuousPoincarePackets20261110
open NormalizedCuspCompactPoincare20261026b ActualContinuousPoincarePairing20261110
open private moment_from_log from ImbalancedChen.Part3ActualUnitBandSeedBudget
open private exp_half from ImbalancedChen.Part3ActualUnitBandHeightSeeds
open private lp_norm_sq_eq_integral_norm_sq from ImbalancedChen.Part3ActualKProfileL2Continuity

def probe (right : Bool) (i k : ℤ) := if right then rightPattern i k else pattern i k

theorem probe_test (right : Bool) (i k : ℤ) :
    Continuous (probe right i k) ∧ HasCompactSupport (probe right i k) ∧
      tsupport (probe right i k) ⊆ Ioi (0:ℝ) := by
  cases right
  · exact pattern_test i k
  · exact right_test i k

theorem probe_norm (right : Bool) (i k : ℤ) (y : ℝ) :
    ‖probe right i k y‖ = if 0 < y then win (Real.log y-(i:ℝ)) else 0 := by
  cases right
  · exact pattern_norm i k y
  · rw [show probe true i k=rightPattern i k by rfl,right_norm,pattern_norm]

def base (u : ℝ) : ℂ := (Real.exp (-u/2)*win u : ℝ)
def amp (i : ℤ) := Real.exp (-(i:ℝ)/2)
def shift (m i : ℤ) := Real.log |(m:ℝ)|-(i:ℝ)
def logWindow (m i : ℤ) : LogTest where
  toFun u := (amp i : ℂ)*base (u+shift m i)
  contDiff' := by
    have h : ContDiff ℝ ∞ base := Complex.ofRealCLM.contDiff.comp ((by fun_prop : ContDiff ℝ ∞
      (fun u : ℝ => Real.exp (-u/2))).mul win_smooth)
    exact contDiff_const.mul (h.comp (contDiff_id.add contDiff_const))
  hasCompactSupport' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_Icc : IsCompact (Icc (-2-shift m i) (2-shift m i)))
    intro u hu
    have hw : win (u+shift m i) ≠ 0 := by intro z; exact hu (by simp [base,z])
    obtain ⟨h₁,h₂⟩ := win_nonzero hw
    exact ⟨by linarith,by linarith⟩
  tsupport_subset' := subset_univ _

def envelope (m i : ℤ) := fromLog (logWindow m i)

private theorem envelope_at (m i : ℤ) (hm : m ≠ 0) (y : ℝ) :
    (envelope m i).toFun y = if 0 < y then
      ((Real.sqrt |(m:ℝ)|)⁻¹*win (Real.log (|(m:ℝ)|*y)-(i:ℝ)) : ℝ) else 0 := by
  have hM : 0 < |(m:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  by_cases hy : 0 < y
  · rw [if_pos hy,← Real.exp_log hy]
    simp only [envelope,fromLog_exp,logWindow,base,amp,shift]
    rw [Real.log_mul hM.ne' (Real.exp_pos _).ne',Real.log_exp]
    have E : Real.exp (Real.log y/2)*Real.exp (-(i:ℝ)/2)*
        Real.exp (-(Real.log y+(Real.log |(m:ℝ)|-(i:ℝ)))/2) = (Real.sqrt |(m:ℝ)|)⁻¹ := by
      rw [← Real.exp_add,← Real.exp_add,show Real.log y/2+ -(i:ℝ)/2+
        -(Real.log y+(Real.log |(m:ℝ)|-(i:ℝ)))/2 = -(Real.log |(m:ℝ)|/2) by ring,
        Real.exp_neg,exp_half _ hM]
    rw [show Real.log |(m:ℝ)|+Real.log y-(i:ℝ) = Real.log y+(Real.log |(m:ℝ)|-(i:ℝ)) by ring,← E]
    push_cast; ring
  · rw [if_neg hy]
    exact image_eq_zero_of_notMem_tsupport (fun h => hy ((envelope m i).positive h))

private theorem envelope_real (m i : ℤ) (hm : m≠0) (y : ℝ) :
    (envelope m i).toFun y = (‖(envelope m i).toFun y‖ : ℂ) := by
  rw [envelope_at m i hm]
  split_ifs
  · rw [Complex.norm_real,Real.norm_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (win_bounds _).1)]
  · simp

theorem scaled_norm (m i k : ℤ) (hm : m≠0) (right : Bool) (y : ℝ) :
    ‖scaledSeed m (probe right i k) y‖ = ‖(envelope m i).toFun y‖ := by
  have hM : 0 < |(m:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  rw [scaledSeed,norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),
    probe_norm,envelope_at m i hm]
  by_cases hy : 0 < y
  · rw [if_pos hy,if_pos (mul_pos hM hy),Complex.norm_real,Real.norm_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (win_bounds _).1)]
  · simp [hy,not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hM.le (le_of_not_gt hy))]

def baseEnergy : ℝ := ∫ u : ℝ, ‖base u‖^2
def baseMoment : ℂ := ∫ u : ℝ, (Real.exp (-u/2) : ℂ)*star (base u)

theorem log_energy (m i : ℤ) :
    ‖logVector (envelope m i)‖^2 = (amp i)^2*baseEnergy := by
  rw [envelope,logVector_fromLog,lp_norm_sq_eq_integral_norm_sq]
  calc
    _ = ∫ u : ℝ, (amp i)^2*‖base (u+shift m i)‖^2 := by
      apply integral_congr_ae
      filter_upwards [test_ae (logWindow m i)] with u h
      rw [h]; change ‖(amp i:ℂ)*_‖^2=_
      rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
    _ = _ := by rw [integral_const_mul,integral_add_right_eq_self]; rfl

theorem log_moment (m i : ℤ) :
    moment (envelope m i).toHeightSeed 0 =
      (Real.exp ((Real.log |(m:ℝ)|)/2)*Real.exp (-(i:ℝ)) : ℝ)*baseMoment := by
  rw [envelope,moment_from_log]
  let T := fun u : ℝ => (Real.exp (-u/2):ℂ)*star (base u)
  let S := Real.exp (Real.log |(m:ℝ)|/2)*Real.exp (-(i:ℝ))
  have E (u : ℝ) : Real.exp (-u/2)*amp i = S*Real.exp (-(u+shift m i)/2) := by
    dsimp [S,amp,shift]; rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; congr 1; ring
  calc
    _ = ∫ u : ℝ, (S:ℂ)*T (u+shift m i) := by
      apply integral_congr_ae; apply ae_of_all; intro u
      change (Real.exp (-u/2):ℂ)*star ((amp i:ℂ)*base (u+shift m i))=_
      simp only [T,star_mul',Complex.star_def,Complex.conj_ofReal]
      have e := congrArg Complex.ofReal (E u)
      push_cast at e
      linear_combination conj (base (u+shift m i))*e
    _ = _ := by rw [integral_const_mul,integral_add_right_eq_self]; rfl

def price (i : ℤ) := amp i+Real.exp (-(i:ℝ))
theorem price_nonneg (i : ℤ) : 0 ≤ price i := add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
theorem price_growth (i : ℤ) : price i ≤ 2*Real.exp |(i:ℝ)| := by
  have h := neg_le_abs (i:ℝ)
  have a : -(i:ℝ)/2 ≤ |(i:ℝ)| := by linarith [abs_nonneg (i:ℝ)]
  exact (add_le_add (Real.exp_le_exp.mpr a) (Real.exp_le_exp.mpr h)).trans_eq (two_mul _).symm

/-- The constant depends on level and the original signed dilation only. -/
theorem scaled_frame_budget (N : ℕ) [NeZero N] (m : ℤ) (hm : m≠0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : SL(2,ℤ)) (right : Bool) (i k : ℤ),
      let h := probe_test right i k
      let t := scaled_test m hm _ h.1 h.2.1 h.2.2
      ‖framedVector N g m (scaledSeed m (probe right i k)) t.1 t.2.1 t.2.2‖ ≤ C*price i := by
  let D := |actualVolume N|⁻¹*(Real.exp (Real.log |(m:ℝ)|/2)*‖baseMoment‖)^2
  have hB : 0 ≤ baseEnergy := integral_nonneg (fun _ => sq_nonneg _)
  have hD : 0 ≤ D := mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (sq_nonneg _)
  let C := Real.sqrt (2*baseEnergy+D)
  refine ⟨C,Real.sqrt_nonneg _,?_⟩
  intro g right i k
  let h := probe_test right i k
  let t := scaled_test m hm _ h.1 h.2.1 h.2.2
  have H := signed_envelope_norm_sq N g m (scaledSeed m (probe right i k)) t.1 t.2.1 t.2.2
    (envelope m i) (envelope_real m i hm) (fun y => (scaled_norm m i k hm right y).le)
  rw [log_energy,log_moment,norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)] at H
  have E : |actualVolume N|⁻¹*((Real.exp (Real.log |(m:ℝ)|/2)*Real.exp (-(i:ℝ)))*‖baseMoment‖)^2
    = D*(Real.exp (-(i:ℝ)))^2 := by dsimp [D]; ring
  rw [E] at H
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (price_nonneg i))).mp
  rw [mul_pow,show C^2=2*baseEnergy+D from Real.sq_sqrt (by linarith)]
  have a : amp i≤price i := le_add_of_nonneg_right (Real.exp_pos _).le
  have b : Real.exp (-(i:ℝ))≤price i := le_add_of_nonneg_left (Real.exp_pos _).le
  have a' := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Real.exp_pos _).le (price_nonneg i)).mpr a)
    (mul_nonneg (by norm_num : (0:ℝ)≤2) hB)
  have b' := mul_le_mul_of_nonneg_left ((sq_le_sq₀ (Real.exp_pos _).le (price_nonneg i)).mpr b) hD
  linarith only [H,a',b']
end
end ImbalancedChen.Part3.PrescribedTensorSeedNorm20261112
