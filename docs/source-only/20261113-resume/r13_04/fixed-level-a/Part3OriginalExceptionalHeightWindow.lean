import ImbalancedChen.Part3ActualUnitBandHeightSeeds
import ImbalancedChen.Part3OriginalContinuousPoincarePackets
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Batteries.Tactic.OpenPrivate

/-! One fixed nonnegative plateau for all signed marks, both cusps and every
positive level. The square-root height is the one in the original Whittaker
expansion. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalExceptionalHeightWindow20261112
open Set MeasureTheory Complex
open scoped Topology Distributions ContDiff
open SmoothZeroHeightSeedProfiles20261026b ActualLogHorocycleAdjoint20261112
open OriginalContinuousPoincarePackets20261110
open private exp_half from ImbalancedChen.Part3ActualUnitBandHeightSeeds

def bump (u : ℝ) : ℝ := Real.smoothTransition (4*(u-1))*Real.smoothTransition (4*(2-u))
theorem bump_bounds (u : ℝ) : 0≤bump u ∧ bump u≤1 :=
  ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _),
   mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)⟩
theorem bump_smooth : ContDiff ℝ ∞ bump := by unfold bump;fun_prop
theorem bump_left {u : ℝ} (hu : u≤1) : bump u=0 := by
  simp [bump,Real.smoothTransition.zero_of_nonpos (show 4*(u-1)≤0 by linarith)]
theorem bump_right {u : ℝ} (hu : 2≤u) : bump u=0 := by
  simp [bump,Real.smoothTransition.zero_of_nonpos (show 4*(2-u)≤0 by linarith)]
theorem bump_inside {u : ℝ} (hu : bump u≠0) : 1<u ∧ u<2 :=
  ⟨lt_of_not_ge (fun h => hu (bump_left h)),lt_of_not_ge (fun h => hu (bump_right h))⟩
theorem bump_plateau {u : ℝ} (h₁ : 5/4≤u) (h₂ : u≤7/4) : bump u=1 := by
  simp [bump,Real.smoothTransition.one_of_one_le (show 1≤4*(u-1) by linarith),
    Real.smoothTransition.one_of_one_le (show 1≤4*(2-u) by linarith)]

private def profile (C : ℝ) : LogTest where
  toFun v := (bump (C*Real.exp v):ℂ)
  contDiff' := Complex.ofRealCLM.contDiff.comp (bump_smooth.comp (by fun_prop))
  hasCompactSupport' := by
    by_cases hc : 0<C
    · apply HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc : IsCompact (Icc (Real.log (1/C)) (Real.log (2/C))))
      intro v hv
      have h := bump_inside (show bump (C*Real.exp v)≠0 from fun h => hv (by simp [h]))
      have lo : 1/C<Real.exp v := (div_lt_iff₀ hc).mpr (by linarith [h.1])
      have hi : Real.exp v<2/C := (lt_div_iff₀ hc).mpr (by linarith [h.2])
      exact ⟨(Real.log_lt_iff_lt_exp (by positivity)).mpr lo |>.le,
        (Real.lt_log_iff_exp_lt (by positivity)).mpr hi |>.le⟩
    · have Z : (fun v : ℝ => (bump (C*Real.exp v):ℂ))=0 := by
        funext v
        simp only [Pi.zero_apply,Complex.ofReal_eq_zero]
        exact bump_left ((mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc) (Real.exp_pos _).le).trans zero_le_one)
      rw [Z];exact HasCompactSupport.zero
  tsupport_subset' := subset_univ _

def seed (C : ℝ) : SmoothHeightSeed := fromLog (profile C)

theorem seed_pos_height (C : ℝ) {y : ℝ} (hy : 0<y) :
    (seed C).toFun y=((Real.sqrt y*bump (C*y):ℝ):ℂ) := by
  have S := fromLog_exp (profile C) (Real.log y)
  rw [Real.exp_log hy,exp_half y hy] at S
  simpa only [seed,profile,Real.exp_log hy,Complex.ofReal_mul] using S

theorem seed_scaling (H : ℝ) (m : ℤ) (hm : m≠0) :
    (seed (H*|(m:ℝ)|)).toFun=scaledSeed m (seed H).toFun := by
  have p : 0<|(m:ℝ)| := abs_pos.mpr (by exact_mod_cast hm)
  funext y
  by_cases hy : 0<y
  · rw [scaledSeed,seed_pos_height _ hy,seed_pos_height _ (mul_pos p hy),Real.sqrt_mul p.le,
      ←mul_assoc H]
    push_cast
    have h : (Real.sqrt |(m:ℝ)|:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr p).ne'
    field_simp [h] <;>ring
  · have zero (C y : ℝ) (hy : ¬0<y) : (seed C).toFun y=0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hy ((seed C).positive h))
    rw [zero _ _ hy,scaledSeed,zero _ _ (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos p.le (le_of_not_gt hy))),mul_zero]

theorem probe_common (H : ℝ) (m : ℤ) (hm : m≠0) (ν : ℂ) :
    orderProbe m (seed (H*|(m:ℝ)|)).toFun ν=orderProbe 1 (seed H).toFun ν := by
  rw [seed_scaling H m hm,common_orderProbe m hm]

def bottom (H L : ℝ) : ℝ := 1/(2*L*H)
theorem bottom_pos {H L : ℝ} (hH : 0<H) (hL : 0<L) : 0<bottom H L := by unfold bottom;positivity

theorem seed_band {H L : ℝ} (hH : 0<H) (hL : 0<L) {m : ℤ}
    (low : L≤|(m:ℝ)|) (high : |(m:ℝ)|≤2*L) {y : ℝ} (hy : 0<y)
    (ne : (seed (H*|(m:ℝ)|)).toFun y≠0) :
    bottom H L≤y ∧ y≤4*bottom H L := by
  have h := bump_inside (show bump (H*|(m:ℝ)|*y)≠0 from fun h => ne (by simp [seed_pos_height _ hy,h]))
  have a := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left high hH.le) hy.le
  have b := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left low hH.le) hy.le
  constructor
  · exact (div_le_iff₀ (by positivity)).mpr (by nlinarith only [a,h.1])
  · unfold bottom
    rw [show 4*(1/(2*L*H))=2/(L*H) by field_simp [hH.ne',hL.ne'] <;> ring]
    exact (le_div_iff₀ (mul_pos hL hH)).mpr (by nlinarith only [b,h.2])

theorem seed_sq_le {H L : ℝ} (hH : 0<H) (hL : 0<L) {m : ℤ}
    (low : L≤|(m:ℝ)|) (high : |(m:ℝ)|≤2*L) {y : ℝ} (hy : 0<y) :
    ‖(seed (H*|(m:ℝ)|)).toFun y‖^2≤4*bottom H L := by
  by_cases ne : (seed (H*|(m:ℝ)|)).toFun y=0
  · simp [ne,(bottom_pos hH hL).le]
  · have B := bump_bounds (H*|(m:ℝ)|*y)
    rw [seed_pos_height _ hy,Complex.norm_real,Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) B.1),mul_pow,
      Real.sq_sqrt hy.le]
    exact (mul_le_of_le_one_right hy.le (pow_le_one₀ B.1 B.2)).trans (seed_band hH hL low high hy ne).2

end ImbalancedChen.Part3.OriginalExceptionalHeightWindow20261112
end
