import ImbalancedChen.P4BOriginalActualRoughE3Payment

/-! SOURCE ONLY / UNCOMPILED. The CURRENT doubleStep upper/gap profiles
are used. The older ContDiffBump gap is not identified with them.
Native long blocks are strict-left/closed-right; unit atoms remain in
the short coordinates and are excluded as longs by the proved U>1. -/
namespace ImbalancedChen.P4BOriginalSharpLongProfiles
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap
open Part3.TwoLongQuantitativeTransitionProfiles
open Part3.TwoLongTransitionMellinN2
open Part3.PrimeMellinProfileVariation20261026b (phase phase_norm)
open Part3.TwoLongLiteralMellinModes (wideWindow N2)
open P4BOriginalCoprimeSmoothE1 (mass price)
open P5Z.HBRightClosedDyadicRoles (Block Owns)
open P5Z.ActualHBDyadicProductWindow (lower)

theorem current_endpoint_integral {delta : ℝ} (hd : 0<delta) (a : ℝ) :
    (∫ x : ℝ,endpoint delta a x)≤4*delta := by
  let S := Icc (a-2*delta) (a+2*delta)
  have hs : Function.support (endpoint delta a)⊆S := by
    intro x hx
    have H := doubleStep_support (a:=a-delta) (b:=a+delta) hd hx
    constructor <;> linarith [H.1,H.2]
  have hc : HasCompactSupport (endpoint delta a) :=
    isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc)
  have hi := (doubleStep_smooth delta (a-delta) (a+delta)).continuous.integrable_of_hasCompactSupport hc
  have heq : endpoint delta a=S.indicator (endpoint delta a) := by
    funext x
    by_cases hx : x∈S
    · simp [hx]
    · have hz : endpoint delta a x=0 := by by_contra h; exact hx (hs h)
      simp [hx,hz]
  rw [heq,integral_indicator measurableSet_Icc]
  calc
    _≤∫ _x in S,(1:ℝ) := setIntegral_mono_on hi.integrableOn continuous_const.integrableOn_Icc
      measurableSet_Icc (fun x hx => (doubleStep_range delta (a-delta) (a+delta) x).2)
    _=4*delta := by
      dsimp [S]
      rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le (by linarith : a-2*delta≤a+2*delta),
        intervalIntegral.integral_const,smul_eq_mul]
      ring

theorem current_gap_integral {delta : ℝ} (hd : 0<delta) : (∫ x : ℝ,gap delta x)≤8*delta := by
  have hi (a : ℝ) : Integrable (endpoint delta a) := by
    have hs : Function.support (endpoint delta a)⊆Icc (a-2*delta) (a+2*delta) := by
      intro x hx
      have H := doubleStep_support (a:=a-delta) (b:=a+delta) hd hx
      constructor <;> linarith [H.1,H.2]
    exact (doubleStep_smooth delta (a-delta) (a+delta)).continuous.integrable_of_hasCompactSupport
      (isCompact_Icc.of_isClosed_subset isClosed_closure (closure_minimal hs isClosed_Icc))
  unfold gap
  rw [integral_add (hi 1) (hi 2)]
  linarith [current_endpoint_integral hd 1,current_endpoint_integral hd 2]

theorem plain_profile (isGap : Bool) (delta U x : ℝ) :
    profile isGap false delta U 0 x=((if isGap then gap delta x else upper delta x):ℝ) := by
  cases isGap <;> simp [profile,twisted,amplitude,transition,logFactor,phase]

def stripProfile (isGap : Bool) {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) : 𝓢(ℝ,ℂ) :=
  profileSchwartz isGap false hd hs U 0

theorem stripProfile_apply (isGap : Bool) {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U x : ℝ) :
    stripProfile isGap hd hs U x=((if isGap then gap delta x else upper delta x):ℝ) :=
  plain_profile isGap delta U x

theorem stripProfile_support (isGap : Bool) {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    Function.support (stripProfile isGap hd hs U : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2) :=
  profile_support isGap false hd hs U 0

theorem strip_masses {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    ‖mass (stripProfile false hd hs U)‖≤2 ∧ ‖mass (stripProfile true hd hs U)‖≤8*delta := by
  constructor
  · apply (norm_integral_le_integral_norm _).trans
    have H := norm_integral_le_two (stripProfile false hd hs U).integrable
      (stripProfile_support false hd hs U) 1 (fun x hx => by
        simpa only [stripProfile_apply,if_false,Complex.norm_real,Real.norm_eq_abs] using upper_abs_le_one delta x)
    simpa using H
  · apply (norm_integral_le_integral_norm _).trans
    have he : (fun x : ℝ => ‖stripProfile true hd hs U x‖)=gap delta := by
      funext x
      simp only [stripProfile_apply,if_true,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gap_nonneg delta x)]
    rw [he]
    exact current_gap_integral hd

def stripPrice : ℝ := 2*Part3.TwoLongN2FourierDecay.fourierDecayConstant*(upperCost+gapCost)

theorem stripPrice_nonneg : 0≤stripPrice := by
  have h1 := Part3.TwoLongN2FourierDecay.fourierDecayConstant_pos.le
  have h2 := D_nonneg
  unfold stripPrice upperCost gapCost
  positivity

theorem strip_prices {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) (isGap : Bool) :
    price (stripProfile isGap hd hs U)≤stripPrice/delta^2 := by
  have hC := Part3.TwoLongN2FourierDecay.fourierDecayConstant_pos.le
  have hu : 0≤upperCost := by have H:=D_nonneg; unfold upperCost; positivity
  have hg := gapCost_nonneg
  have hN : N2 (stripProfile isGap hd hs U : ℝ→ℂ)≤(upperCost+gapCost)/delta^2 := by
    cases isGap
    · have he : (stripProfile false hd hs U : ℝ→ℂ)=fun x => (upper delta x:ℂ) := by
        funext x; exact stripProfile_apply false hd hs U x
      rw [he]
      exact (upper_N2 hd hs).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))
    · have he : (stripProfile true hd hs U : ℝ→ℂ)=fun x => (gap delta x:ℂ) := by
        funext x; exact stripProfile_apply true hd hs U x
      rw [he]
      exact (gap_N2 hd hs).trans (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))
  exact (mul_le_mul_of_nonneg_left hN (mul_nonneg (by norm_num) hC)).trans_eq (by unfold stripPrice; ring)

theorem owns_iff_Ioc {b : Block} (hlarge : (1:ℝ)<lower b) (n : ℕ) :
    Owns b n ↔ (n:ℝ)/(lower b:ℝ)∈Ioc (1:ℝ) 2 := by
  cases b with
  | unit => simp [lower] at hlarge
  | dyadic j =>
      simp only [Owns,lower,Nat.cast_pow,Nat.cast_ofNat]
      have hp : (0:ℝ)<(2:ℝ)^j := by positivity
      constructor
      · intro hn
        rcases hn with ⟨hlo,hhi⟩
        constructor
        · apply (lt_div_iff₀ hp).mpr
          exact_mod_cast hlo
        · apply (div_le_iff₀ hp).mpr
          simpa only [lower,pow_succ,mul_comm] using (show (n:ℝ)≤(2:ℝ)^(j+1) by exact_mod_cast hhi)
      · intro hn
        constructor
        · exact_mod_cast ((lt_div_iff₀ hp).mp hn.1)
        · have H := (div_le_iff₀ hp).mp hn.2
          exact_mod_cast (show (n:ℝ)≤(2:ℝ)^(j+1) by simpa only [pow_succ,mul_comm] using H)

def sharpProfile (isLog : Bool) (U t x : ℝ) : ℂ :=
  ((sharp x*logFactor isLog U x:ℝ):ℂ)*phase t x

def stripShape (delta z w : ℝ) : ℝ := gap delta z*upper delta w+upper delta z*gap delta w

theorem stripShape_nonneg (delta z w : ℝ) : 0≤stripShape delta z w :=
  add_nonneg (mul_nonneg (gap_nonneg _ _) (doubleStep_range delta 1 2 w).1)
    (mul_nonneg (doubleStep_range delta 1 2 z).1 (gap_nonneg _ _))

theorem stripShape_support {delta z w : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (h : stripShape delta z w≠0) : z∈window ∧ w∈window := by
  by_cases h1 : gap delta z*upper delta w=0
  · have h2 : upper delta z*gap delta w≠0 := by intro h2; exact h (by simp [stripShape,h1,h2])
    exact ⟨upper_support hd hs (mul_ne_zero_iff.mp h2).1,gap_support hd hs (mul_ne_zero_iff.mp h2).2⟩
  · exact ⟨gap_support hd hs (mul_ne_zero_iff.mp h1).1,upper_support hd hs (mul_ne_zero_iff.mp h1).2⟩

theorem sharp_pair_profile_error (log1 log2 : Bool) {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (U V t1 t2 z w : ℝ) :
    ‖sharpProfile log1 U t1 z*sharpProfile log2 V t2 w-
      profile false log1 delta U t1 z*profile false log2 delta V t2 w‖≤
      logSize U*logSize V*stripShape delta z w := by
  have H := rectangle_error hd z w
  have he : ‖sharpProfile log1 U t1 z*sharpProfile log2 V t2 w-
      profile false log1 delta U t1 z*profile false log2 delta V t2 w‖=
      |logFactor log1 U z|*|logFactor log2 V w|*(upper delta z*upper delta w-sharp z*sharp w) := by
    have hid : sharpProfile log1 U t1 z*sharpProfile log2 V t2 w-
        profile false log1 delta U t1 z*profile false log2 delta V t2 w=
        ((logFactor log1 U z:ℝ):ℂ)*((logFactor log2 V w:ℝ):ℂ)*phase t1 z*phase t2 w*
          ((sharp z*sharp w-upper delta z*upper delta w:ℝ):ℂ) := by
      simp only [sharpProfile,profile,twisted,amplitude,transition,Bool.false_eq_true,if_false]
      push_cast
      ring
    rw [hid]
    simp only [norm_mul,phase_norm,mul_one,Complex.norm_real,Real.norm_eq_abs]
    have hab : |sharp z*sharp w-upper delta z*upper delta w|=upper delta z*upper delta w-sharp z*sharp w := by
      rw [abs_of_nonpos (by linarith [H.1])]; ring
    rw [hab]
  rw [he]
  by_cases hzero : stripShape delta z w=0
  · have hz : upper delta z*upper delta w-sharp z*sharp w=0 := by
      have H2 : upper delta z*upper delta w-sharp z*sharp w≤stripShape delta z w := H.2
      rw [hzero] at H2
      linarith [H.1,H2]
    simp [hz,hzero]
  · obtain ⟨hz,hw⟩ := stripShape_support hd hs hzero
    exact mul_le_mul (mul_le_mul (logFactor_bounds log1 U hz).1 (logFactor_bounds log2 V hw).1
      (abs_nonneg _) (zero_le_one.trans (logSize_one_le U))) H.2 H.1
      (mul_nonneg (zero_le_one.trans (logSize_one_le U)) (zero_le_one.trans (logSize_one_le V)))

end
end ImbalancedChen.P4BOriginalSharpLongProfiles
