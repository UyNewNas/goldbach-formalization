import Mathlib
import ImbalancedChen.Part3TwoLongLiteralMellinModes

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Legitimate smooth upper/endpoint-strip profiles for the original (a,b]
long intervals. The cutoff and strip functions are CONSTRUCTED from
Mathlib bumps. Their pointwise interval/rectangle inequalities and C2
compact norm guards are proved, with no analytic-witness assumption.
A quantitative uniform delta^-2 N2 bound remains separate.
-/
namespace ImbalancedChen.Part3.TwoLongActualSmoothStripWitness
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators Topology
open ImbalancedChen.Part3.TwoLongLiteralMellinModes

/-- Upper cutoff equal to one on [a,b], supported in (a-delta,b+delta). -/
def intervalBump (a b delta : ℝ) (hab : a < b) (hd : 0 < delta) :
    ContDiffBump ((a+b)/2) where
  rIn := (b-a)/2
  rOut := (b-a)/2 + delta
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

def upper (a b delta : ℝ) (hab : a < b) (hd : 0 < delta) (x : ℝ) : ℝ :=
  intervalBump a b delta hab hd x

/-- One endpoint strip, one on the delta-neighborhood, zero outside 2delta. -/
def endpointBump (a delta : ℝ) (hd : 0 < delta) : ContDiffBump a where
  rIn := delta
  rOut := 2*delta
  rIn_pos := hd
  rIn_lt_rOut := by linarith

def gap (a b delta : ℝ) (hd : 0 < delta) (x : ℝ) : ℝ :=
  endpointBump a delta hd x + endpointBump b delta hd x

def sharp (a b x : ℝ) : ℝ := if x ∈ Ioc a b then 1 else 0

theorem upper_nonneg (a b delta : ℝ) (hab : a < b) (hd : 0 < delta) (x : ℝ) :
    0 ≤ upper a b delta hab hd x := (intervalBump a b delta hab hd).nonneg

theorem upper_le_one (a b delta : ℝ) (hab : a < b) (hd : 0 < delta) (x : ℝ) :
    upper a b delta hab hd x ≤ 1 := (intervalBump a b delta hab hd).le_one

theorem gap_nonneg (a b delta : ℝ) (hd : 0 < delta) (x : ℝ) :
    0 ≤ gap a b delta hd x :=
  add_nonneg (endpointBump a delta hd).nonneg (endpointBump b delta hd).nonneg

theorem upper_one {a b delta x : ℝ} (hab : a < b) (hd : 0 < delta)
    (hx : x ∈ Icc a b) : upper a b delta hab hd x = 1 := by
  apply (intervalBump a b delta hab hd).one_of_mem_closedBall
  change dist x ((a+b)/2) ≤ (b-a)/2
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [hx.1,hx.2]

theorem upper_support {a b delta : ℝ} (hab : a < b) (hd : 0 < delta) :
    Function.support (upper a b delta hab hd) ⊆ Icc (a-delta) (b+delta) := by
  intro x hx
  have h : x ∈ Metric.ball ((a+b)/2) ((b-a)/2+delta) := by
    change x ∈ Function.support (intervalBump a b delta hab hd) at hx
    rw [(intervalBump a b delta hab hd).support_eq] at hx
    exact hx
  have hs := abs_lt.mp (show |x-(a+b)/2| < (b-a)/2+delta by
    simpa only [Metric.mem_ball,Real.dist_eq] using h)
  constructor <;> linarith [hs.1,hs.2]


theorem endpoint_support (a delta : ℝ) (hd : 0 < delta) :
    Function.support (endpointBump a delta hd) ⊆ Icc (a-2*delta) (a+2*delta) := by
  intro x hx
  rw [(endpointBump a delta hd).support_eq] at hx
  have hs := abs_lt.mp (show |x-a| < 2*delta by
    simpa only [Metric.mem_ball,Real.dist_eq] using hx)
  constructor <;> linarith [hs.1,hs.2]

theorem gap_support {a b delta : ℝ} (hab : a ≤ b) (hd : 0 < delta) :
    Function.support (gap a b delta hd) ⊆ Icc (a-2*delta) (b+2*delta) := by
  intro x hx
  by_cases ha : endpointBump a delta hd x = 0
  · have hb : endpointBump b delta hd x ≠ 0 := by
      intro hb
      exact hx (by simp [gap,ha,hb])
    have hs := endpoint_support b delta hd hb
    constructor <;> linarith [hs.1,hs.2]
  · have hs := endpoint_support a delta hd ha
    constructor <;> linarith [hs.1,hs.2]

def normalizedUpper (delta : ℝ) (hd : 0 < delta) : ℝ → ℝ :=
  upper 1 2 delta (by norm_num) hd

def normalizedGap (delta : ℝ) (hd : 0 < delta) : ℝ → ℝ := gap 1 2 delta hd

/-- Actual profiles with the precise fixed support required by P2. -/
theorem normalizedUpper_support {delta : ℝ} (hd : 0 < delta) (hsmall : delta ≤ 1/4) :
    Function.support (normalizedUpper delta hd) ⊆ Icc (1/2 : ℝ) (5/2) := by
  intro x hx
  have hs := upper_support (by norm_num : (1 : ℝ) < 2) hd hx
  constructor <;> linarith [hs.1,hs.2]

theorem normalizedGap_support {delta : ℝ} (hd : 0 < delta) (hsmall : delta ≤ 1/4) :
    Function.support (normalizedGap delta hd) ⊆ Icc (1/2 : ℝ) (5/2) := by
  intro x hx
  have hs := gap_support (by norm_num : (1 : ℝ) ≤ 2) hd hx
  constructor <;> linarith [hs.1,hs.2]

/-- The strict-left/closed-right convention is kept literally. In
particular x=a is paid by the LEFT endpoint strip. -/
theorem sharp_le_upper {a b delta : ℝ} (hab : a < b) (hd : 0 < delta) (x : ℝ) :
    0 ≤ sharp a b x ∧ sharp a b x ≤ upper a b delta hab hd x := by
  by_cases hx : x ∈ Ioc a b
  · rw [sharp, if_pos hx, upper_one hab hd ⟨hx.1.le,hx.2⟩]
    exact ⟨by norm_num,le_rfl⟩
  · rw [sharp,if_neg hx]
    exact ⟨le_rfl,upper_nonneg _ _ _ hab hd x⟩

theorem upper_sharp_error {a b delta : ℝ} (hab : a < b) (hd : 0 < delta) (x : ℝ) :
    |upper a b delta hab hd x - sharp a b x| ≤ gap a b delta hd x := by
  by_cases hx : x ∈ Ioc a b
  · rw [sharp,if_pos hx,upper_one hab hd ⟨hx.1.le,hx.2⟩,sub_self,abs_zero]
    exact gap_nonneg _ _ _ hd x
  · rw [sharp,if_neg hx,sub_zero,abs_of_nonneg (upper_nonneg _ _ _ hab hd x)]
    by_cases hh : upper a b delta hab hd x = 0
    · rw [hh]; exact gap_nonneg _ _ _ hd x
    have hs := upper_support hab hd hh
    have hout : x ≤ a ∨ b < x := by
      by_cases ha : x ≤ a
      · exact Or.inl ha
      · exact Or.inr (lt_of_not_ge (fun hb => hx ⟨lt_of_not_ge ha,hb⟩))
    rcases hout with hleft | hright
    · have hmem : x ∈ Metric.closedBall a delta := by
        change dist x a ≤ delta
        rw [Real.dist_eq,abs_le]
        constructor <;> linarith [hs.1]
      have hone := (endpointBump a delta hd).one_of_mem_closedBall hmem
      have hother := (endpointBump b delta hd).nonneg (x := x)
      have hu := upper_le_one _ _ _ hab hd x
      dsimp [gap]
      rw [hone]
      linarith
    · have hmem : x ∈ Metric.closedBall b delta := by
        change dist x b ≤ delta
        rw [Real.dist_eq,abs_le]
        constructor <;> linarith [hs.2]
      have hone := (endpointBump b delta hd).one_of_mem_closedBall hmem
      have hother := (endpointBump a delta hd).nonneg (x := x)
      have hu := upper_le_one _ _ _ hab hd x
      dsimp [gap]
      rw [hone]
      linarith

/-- The precise two nonnegative endpoint errors behind the original
upper/gap1/gap2 Brun rectangle decomposition. -/
theorem rectangle_error {a b c d delta : ℝ} (hab : a < b) (hcd : c < d)
    (hd : 0 < delta) (x y : ℝ) :
    0 ≤ upper a b delta hab hd x * upper c d delta hcd hd y -
      sharp a b x * sharp c d y ∧
    upper a b delta hab hd x * upper c d delta hcd hd y -
      sharp a b x * sharp c d y ≤
      gap a b delta hd x * upper c d delta hcd hd y +
        upper a b delta hab hd x * gap c d delta hd y := by
  have hs₁ := sharp_le_upper hab hd x
  have hs₂ := sharp_le_upper hcd hd y
  have hu₁ := upper_nonneg _ _ _ hab hd x
  have hu₂ := upper_nonneg _ _ _ hcd hd y
  have hk₁ := gap_nonneg a b delta hd x
  have hk₂ := gap_nonneg c d delta hd y
  have he₁ := (le_abs_self _).trans (upper_sharp_error hab hd x)
  have he₂ := (le_abs_self _).trans (upper_sharp_error hcd hd y)
  constructor
  · exact sub_nonneg.mpr (mul_le_mul hs₁.2 hs₂.2 hs₂.1 hu₁)
  · have h1 := mul_le_mul_of_nonneg_right he₁ hu₂
    have h2 := mul_le_mul_of_nonneg_left he₂ hs₁.1
    have h3 := mul_le_mul_of_nonneg_right hs₁.2 hk₂
    nlinarith only [h1,h2,h3]

theorem upper_smooth {a b delta : ℝ} (hab : a < b) (hd : 0 < delta) :
    ContDiff ℝ ∞ (upper a b delta hab hd) := (intervalBump a b delta hab hd).contDiff

theorem upper_compact {a b delta : ℝ} (hab : a < b) (hd : 0 < delta) :
    HasCompactSupport (upper a b delta hab hd) := (intervalBump a b delta hab hd).hasCompactSupport

theorem gap_smooth (a b delta : ℝ) (hd : 0 < delta) : ContDiff ℝ ∞ (gap a b delta hd) :=
  (endpointBump a delta hd).contDiff.add (endpointBump b delta hd).contDiff

theorem gap_compact (a b delta : ℝ) (hd : 0 < delta) : HasCompactSupport (gap a b delta hd) :=
  (endpointBump a delta hd).hasCompactSupport.add (endpointBump b delta hd).hasCompactSupport


/-- The endpoint-strip mass has the manuscript's actual O(delta) size,
proved from the constructed support and 0<=bump<=1. -/
theorem endpoint_integral_le (a delta : ℝ) (hd : 0 < delta) :
    (∫ x : ℝ, endpointBump a delta hd x) ≤ 4*delta := by
  let B := endpointBump a delta hd
  let S := Icc (a-2*delta) (a+2*delta)
  have hI : Integrable (fun x : ℝ => B x) :=
    B.continuous.integrable_of_hasCompactSupport B.hasCompactSupport
  have hzero (x : ℝ) (hx : x ∉ S) : B x = 0 := by
    by_contra hn
    have hb : x ∈ Metric.ball a (2*delta) := by
      rw [← B.support_eq]
      exact hn
    have hh := abs_lt.mp (show |x-a| < 2*delta by
      simpa only [Metric.mem_ball,Real.dist_eq] using hb)
    apply hx
    constructor <;> linarith [hh.1,hh.2]
  have heq : (fun x : ℝ => B x) = S.indicator (fun x => B x) := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx,hzero x hx]
  calc
    _ = ∫ x in S, B x := by rw [heq,integral_indicator measurableSet_Icc]
    _ ≤ ∫ x in S, (1 : ℝ) := by
      apply setIntegral_mono_on hI.integrableOn continuous_const.integrableOn_Icc
        measurableSet_Icc
      intro x hx
      exact B.le_one
    _ = 4*delta := by
      unfold S
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : a-2*delta ≤ a+2*delta),
        intervalIntegral.integral_const,smul_eq_mul]
      ring

theorem gap_integral_le (a b delta : ℝ) (hd : 0 < delta) :
    (∫ x : ℝ, gap a b delta hd x) ≤ 8*delta := by
  have hI₁ := (endpointBump a delta hd).continuous.integrable_of_hasCompactSupport
    (endpointBump a delta hd).hasCompactSupport
  have hI₂ := (endpointBump b delta hd).continuous.integrable_of_hasCompactSupport
    (endpointBump b delta hd).hasCompactSupport
  unfold gap
  rw [integral_add hI₁ hI₂]
  linarith [endpoint_integral_le a delta hd,endpoint_integral_le b delta hd]

/-- Each constructed actual real profile supplies the C2/compact and N2
integrability guards, before requesting any quantitative delta power. -/
theorem smooth_compact_N2_guard {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ContDiff ℝ 2 (fun x => (f x : ℂ)) ∧
      Integrable (fun x => ‖(f x : ℂ)‖) ∧
      Integrable (fun x => ‖deriv (deriv (fun y => (f y : ℂ))) x‖) := by
  have hfc : ContDiff ℝ ∞ (fun x => (f x : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hcc : HasCompactSupport (fun x => (f x : ℂ)) := by
    change IsCompact (closure (Function.support (fun x => (f x : ℂ))))
    have hs : Function.support (fun x => (f x : ℂ)) = Function.support f := by
      ext x; simp
    rw [hs]
    exact hc
  have hd1 := (contDiff_infty_iff_deriv.mp hfc).2
  have hd2 := (contDiff_infty_iff_deriv.mp hd1).2
  exact ⟨hfc.of_le (by norm_num),
    (hfc.continuous.integrable_of_hasCompactSupport hcc).norm,
    (hd2.continuous.integrable_of_hasCompactSupport hcc.deriv.deriv).norm⟩

end
end ImbalancedChen.Part3.TwoLongActualSmoothStripWitness
