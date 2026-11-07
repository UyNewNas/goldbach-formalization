import MathlibNt.SieveTheory.LiLiuGoldbachOrdinaryLowerDensityFactors
import ImbalancedChen.Part5RenewalTablePrimitive

/-!
SOURCE ONLY / UNCOMPILED.

The actual constructed JR lower function, with the manuscript normalization,
has its zero anchor at two. Its delayed primitive starts at ONE. The adopted
H248 table enters only through its proved real integral primitive. No sieve
count estimate, action soundness, or arbitrary replacement f/F is assumed.

The exact source/JR identification reconnects lowerBar to the actual Suzuki
lowerAmplitude already used in the original U5 coefficient dictionary.
The final identities isolate, rather than discharge, the mean-transport step.
-/

namespace ImbalancedChen.P5CanonicalLowerCancellation

noncomputable section

open Set MeasureTheory
open scoped Interval
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open Part5UpperTables
open Part5UpperTables.Renewal

def upperA (s : ℝ) : ℝ := s * jr1965F s / jr1965DelayConstant
def lowerBar (s : ℝ) : ℝ := s * jr1965f s / jr1965DelayConstant
def upperKernel (w : ℝ) : ℝ := upperA w / w

theorem delayConstant_pos : 0 < jr1965DelayConstant := by
  unfold jr1965DelayConstant
  positivity

theorem upperKernel_eq_actual {w : ℝ} (hw : 0 < w) :
    upperKernel w = jr1965F w / jr1965DelayConstant := by
  unfold upperKernel upperA
  field_simp [hw.ne', delayConstant_pos.ne'] <;> ring

theorem lowerBar_eq_originalLowerAmplitude {s : ℝ} (hs : 2 ≤ s) :
    lowerBar s = Part5OriginalUpsilon5CausalDictionary.lowerAmplitude s := by
  unfold lowerBar Part5OriginalUpsilon5CausalDictionary.lowerAmplitude
  rw [continuousLowerFactor_eq_jr1965f hs]
  rfl

theorem upperA_eq_actualSuzukiAmplitude {s : ℝ} (hs : 2 ≤ s) :
    upperA s = s * suzukiContinuousUpperFactor s /
      (2 * Real.exp Real.eulerMascheroniConstant) := by
  have h := (LiLiuPrereqWF.CoarseDensity.sourceParity_eq_jr1965 hs).1
  unfold upperA suzukiContinuousUpperFactor jr1965DelayConstant
  rw [h]
  ring

theorem continuousOn_upperKernel : ContinuousOn upperKernel (Ioi 0) := by
  unfold upperKernel upperA
  exact ((continuousOn_id.mul continuousOn_jr1965F).div_const _).div
    continuousOn_id (fun w hw => ne_of_gt hw)

theorem upperKernel_intervalIntegrable {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    IntervalIntegrable upperKernel volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_upperKernel.mono
  intro w hw
  have hlo : 1 ≤ min a b := le_min ha hb
  exact lt_of_lt_of_le zero_lt_one (hlo.trans hw.1)

@[simp] theorem lowerBar_two : lowerBar 2 = 0 := by
  unfold lowerBar
  rw [jr1965f_initial (by norm_num : (2 : ℝ) ≤ 2)]
  ring

/-- The exact delayed lower increment, including x=2. -/
theorem lowerBar_increment {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    lowerBar y - lowerBar x = ∫ w in (x - 1)..(y - 1), upperKernel w := by
  have h := jr1965f_integral_recurrence hx hxy
  calc
    lowerBar y - lowerBar x =
        (y * jr1965f y - x * jr1965f x) / jr1965DelayConstant := by
      unfold lowerBar
      ring
    _ = (∫ t in x..y, jr1965F (t - 1)) / jr1965DelayConstant := by
      rw [h]
      ring
    _ = ∫ t in x..y, jr1965F (t - 1) / jr1965DelayConstant := by
      rw [intervalIntegral.integral_div]
    _ = ∫ w in (x - 1)..(y - 1), jr1965F w / jr1965DelayConstant :=
      intervalIntegral.integral_comp_sub_right _ 1
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [uIcc_of_le (by linarith : x - 1 ≤ y - 1)] at hw
      exact (upperKernel_eq_actual (by linarith [hw.1])).symm

/-- Original abar(s), with the correct lower endpoint one and NO extra constant. -/
theorem lowerBar_integral {s : ℝ} (hs : 2 ≤ s) :
    lowerBar s = ∫ w in (1 : ℝ)..(s - 1), upperA w / w := by
  have h := lowerBar_increment (x := 2) (by norm_num) hs
  simpa only [lowerBar_two, sub_zero, show (2 : ℝ) - 1 = 1 by norm_num,
    upperKernel] using h

theorem lowerBar_integral_Ico {s : ℝ} (hs : 2 ≤ s) :
    lowerBar s = ∫ w in Ico (1 : ℝ) (s - 1), upperA w / w := by
  rw [lowerBar_integral hs, intervalIntegral.integral_of_le (by linarith),
    integral_Ico_eq_integral_Ioc]

/-- Direct statement for the actual original coefficient dictionary object. -/
theorem originalLowerAmplitude_integral {s : ℝ} (hs : 2 ≤ s) :
    Part5OriginalUpsilon5CausalDictionary.lowerAmplitude s =
      ∫ w in (1 : ℝ)..(s - 1), upperA w / w := by
  rw [← lowerBar_eq_originalLowerAmplitude hs]
  exact lowerBar_integral hs

/-- Source derivative: no derivative contract is an input. -/
theorem lowerBar_hasDerivAt {s : ℝ} (hs : 2 < s) :
    HasDerivAt lowerBar (upperA (s - 1) / (s - 1)) s := by
  have h := (hasDerivAt_mul_jr1965f hs).div_const jr1965DelayConstant
  have heq : jr1965F (s - 1) / jr1965DelayConstant =
      upperA (s - 1) / (s - 1) :=
    (upperKernel_eq_actual (by linarith)).symm
  rw [heq] at h
  exact h

/-- The original h<-H transition stops at w=5, so its source anchor is s=6. -/
theorem lowerBar_six_sub {s : ℝ} (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    lowerBar 6 - lowerBar s = ∫ w in (s - 1)..5, upperA w / w := by
  simpa only [show (6 : ℝ) - 1 = 5 by norm_num, upperKernel] using
    lowerBar_increment hs hs6

/-- Exact cancellation for every original upper table, not an action-soundness premise. -/
theorem lowerTransition_base_cancellation (nums : Fin 200 → ℤ)
    {s : ℝ} (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    lowerBar s + lowerTransition nums s = lowerBar 6 -
      ∫ w in (s - 1)..5, (upperA w - upperFloor nums w) / w := by
  have hA := upperKernel_intervalIntegrable (a := s - 1) (b := 5)
    (by linarith) (by norm_num)
  have hH := intervalIntegrable_upperFloor_div nums (s - 1) 5
  have hsplit :
      (∫ w in (s - 1)..5, (upperA w - upperFloor nums w) / w) =
        (∫ w in (s - 1)..5, upperA w / w) -
        ∫ w in (s - 1)..5, upperFloor nums w / w := by
    simp_rw [sub_div]
    exact intervalIntegral.integral_sub hA hH
  rw [hsplit, lowerTransition_eq_interval nums hs]
  linarith only [lowerBar_six_sub hs hs6]

theorem adoptedhnew_base_cancellation {s : ℝ} (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    lowerBar s + adoptedhnew s = lowerBar 6 -
      ∫ w in (s - 1)..5, (upperA w - H248 w) / w := by
  exact lowerTransition_base_cancellation H248Numerators hs hs6

theorem originalLowerAmplitude_adoptedhnew_cancellation
    {s : ℝ} (hs : 2 ≤ s) (hs6 : s ≤ 6) :
    Part5OriginalUpsilon5CausalDictionary.lowerAmplitude s + adoptedhnew s =
      Part5OriginalUpsilon5CausalDictionary.lowerAmplitude 6 -
        ∫ w in (s - 1)..5, (upperA w - H248 w) / w := by
  rw [← lowerBar_eq_originalLowerAmplitude hs,
    ← lowerBar_eq_originalLowerAmplitude (by norm_num : (2 : ℝ) ≤ 6)]
  exact adoptedhnew_base_cancellation hs hs6

/-- The same cancellation at the genuine enhanced U5 residual and query.
The actual dictionary already proves that this query lies in [2,5]. -/
theorem originalU5_adoptedhnew_kernel_cancellation
    {x : Fin 2 → ℝ} (hx : x ∈ Part5OriginalUpsilon5CausalDictionary.triangle) :
    Part5OriginalUpsilon5CausalDictionary.kernel adoptedhnew x =
      4 * Part5OriginalUpsilon5CausalDictionary.lowerAmplitude 6 /
          Part5OriginalUpsilon5CausalDictionary.residual x -
        (4 / Part5OriginalUpsilon5CausalDictionary.residual x) *
          ∫ w in (Part5OriginalUpsilon5CausalDictionary.argument x - 1)..5,
            (upperA w - H248 w) / w := by
  have hs := Part5OriginalUpsilon5CausalDictionary.argument_mem hx
  unfold Part5OriginalUpsilon5CausalDictionary.kernel
  rw [originalLowerAmplitude_adoptedhnew_cancellation hs.1
    (hs.2.trans (by norm_num : (5 : ℝ) ≤ 6))]
  ring

/-- The finite-table increment itself is exact and has the positive H orientation. -/
theorem adoptedhnew_increment {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    adoptedhnew x - adoptedhnew y = ∫ w in (x - 1)..(y - 1), H248 w / w := by
  rw [adoptedhnew_interval hx, adoptedhnew_interval (hx.trans hxy)]
  have h := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_upperFloor_div H248Numerators (x - 1) (y - 1))
    (intervalIntegrable_upperFloor_div H248Numerators (y - 1) 5)
  change (∫ w in (x - 1)..(y - 1), H248 w / w) +
      (∫ w in (y - 1)..5, H248 w / w) =
      ∫ w in (x - 1)..5, H248 w / w at h
  linarith only [h]

end
end ImbalancedChen.P5CanonicalLowerCancellation
