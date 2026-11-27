import ImbalancedChen.ActualExtendedThirdLowerFactorRegularity
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiProposition118SourceIntegralDDE

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Actual coupled numerator recurrences, with the integrability and order facts
supplied from the genuine JR/Suzuki source, followed by a one-step enclosure
from previous endpoint enclosures. This is not a new synthetic DDE model.
The lower factor is definitionally the actual normalized lower factor on
[2,infinity). No desired next-node enclosure, DDE, curvature assertion, or
final integral bound is an input. The endpoint step is a rectangle bound:
it does NOT certify the original, sharper 112-bit chord updates.
Original n=16384, 112-bit table, 2^48 conversion, K, C, rho, h and reserves
are unchanged. The missing sharp chord and rational weight suppliers remain
explicitly OPEN; this file must not be reported as full [2,12] query closure.
-/

namespace ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly

noncomputable section
open Set MeasureTheory
open MathlibNt.SieveTheory
open MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

/-- Exactly the amplitude in the actual normalized lower factor. -/
def A : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

def lower (s : ℝ) : ℝ := thirdTailLowerFactor s
def upper (s : ℝ) : ℝ := suzukiContinuousUpperFactor s / A
def L (s : ℝ) : ℝ := s * lower s
def H (s : ℝ) : ℝ := s * upper s

theorem A_pos : 0 < A := by unfold A; positivity

theorem lower_eq_actual {s : ℝ} (hs : 2 ≤ s) :
    lower s = actualExtendedThirdLowerFactor s := by
  exact (actualExtendedThirdLowerFactor_of_two_le hs).symm

theorem lower_source (s : ℝ) :
    lower s = (1 - suzukiProposition118SourceTMinus s) / A := by
  rfl

theorem upper_source (s : ℝ) :
    upper s = (1 + suzukiProposition118SourceTPlus s) / A := by
  rfl

/-- Antitonicity is supplied by the actual convergent odd layer series. -/
theorem source_plus_antitone :
    AntitoneOn suzukiProposition118SourceTPlus (Ici 2) := by
  intro x hx y hy hxy
  apply Summable.tsum_le_tsum _
    (summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract (by change 2 ≤ y at hy; linarith))
    (summable_suzukiProposition118SourceTPlus_of_sourceContract
      jr1965Section13HatSourceContract (by change 2 ≤ x at hx; linarith))
  intro k
  exact suzukiLayer_one_antitoneOn_parityDomain (by norm_num) (2 * k + 1)
    (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain];
        change 2 ≤ x at hx; linarith)
    (by simp [suzukiParityDomainOne, KappaOneModel.parityDomain];
        change 2 ≤ y at hy; linarith) hxy

theorem source_minus_antitone :
    AntitoneOn suzukiProposition118SourceTMinus (Ici 2) := by
  intro x hx y hy hxy
  have h := thirdTail_lowerFactor_monotone hx hy hxy
  change 1 - suzukiProposition118SourceTMinus x ≤
    1 - suzukiProposition118SourceTMinus y at h
  linarith

theorem lower_monotone : MonotoneOn lower (Ici 2) := by
  intro x hx y hy hxy
  exact div_le_div_of_nonneg_right
    (thirdTail_lowerFactor_monotone hx hy hxy) A_pos.le

theorem upper_antitone : AntitoneOn upper (Ici 2) := by
  intro x hx y hy hxy
  simpa only [upper, suzukiContinuousUpperFactor, add_comm] using
    (div_le_div_of_nonneg_right
      (add_le_add_left (source_plus_antitone hx hy hxy) 1) A_pos.le)

private theorem shifted_source_integrable {x y : ℝ}
    (hx : 3 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => suzukiProposition118SourceTPlus (t-1)) volume x y ∧
    IntervalIntegrable (fun t => suzukiProposition118SourceTMinus (t-1)) volume x y := by
  have hshift (f : ℝ → ℝ) (hf : AntitoneOn f (Ici 2)) :
      AntitoneOn (fun t => f (t-1)) (uIcc x y) := by
    rw [uIcc_of_le hxy]
    intro u hu v hv huv
    apply hf
    · change 2 ≤ u - 1
      linarith [hu.1]
    · change 2 ≤ v - 1
      linarith [hv.1]
    · linarith
  exact ⟨(hshift _ source_plus_antitone).intervalIntegrable,
    (hshift _ source_minus_antitone).intervalIntegrable⟩

theorem shifted_factors_integrable {x y : ℝ}
    (hx : 3 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (fun t => upper (t-1)) volume x y ∧
    IntervalIntegrable (fun t => lower (t-1)) volume x y := by
  obtain ⟨hp, hm⟩ := shifted_source_integrable hx hxy
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume x y :=
    continuousOn_const.intervalIntegrable
  exact ⟨(hc.add hp).div_const A, (hc.sub hm).div_const A⟩

/-- Separate coupled equation for the genuine lower numerator. -/
theorem L_sub {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    L y - L x = ∫ t in x..y, upper (t-1) := by
  have hs := suzukiProposition118SourceTMinus_weighted_sub
    jr1965Section13HatSourceContract (by linarith : 2 ≤ x) hxy
  have hp := (shifted_source_integrable hx hxy).1
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume x y :=
    continuousOn_const.intervalIntegrable
  have hn : y * (1 - suzukiProposition118SourceTMinus y) -
      x * (1 - suzukiProposition118SourceTMinus x) =
      (y-x) + ∫ t in x..y, suzukiProposition118SourceTPlus (t-1) := by
    linarith only [hs]
  simp only [L, lower_source, upper_source]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add hc hp,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  calc
    _ = (y * (1 - suzukiProposition118SourceTMinus y) -
        x * (1 - suzukiProposition118SourceTMinus x)) / A := by ring
    _ = _ := by rw [hn]

/-- Separate coupled equation for the genuine upper numerator. -/
theorem H_sub {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    H y - H x = ∫ t in x..y, lower (t-1) := by
  have hs := suzukiProposition118SourceTPlus_weighted_sub
    jr1965Section13HatSourceContract hx hxy
  have hm := (shifted_source_integrable hx hxy).2
  have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume x y :=
    continuousOn_const.intervalIntegrable
  have hn : y * (1 + suzukiProposition118SourceTPlus y) -
      x * (1 + suzukiProposition118SourceTPlus x) =
      (y-x) - ∫ t in x..y, suzukiProposition118SourceTMinus (t-1) := by
    linarith only [hs]
  simp only [H, upper_source, lower_source]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub hc hm,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, mul_one]
  calc
    _ = (y * (1 + suzukiProposition118SourceTPlus y) -
        x * (1 + suzukiProposition118SourceTPlus x)) / A := by ring
    _ = _ := by rw [hn]

/-- The source gap equation is recovered with its NEGATIVE delay sign. -/
theorem gap_sub {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    (H y - L y) - (H x - L x) =
      -(∫ t in x..y, upper (t-1) - lower (t-1)) := by
  obtain ⟨hu, hl⟩ := shifted_factors_integrable hx hxy
  rw [intervalIntegral.integral_sub hu hl]
  linarith only [L_sub hx hxy, H_sub hx hxy]

/-- Unconditional rectangle bounds, simultaneously for both actual increments.
These preserve the coupling and expose exactly which delayed endpoints suffice. -/
theorem coupled_increment_bounds {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    (y-x) * upper (y-1) ≤ L y - L x ∧
    L y - L x ≤ (y-x) * upper (x-1) ∧
    (y-x) * lower (x-1) ≤ H y - H x ∧
    H y - H x ≤ (y-x) * lower (y-1) := by
  obtain ⟨hu, hl⟩ := shifted_factors_integrable hx hxy
  have hc (c : ℝ) : IntervalIntegrable (fun _ : ℝ => c) volume x y :=
    continuousOn_const.intervalIntegrable
  have hx2 : x-1 ∈ Ici (2 : ℝ) := by change 2 ≤ x-1; linarith
  have hy2 : y-1 ∈ Ici (2 : ℝ) := by change 2 ≤ y-1; linarith
  have ht2 (t : ℝ) (ht : t ∈ Icc x y) : t-1 ∈ Ici (2 : ℝ) := by
    change 2 ≤ t-1
    linarith [ht.1]
  have hLL := intervalIntegral.integral_mono_on hxy (hc (upper (y-1))) hu
    (fun t ht => upper_antitone (ht2 t ht) hy2 (by linarith [ht.2]))
  have hLU := intervalIntegral.integral_mono_on hxy hu (hc (upper (x-1)))
    (fun t ht => upper_antitone hx2 (ht2 t ht) (by linarith [ht.1]))
  have hHL := intervalIntegral.integral_mono_on hxy (hc (lower (x-1))) hl
    (fun t ht => lower_monotone hx2 (ht2 t ht) (by linarith [ht.1]))
  have hHU := intervalIntegral.integral_mono_on hxy hl (hc (lower (y-1)))
    (fun t ht => lower_monotone (ht2 t ht) hy2 (by linarith [ht.2]))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hLL hLU hHL hHU
  rw [L_sub hx hxy, H_sub hx hxy]
  exact ⟨hLL, hLU, hHL, hHU⟩

/-- A usable forward step from current-node and delayed endpoint bounds.
The premises concern x, x-1 and y-1 only; no premise concerns L y or H y.
In the original grid step y=x+1/16384 all delayed points precede x. -/
theorem coupled_node_step {x y llo lhi hlo hhi ulo uhi flo fhi : ℝ}
    (hx : 3 ≤ x) (hxy : x ≤ y)
    (hL : llo ≤ L x ∧ L x ≤ lhi) (hH : hlo ≤ H x ∧ H x ≤ hhi)
    (hUlo : ulo ≤ upper (y-1)) (hUhi : upper (x-1) ≤ uhi)
    (hFlo : flo ≤ lower (x-1)) (hFhi : lower (y-1) ≤ fhi) :
    (llo + (y-x)*ulo ≤ L y ∧ L y ≤ lhi + (y-x)*uhi) ∧
    (hlo + (y-x)*flo ≤ H y ∧ H y ≤ hhi + (y-x)*fhi) := by
  obtain ⟨hLL, hLU, hHL, hHU⟩ := coupled_increment_bounds hx hxy
  have hd : 0 ≤ y-x := sub_nonneg.mpr hxy
  have a := mul_le_mul_of_nonneg_left hUlo hd
  have b := mul_le_mul_of_nonneg_left hUhi hd
  have c := mul_le_mul_of_nonneg_left hFlo hd
  have d := mul_le_mul_of_nonneg_left hFhi hd
  constructor <;> constructor <;> linarith only [hL.1, hL.2, hH.1, hH.2,
    hLL, hLU, hHL, hHU, a, b, c, d]


/-- Exact delayed-coordinate form used by weights(j) in the original table. -/
theorem L_sub_delayed {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    L y - L x = ∫ u in (x-1)..(y-1), H u / u := by
  rw [L_sub hx hxy, intervalIntegral.integral_comp_sub_right]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith : x-1 ≤ y-1)] at hu
  have hu0 : u ≠ 0 := by linarith [hu.1]
  simp [H, hu0]

theorem H_sub_delayed {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    H y - H x = ∫ u in (x-1)..(y-1), L u / u := by
  rw [H_sub hx hxy, intervalIntegral.integral_comp_sub_right]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (by linarith : x-1 ≤ y-1)] at hu
  have hu0 : u ≠ 0 := by linarith [hu.1]
  simp [L, hu0]

/-- The literal original n=16384 coupled cell recurrence. The first admitted
index is 3*n+1. In particular this covers every lower chord update i>4*n
and every nonconstant upper update i>3*n through the original endpoint 12*n.
It does not assert a rounded chord enclosure. -/
theorem original_grid_cell_recurrence (i : ℕ) (hi : 49153 ≤ i) :
    (L ((i : ℝ)/16384) - L (((i : ℝ)-1)/16384) =
      ∫ u in (((i : ℝ)-16384-1)/16384)..(((i : ℝ)-16384)/16384), H u / u) ∧
    (H ((i : ℝ)/16384) - H (((i : ℝ)-1)/16384) =
      ∫ u in (((i : ℝ)-16384-1)/16384)..(((i : ℝ)-16384)/16384), L u / u) := by
  have hiR : (49153 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
  have hx : (3 : ℝ) ≤ ((i : ℝ)-1)/16384 := by linarith
  have hxy : ((i : ℝ)-1)/16384 ≤ (i : ℝ)/16384 := by linarith
  have ha : ((i : ℝ)-1)/16384 - 1 = ((i : ℝ)-16384-1)/16384 := by ring
  have hb : (i : ℝ)/16384 - 1 = ((i : ℝ)-16384)/16384 := by ring
  constructor
  · simpa only [ha, hb] using (L_sub_delayed hx hxy)
  · simpa only [ha, hb] using (H_sub_delayed hx hxy)

end
end ImbalancedChen.OriginalU2CoupledRecurrenceSourceOnly
