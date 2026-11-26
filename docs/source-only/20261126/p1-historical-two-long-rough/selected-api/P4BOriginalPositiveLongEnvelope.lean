import ImbalancedChen.P4BOriginalBrunCoprimeE1
import ImbalancedChen.Part3TwoLongQuantitativeTransitionProfiles

/-! SOURCE ONLY / UNCOMPILED. A genuine nonnegative smooth majorant.
abs(profile) is never declared smooth. The original unit Mellin phase
is used only through its proved norm-one identity. Both actual smooth
transition labels, including the two endpoint bumps, are covered. -/
namespace ImbalancedChen.P4BOriginalPositiveLongEnvelope
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap
open Part3.TwoLongLiteralMellinModes (N2)
open Part3.TwoLongN2FourierDecay (secondSchwartz fourierDecayConstant fourierDecayConstant_pos)
open Part3.TwoLongActualDoublePeriodization
open Part3.TwoLongQuantitativeTransitionProfiles
open Part3.TwoLongTransitionMellinN2
open Part3.PrimeMellinProfileVariation20261026b (phase_norm)
open P4BOriginalCoprimeSmoothE1 (mass price)

def envelope (delta U x : ℝ) : ℝ := logSize U*(upper delta x+gap delta x)

theorem envelope_nonneg (delta U x : ℝ) : 0≤envelope delta U x :=
  mul_nonneg (zero_le_one.trans (logSize_one_le U))
    (add_nonneg (doubleStep_range delta 1 2 x).1 (gap_nonneg delta x))

theorem envelope_smooth (delta U : ℝ) : ContDiff ℝ ∞ (envelope delta U) :=
  contDiff_const.mul ((upper_smooth delta).add (gap_smooth delta))

theorem envelope_support {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    Function.support (envelope delta U)⊆Icc (1/2:ℝ) (5/2) := by
  intro x hx
  have hsum : upper delta x+gap delta x≠0 := fun h => hx (by simp [envelope,h])
  by_cases hu : upper delta x=0
  · exact gap_support hd hs (by simpa [hu] using hsum)
  · exact upper_support hd hs hu

def envelopeSchwartz {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) : 𝓢(ℝ,ℂ) :=
  logSize U • (actualUpperSchwartz hd hs+actualGapSchwartz hd hs)

theorem envelopeSchwartz_apply {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U x : ℝ) :
    envelopeSchwartz hd hs U x=(envelope delta U x:ℂ) := by
  simp [envelopeSchwartz,envelope,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_add]

theorem envelopeSchwartz_coe {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    (envelopeSchwartz hd hs U : ℝ→ℂ)=fun x => (envelope delta U x:ℂ) := by
  funext x
  exact envelopeSchwartz_apply hd hs U x

theorem profile_majorant (isGap isLog : Bool) {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4)
    (U t x : ℝ) : ‖profile isGap isLog delta U t x‖≤envelope delta U x := by
  by_cases hx : x∈window
  · have hlog := (logFactor_bounds isLog U hx).1
    have htrans0 : 0≤transition isGap delta x := by
      cases isGap
      · exact (doubleStep_range delta 1 2 x).1
      · exact gap_nonneg delta x
    have htrans : transition isGap delta x≤upper delta x+gap delta x := by
      cases isGap <;> dsimp [transition]
      · linarith [gap_nonneg delta x]
      · linarith [(doubleStep_range delta 1 2 x).1]
    simp only [profile,twisted,amplitude,norm_mul,phase_norm,mul_one,Complex.norm_real,
      Real.norm_eq_abs,abs_mul,abs_of_nonneg htrans0]
    exact (mul_le_mul htrans hlog (abs_nonneg _) (add_nonneg
      (doubleStep_range delta 1 2 x).1 (gap_nonneg delta x))).trans_eq (by unfold envelope; ring)
  · have hz : profile isGap isLog delta U t x=0 := by
      by_contra hn
      exact hx (profile_support isGap isLog hd hs U t hn)
    rw [hz,norm_zero]
    exact envelope_nonneg delta U x

private def l1 (F : 𝓢(ℝ,ℂ)) : ℝ := ∫ x : ℝ,‖F x‖

private theorem l1_add_le (F G : 𝓢(ℝ,ℂ)) : l1 (F+G)≤l1 F+l1 G := by
  have H := integral_mono (F+G).integrable.norm (F.integrable.norm.add G.integrable.norm)
    (fun x => norm_add_le (F x) (G x))
  simpa only [integral_add F.integrable.norm G.integrable.norm,l1] using H

private theorem l1_smul (c : ℝ) (hc : 0≤c) (F : 𝓢(ℝ,ℂ)) : l1 (c • F)=c*l1 F := by
  simp [l1,norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,integral_const_mul]

theorem N2_smul_add (c : ℝ) (hc : 0≤c) (F G : 𝓢(ℝ,ℂ)) :
    N2 (c • (F+G) : 𝓢(ℝ,ℂ))≤c*(N2 (F:ℝ→ℂ)+N2 (G:ℝ→ℂ)) := by
  have h2 : secondSchwartz (c • (F+G))=c • (secondSchwartz F+secondSchwartz G) := by
    simp only [secondSchwartz,map_add,map_smul]
  change l1 (c • (F+G))+l1 (secondSchwartz (c • (F+G)))≤
    c*((l1 F+l1 (secondSchwartz F))+(l1 G+l1 (secondSchwartz G)))
  rw [h2,l1_smul c hc,l1_smul c hc]
  have H0 := mul_le_mul_of_nonneg_left (l1_add_le F G) hc
  have H2 := mul_le_mul_of_nonneg_left (l1_add_le (secondSchwartz F) (secondSchwartz G)) hc
  linarith

def envelopeCost : ℝ := upperCost+gapCost

theorem envelopeCost_nonneg : 0≤envelopeCost := by
  have H := D_nonneg
  unfold envelopeCost upperCost gapCost
  positivity

theorem envelope_N2 {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    N2 (envelopeSchwartz hd hs U : ℝ→ℂ)≤envelopeCost*logSize U/delta^2 := by
  have hc := zero_le_one.trans (logSize_one_le U)
  have H := N2_smul_add (logSize U) hc (actualUpperSchwartz hd hs) (actualGapSchwartz hd hs)
  exact H.trans ((mul_le_mul_of_nonneg_left (add_le_add (upper_N2 hd hs) (gap_N2 hd hs)) hc).trans_eq
    (by unfold envelopeCost; ring))

theorem envelope_mass {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    ‖mass (envelopeSchwartz hd hs U)‖≤6*logSize U := by
  have hc := zero_le_one.trans (logSize_one_le U)
  have hbound (x : ℝ) : ‖envelopeSchwartz hd hs U x‖≤3*logSize U := by
    rw [envelopeSchwartz_apply,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (envelope_nonneg _ _ _)]
    have hu := (abs_le.mp (upper_abs_le_one delta x)).2
    have hg := (abs_le.mp (gap_abs_le_two delta x)).2
    unfold envelope
    nlinarith
  have hsupp : Function.support (envelopeSchwartz hd hs U : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2) := by
    intro x hx
    apply envelope_support hd hs U
    simpa only [envelopeSchwartz_apply,Complex.ofReal_eq_zero] using hx
  exact (norm_integral_le_integral_norm _).trans
    ((norm_integral_le_two (envelopeSchwartz hd hs U).integrable hsupp (3*logSize U)
      (fun x _ => hbound x)).trans_eq (by ring))

def meanConstant : ℝ := 6+2*fourierDecayConstant*envelopeCost
def meanPrice (delta U : ℝ) : ℝ := meanConstant*logSize U/delta^2

theorem meanPrice_nonneg (delta U : ℝ) : 0≤meanPrice delta U := by
  have h1 := fourierDecayConstant_pos.le
  have h2 := envelopeCost_nonneg
  have h3 := zero_le_one.trans (logSize_one_le U)
  unfold meanPrice meanConstant
  positivity

theorem envelope_prices {delta : ℝ} (hd : 0<delta) (hs : delta≤1/4) (U : ℝ) :
    ‖mass (envelopeSchwartz hd hs U)‖≤meanPrice delta U ∧
      price (envelopeSchwartz hd hs U)≤meanPrice delta U := by
  have hc := zero_le_one.trans (logSize_one_le U)
  have hD := pow_pos hd 2
  have hsmall : delta^2≤1 := by
    have H := mul_nonneg (sub_nonneg.mpr (show delta≤1 by linarith)) (show 0≤1+delta by linarith)
    nlinarith
  have hC : 6≤meanConstant := by
    have H := mul_nonneg fourierDecayConstant_pos.le envelopeCost_nonneg
    unfold meanConstant
    linarith
  constructor
  · apply (envelope_mass hd hs U).trans
    unfold meanPrice
    apply (le_div_iff₀ hD).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsmall (mul_nonneg (by norm_num : (0:ℝ)≤6) hc),
      mul_le_mul_of_nonneg_right hC hc]
  · calc
      price (envelopeSchwartz hd hs U)≤2*fourierDecayConstant*(envelopeCost*logSize U/delta^2) :=
        mul_le_mul_of_nonneg_left (envelope_N2 hd hs U)
          (mul_nonneg (by norm_num) fourierDecayConstant_pos.le)
      _=(2*fourierDecayConstant*envelopeCost)*logSize U/delta^2 := by ring
      _≤meanPrice delta U := by
        unfold meanPrice meanConstant
        exact div_le_div_of_nonneg_right (by nlinarith) hD.le

end
end ImbalancedChen.P4BOriginalPositiveLongEnvelope
