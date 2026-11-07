import ImbalancedChen.P5UnroughMobiusSharp
import ImbalancedChen.Part3RoughAPTwistAverage
import ImbalancedChen.P5ActualRoughMobiusSmallSW

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing supplier of O's ClassicalUnroughMobiusSW. This theorem has no
SW hypothesis. It consumes actual zero-cutoff character cancellation,
keeps the exact coprime mean through finite orthogonality, and transports
the original real scales and modulus range. Principal characters cancel
exactly; no principal Mobius asymptotic is required.

The contour input is the existing generic physical Perron budget, whose
source chain uses the pinned primitive Siegel L(1) lower bound and actual
induction to the original character. All inherited source-only dependencies
remain held. This file is not a claim of elaboration or kernel closure.
-/
namespace ImbalancedChen.P5Z.UnroughMobiusSWSupplier
noncomputable section
open Classical Finset
open scoped BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.Part3.UnroughMobiusSharp20261102
open ImbalancedChen.Part3.RoughAPPrincipalCancellation20261027
open ImbalancedChen.Part3.RoughAPTwistAverage20261027
open ImbalancedChen.Part3.PrimeMellinProfileVariation20261026b
open ActualRoughMobiusInner ActualRoughMobiusSmallSW

theorem roughOneSlot_zero (n : ℕ) : roughOneSlot 0 n = 1 := by
  have hp : ∀ p : ℕ, p.Prime → p ∣ n → (0 : ℝ) < (p : ℝ) := by
    intro p hp _
    exact_mod_cast hp.pos
  simp only [roughOneSlot,if_pos hp]

/-- Literal coefficient dictionary, including n=0. -/
theorem zero_cutoff_base_eq_mu :
    actualBaseCoefficient true 0 0 1 (fun _ => 1) = muCoefficient := by
  funext n
  by_cases hn : n = 0
  · simp [actualBaseCoefficient,hn,muCoefficient]
  · simp [actualBaseCoefficient,hn,roughCoefficient,roughMoebiusSlot,
      roughOneSlot_zero,phase,muCoefficient]

/-- K log(W)^B is inside log(2W)^(B+1) once log(W)>=K.
The extra exponent is fixed before the modulus and interval vary. -/
theorem modulus_log_transport {W B K : ℝ} (hW : 1 < W)
    (hB : 0 ≤ B) (hK : K ≤ Real.log W) :
    K*(Real.log W)^B ≤ (Real.log (2*W))^(B+1) := by
  have hWp : 0 < W := zero_lt_one.trans hW
  have hL : 0 < Real.log W := Real.log_pos hW
  have hLL : Real.log W ≤ Real.log (2*W) :=
    Real.log_le_log hWp (by linarith)
  have hL2 : 0 < Real.log (2*W) := hL.trans_le hLL
  calc
    _ ≤ Real.log (2*W)*(Real.log (2*W))^B :=
      mul_le_mul (hK.trans hLL) (Real.rpow_le_rpow hL.le hLL hB)
        (Real.rpow_nonneg hL.le _) hL2.le
    _ = _ := by rw [Real.rpow_add hL2,Real.rpow_one]; ring

/-- Actual unconditional source candidate for the exact O interface.
C and X precede every W,a,b,q,r. No upper bound on W or absolute q occurs.
The allowed logarithmic modulus constant K is paid by the threshold only. -/
theorem classicalUnroughMobiusSW : ClassicalUnroughMobiusSW := by
  intro A B K hA hB hK
  obtain ⟨C,hC,x0,hx0,hinterval⟩ :=
    exists_unrough_interval_character_SW A (B+1) 0 (1/2)
      hA (by linarith) (by norm_num) (by norm_num)
  refine ⟨4*C,max 2 (max x0 (Real.exp K)),by positivity,le_max_left _ _,?_⟩
  intro W a b hW ha hab hb q r hq hqlog hr
  have hW2 : 2 ≤ W := (le_max_left _ _).trans hW
  have hW1 : 1 < W := lt_of_lt_of_le (by norm_num) hW2
  have hWp : 0 < W := zero_lt_one.trans hW1
  have hL : 0 < Real.log W := Real.log_pos hW1
  have h2Wp : 0 < 2*W := by positivity
  have hLL : Real.log W ≤ Real.log (2*W) :=
    Real.log_le_log hWp (by linarith)
  have hL2 : 0 < Real.log (2*W) := hL.trans_le hLL
  have hxW : x0 ≤ W :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hW)
  have heW : Real.exp K ≤ W :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hW)
  have hKlog : K ≤ Real.log W := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos K) heW
  have hmod : (q : ℝ) ≤ (Real.log (2*W))^(B+1) :=
    hqlog.trans (modulus_log_transport hW1 hB hKlog)
  have hscale : (2*W)^(1/2 : ℝ) ≤ W := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.sqrt_le_iff).mpr ⟨hWp.le,by nlinarith⟩
  have ha0 : 0 < a := hWp.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  letI : NeZero q := ⟨hq.ne'⟩
  have hbound : ‖unroughError a b q r‖ ≤
      C*(a+b)*(Real.log (2*W))^(-A) := by
    apply auxiliarySWError_norm_le_of_twist_le (interval a b) muCoefficient 1
      hq hr (by positivity)
    intro χ hχ
    rw [← zero_cutoff_base_eq_mu,actual_twist_eq_finite]
    simp only [mul_one]
    exact hinterval (2*W) (hxW.trans (by linarith)) q hmod χ hχ
      true 0 1 a b (by simp) (by norm_num) (hscale.trans ha) hab hb
  have hden : (Real.log W)^A ≤ (Real.log (2*W))^A :=
    Real.rpow_le_rpow hL.le hLL hA
  calc
    _ ≤ C*(a+b)*(Real.log (2*W))^(-A) := hbound
    _ = C*(a+b)/(Real.log (2*W))^A := by
      rw [Real.rpow_neg hL2.le]; rfl
    _ ≤ C*(a+b)/(Real.log W)^A :=
      div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hL A) hden
    _ ≤ C*(4*W)/(Real.log W)^A :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : a+b ≤ 4*W) hC.le)
        (Real.rpow_nonneg hL.le A)
    _ = _ := by ring

end
end ImbalancedChen.P5Z.UnroughMobiusSWSupplier
