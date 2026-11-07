import ImbalancedChen.Part3OriginalS2NativeKeyTail
import Mathlib.Tactic

/-! Arbitrary logarithmic payment on the genuine primitive smooth-q
support. Constants precede all atoms, keys and residues. The original
physical range-(7) cap is explicit. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalS2NativeKeyTailPayment

open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2FullMixedTailPayment
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3OriginalS2NativePsiGeometry
open ImbalancedChen.Part3OriginalS2NativeKeyTail
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

def nativeFinalConstant
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ)) : ℝ :=
  46080 * hShiu.A * uniformEulerConstant 1

theorem nativeFinalConstant_pos
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ)) :
    0 < nativeFinalConstant hShiu := by
  unfold nativeFinalConstant
  exact mul_pos (mul_pos (by norm_num) hShiu.A_pos) (uniformEulerConstant_pos 1)

theorem nativeLogFactor_le_six_logs
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlog : 1 ≤ Real.log d.scale)
    (hphysical : nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    nativeLogFactor hShiu d ≤ nativeFinalConstant hShiu * Real.log d.scale ^ 6 := by
  have hx1 : 1 ≤ d.scale := by linarith
  have hxpos : 0 < d.scale := by linarith
  have hP : (nativePhysicalCap d : ℝ) ≤ d.scale := by
    calc
      _ ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) := by exact_mod_cast hphysical
      _ ≤ d.scale ^ ((4 : ℝ) / 5) := Nat.floor_le (Real.rpow_nonneg hxpos.le _)
      _ ≤ d.scale := Real.rpow_le_self_of_one_le hx1 (by norm_num)
  have hcap : physicalCap d ≤ nativePhysicalCap d := by
    apply Nat.floor_mono
    have hQ1 : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    have hQ2 : 0 ≤ d.Q2 := by linarith [hd.2.2.2.1]
    have hQ3 : 0 ≤ d.Q3 := by linarith [hd.2.2.2.2.1]
    nlinarith [mul_nonneg (mul_nonneg hQ1 hQ2) hQ3]
  have hR := (roughCap_le_physicalCap hd).trans
    ((show (physicalCap d : ℝ) ≤ nativePhysicalCap d by exact_mod_cast hcap).trans hP)
  have hR1 := one_le_roughCap hd
  have hphi : logBudget (nativePhysicalCap d) ≤ 2 * Real.log d.scale := by
    have hmax : max 1 (nativePhysicalCap d : ℝ) ≤ d.scale := max_le hx1 hP
    have hle := Real.log_le_log
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)) hmax
    unfold logBudget
    linarith
  have hrough : 1 + Real.log (roughCap d) ≤ 2 * Real.log d.scale := by
    have hle := Real.log_le_log (by linarith : 0 < roughCap d) hR
    linarith
  have h8 : Real.log (8 * d.scale) ≤ 8 * Real.log d.scale := by
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hxpos.ne']
    have he := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)
    linarith
  have hA := hShiu.A_pos.le
  have hE := (uniformEulerConstant_pos 1).le
  have hphin := logBudget_nonneg (nativePhysicalCap d)
  have hroughn : 0 ≤ 1 + Real.log (roughCap d) := by
    have h := Real.log_nonneg hR1
    linarith
  unfold nativeLogFactor
  calc
    _ ≤ 180 * hShiu.A * uniformEulerConstant 1 * (2 * Real.log d.scale) *
        (2 * Real.log d.scale) ^ 4 * (8 * Real.log d.scale) := by
          gcongr <;> first | exact hphi | exact hrough | exact h8 | positivity
    _ = _ := by unfold nativeFinalConstant; ring

theorem exists_nativeKeyTail_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → X ≤ d.scale →
        nativePhysicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) →
        ‖nativeKeyTail d (roughZ d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨Xpay, hXpay, hpay⟩ :=
    exists_collapsed_smooth_tail_arbitrary_log 5 (A + 6) (by linarith)
  let X := max Xpay (max (3 * hShiu.X0)
    (max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1)))
  refine ⟨nativeFinalConstant hShiu, X, nativeFinalConstant_pos hShiu,
    hXpay.trans_le (le_max_left _ _), ?_⟩
  intro B sigma kappa c0 d k hd hXd hphysical
  have hxpay : Xpay ≤ d.scale := (le_max_left _ _).trans hXd
  have hrest : max (3 * hShiu.X0)
      (max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1)) ≤ d.scale :=
    (le_max_right _ _).trans hXd
  have hthreshold : 3 * hShiu.X0 ≤ d.scale := (le_max_left _ _).trans hrest
  have hother : max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1) ≤ d.scale :=
    (le_max_right _ _).trans hrest
  have hlarge0 : (3 : ℝ) ^ (9 : ℕ) + 1 ≤ d.scale := (le_max_left _ _).trans hother
  have hlarge : (3 : ℝ) ^ (9 : ℕ) < d.scale := by linarith
  have hx : 6 ≤ d.scale := by norm_num at hlarge0; linarith
  have hexp : Real.exp 1 + 1 ≤ d.scale := (le_max_right _ _).trans hother
  have hlog : 1 ≤ Real.log d.scale := by
    have he := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ d.scale by linarith)
    simpa only [Real.log_exp] using he
  have hLpos : 0 < Real.log d.scale := by linarith
  have htail := hpay d.scale hxpay
  have htail0 : 0 ≤ collapsedSmoothTail 5
      (Nat.floor (d.scale ^ ((4 : ℝ) / 5))) d.scale (roughZ d.scale) := by
    unfold collapsedSmoothTail
    apply Finset.sum_nonneg
    intro n hn
    positivity
  have hV : 0 ≤ fixedDScale d ((2 : ℝ) ^ k.d) := by
    unfold fixedDScale
    have hM : 0 ≤ d.V := by linarith [hd.2.1]
    have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    positivity
  have hC := (nativeFinalConstant_pos hShiu).le
  have hlogs := nativeLogFactor_le_six_logs hd hShiu hx hlog hphysical
  have hpow : Real.log d.scale ^ (6 : ℕ) * Real.log d.scale ^ (-(A + 6)) =
      Real.log d.scale ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ (nativeLogFactor hShiu d * fixedDScale d ((2 : ℝ) ^ k.d)) *
        collapsedSmoothTail 5 (Nat.floor (d.scale ^ ((4 : ℝ) / 5)))
          d.scale (roughZ d.scale) :=
      nativeKeyTail_le_collapsed_arithmetic hd hShiu hx hlarge hthreshold
        (roughZ d.scale) k hphysical
    _ ≤ (nativeFinalConstant hShiu * Real.log d.scale ^ 6 * fixedDScale d ((2 : ℝ) ^ k.d)) *
        Real.log d.scale ^ (-(A + 6)) := by
          gcongr <;> first | exact hlogs | exact htail | positivity
    _ = nativeFinalConstant hShiu *
        (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
      calc
        _ = (nativeFinalConstant hShiu * fixedDScale d ((2 : ℝ) ^ k.d)) *
            (Real.log d.scale ^ (6 : ℕ) * Real.log d.scale ^ (-(A + 6))) := by ring
        _ = _ := by rw [hpow]; ring

end
end ImbalancedChen.Part3OriginalS2NativeKeyTailPayment
