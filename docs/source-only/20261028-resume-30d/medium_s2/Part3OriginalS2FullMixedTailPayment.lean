import ImbalancedChen.Part3OriginalS2FullMixedCollapsedTail
import Mathlib.Tactic

/-!
The arithmetic collapsed tail (8) pays the ACTUAL full same-psi S2
three-tail family. Constants precede all atoms and moving residues.
The physical range gate physicalCap<=floor(x^(4/5)) remains the original
separate range-(7) interface. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
-/

namespace ImbalancedChen.Part3OriginalS2FullMixedTailPayment

open ImbalancedChen.Part3
open ImbalancedChen.Part3OriginalS2ActualBlockGeometry
open ImbalancedChen.Part3OriginalS2SameGevreyShiuWindows
open ImbalancedChen.Part3OriginalS2FullMixedCollapsedTail
open ImbalancedChen.Part3OriginalSmoothCollapsedHalfRankin
open ImbalancedChen.Part3OriginalSmoothCollapsedArbitraryLog
open ImbalancedChen.Part3OriginalS2RoughZLargeXGate
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuEuler20261028
open ImbalancedChen.P5Z.RoughSquareWeightedBudget
open Classical Finset
open scoped BigOperators

noncomputable section

theorem roughCap_le_physicalCap
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    roughCap d ≤ (physicalCap d : ℝ) := by
  have hQ1 : 1 ≤ d.Q1 := hd.2.2.1
  have hQ2 : 1 ≤ d.Q2 := hd.2.2.2.1
  have hQ3 : 1 ≤ d.Q3 := hd.2.2.2.2.1
  have h23 : 1 ≤ d.Q2 * d.Q3 :=
    (by simpa using mul_le_mul hQ2 hQ3 zero_le_one (by linarith : 0 ≤ d.Q2))
  have h123 : 1 ≤ d.Q1 * (d.Q2 * d.Q3) :=
    (by simpa using mul_le_mul hQ1 h23 zero_le_one (by linarith : 0 ≤ d.Q1))
  have hmult := mul_le_mul_of_nonneg_right hQ1 (by linarith : 0 ≤ d.Q2 * d.Q3)
  have hfloor := Nat.lt_floor_add_one (8 * d.Q1 * d.Q2 * d.Q3)
  dsimp [roughCap, physicalCap]
  nlinarith

theorem physicalCap_le_scale
    {d : MediumAtom} (hx : 1 ≤ d.scale)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    (physicalCap d : ℝ) ≤ d.scale := by
  calc
    _ ≤ (Nat.floor (d.scale ^ ((4 : ℝ) / 5)) : ℝ) := by exact_mod_cast hphysical
    _ ≤ d.scale ^ ((4 : ℝ) / 5) :=
      Nat.floor_le (Real.rpow_nonneg (by linarith : 0 ≤ d.scale) _)
    _ ≤ d.scale := Real.rpow_le_self_of_one_le hx (by norm_num)

def finalConstant
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ)) : ℝ :=
  23040 * hShiu.A * uniformEulerConstant 1

theorem finalConstant_pos
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ)) :
    0 < finalConstant hShiu := by
  unfold finalConstant
  exact mul_pos (mul_pos (by norm_num) hShiu.A_pos) (uniformEulerConstant_pos 1)

theorem wholeLogFactor_le_six_logs
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (hx : 6 ≤ d.scale) (hlog : 1 ≤ Real.log d.scale)
    (hphysical : physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5))) :
    wholeLogFactor hShiu d ≤ finalConstant hShiu * Real.log d.scale ^ 6 := by
  have hx1 : 1 ≤ d.scale := by linarith
  have hxpos : 0 < d.scale := by linarith
  have hP := physicalCap_le_scale hx1 hphysical
  have hR := (roughCap_le_physicalCap hd).trans hP
  have hR1 := one_le_roughCap hd
  have hphi : logBudget (physicalCap d) ≤ 2 * Real.log d.scale := by
    have hmax : max 1 (physicalCap d : ℝ) ≤ d.scale := max_le hx1 hP
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
  have hphin := logBudget_nonneg (physicalCap d)
  have hroughn : 0 ≤ 1 + Real.log (roughCap d) := by
    have h := Real.log_nonneg hR1
    linarith
  unfold wholeLogFactor
  calc
    _ ≤ 90 * hShiu.A * uniformEulerConstant 1 * (2 * Real.log d.scale) *
        (2 * Real.log d.scale) ^ 4 * (8 * Real.log d.scale) := by
          gcongr <;> first | exact hphi | exact hrough | exact h8 | positivity
    _ = _ := by unfold finalConstant; ring

/-- The full mixed family, including every d, has arbitrary logarithmic
saving at its explicit whole-family normalization V0=M*N^2/Q1. For a
fixed d~D subfamily, the earlier subset geometry retains Y=Q1*D instead. -/
theorem exists_fullSamePsiTail_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom),
        MediumAdmissible B sigma kappa c0 d → X ≤ d.scale →
        physicalCap d ≤ Nat.floor (d.scale ^ ((4 : ℝ) / 5)) →
        ‖fullSamePsiTail d (roughZ d.scale)‖ ≤
          C * (wholeFamilyScale d * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨Xpay, hXpay, hpay⟩ :=
    exists_collapsed_smooth_tail_arbitrary_log 5 (A + 6) (by linarith)
  let X := max Xpay (max (3 * hShiu.X0)
    (max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1)))
  refine ⟨finalConstant hShiu, X, finalConstant_pos hShiu,
    hXpay.trans_le (le_max_left _ _), ?_⟩
  intro B sigma kappa c0 d hd hXd hphysical
  have hxpay : Xpay ≤ d.scale := (le_max_left _ _).trans hXd
  have hrest : max (3 * hShiu.X0)
      (max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1)) ≤ d.scale :=
    (le_max_right _ _).trans hXd
  have hthreshold : 3 * hShiu.X0 ≤ d.scale := (le_max_left _ _).trans hrest
  have hother : max ((3 : ℝ) ^ (9 : ℕ) + 1) (Real.exp 1 + 1) ≤ d.scale :=
    (le_max_right _ _).trans hrest
  have hlarge0 : (3 : ℝ) ^ (9 : ℕ) + 1 ≤ d.scale :=
    (le_max_left _ _).trans hother
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
  have hV0 : 0 ≤ wholeFamilyScale d := by
    unfold wholeFamilyScale
    have hV : 0 ≤ d.V := by linarith [hd.2.1]
    have hQ : 0 ≤ d.Q1 := by linarith [hd.2.2.1]
    positivity
  have hC := (finalConstant_pos hShiu).le
  have hlogs := wholeLogFactor_le_six_logs hd hShiu hx hlog hphysical
  have hpow : Real.log d.scale ^ (6 : ℕ) * Real.log d.scale ^ (-(A + 6)) =
      Real.log d.scale ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hLpos]
    congr 1
    ring
  calc
    _ ≤ (wholeLogFactor hShiu d * wholeFamilyScale d) *
        collapsedSmoothTail 5 (Nat.floor (d.scale ^ ((4 : ℝ) / 5)))
          d.scale (roughZ d.scale) :=
      fullSamePsiTail_le_collapsed_arithmetic hd hShiu hx hlarge hthreshold
        (roughZ d.scale) hphysical
    _ ≤ (finalConstant hShiu * Real.log d.scale ^ 6 * wholeFamilyScale d) *
        Real.log d.scale ^ (-(A + 6)) := by
          gcongr <;> first | exact hlogs | exact htail | positivity
    _ = finalConstant hShiu *
        (wholeFamilyScale d * (Real.log d.scale) ^ (-A)) := by
      calc
        _ = (finalConstant hShiu * wholeFamilyScale d) *
            (Real.log d.scale ^ (6 : ℕ) * Real.log d.scale ^ (-(A + 6))) := by ring
        _ = _ := by rw [hpow]; ring

end
end ImbalancedChen.Part3OriginalS2FullMixedTailPayment
