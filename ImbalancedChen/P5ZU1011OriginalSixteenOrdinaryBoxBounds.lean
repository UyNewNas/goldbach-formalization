import ImbalancedChen.P5ZU1011LiteralH248IntervalBounds
import ImbalancedChen.P5ZU1011OriginalSixteenBoxCertificates

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual original sixteen-policy ordinary cost bounds from the independently
proved true cap/residual box circuit and the literal finite H248 interval
extrema. Positive w and residual guards are rational and explicit. No
kernel-bound or floor-interval conclusion is an input. Singleton knots,
clamp50 and the zero exterior all remain in the finite lookup extrema.
-/

namespace ImbalancedChen.P5Z.OriginalSixteenOrdinaryBoxBounds

noncomputable section

open U11Integral U1011OriginalSixteenPolicyBank Part5UpperTables
open U1011OriginalSixteenPolicyBank.BoxCertificates
open LiteralH248IntervalBounds

def ratioLower (p : Policy) (B : Box) : ℚ := residualLower p B / B.hi 3
def ratioUpper (p : Policy) (B : Box) : ℚ := residualUpper p B / B.lo 3
def floorLower (p : Policy) (B : Box) : ℚ :=
  profileIntervalLower (ratioLower p B) (ratioUpper p B)
def floorUpper (p : Policy) (B : Box) : ℚ :=
  profileIntervalUpper (ratioLower p B) (ratioUpper p B)
def ordinaryLower (p : Policy) (B : Box) : ℚ :=
  4 * (1 - floorUpper p B) / residualUpper p B
def ordinaryUpper (p : Policy) (B : Box) : ℚ :=
  4 * (1 - floorLower p B) / residualLower p B

/-- These are genuine positivity checks, not an ordinary cost supplier. -/
def PositiveGuards (p : Policy) (B : Box) : Prop := 0 < B.lo 3 ∧ 0 < residualLower p B

instance (p : Policy) (B : Box) : Decidable (PositiveGuards p B) := by
  unfold PositiveGuards
  infer_instance

theorem ratio_bounds (p : Policy) (B : Box) (hg : PositiveGuards p B)
    {v : LogFour} (hv : v ∈ B.region) :
    (ratioLower p B : ℝ) ≤ typedResidual p v / v 3 ∧
      typedResidual p v / v 3 ≤ (ratioUpper p B : ℝ) := by
  have hr := residual_bounds p B hv
  have hwL : (0 : ℝ) < (B.lo 3 : ℝ) := by exact_mod_cast hg.1
  have hRL : (0 : ℝ) < (residualLower p B : ℝ) := by exact_mod_cast hg.2
  have hw : 0 < v 3 := hwL.trans_le (hv.1 3)
  have hwU : (0 : ℝ) < (B.hi 3 : ℝ) := hw.trans_le (hv.2 3)
  have hR : 0 < typedResidual p v := hRL.trans_le hr.1
  have hRU : (0 : ℝ) < (residualUpper p B : ℝ) := hR.trans_le hr.2
  simp only [ratioLower, ratioUpper, Rat.cast_div]
  constructor
  · exact (div_le_div_of_nonneg_left hRL.le hw (hv.2 3)).trans
      (div_le_div_of_nonneg_right hr.1 hw.le)
  · exact (div_le_div_of_nonneg_right hr.2 hw.le).trans
      (div_le_div_of_nonneg_left hRU.le hwL (hv.1 3))

theorem literal_floor_bounds (p : Policy) (B : Box) (hg : PositiveGuards p B)
    {v : LogFour} (hv : v ∈ B.region) :
    (floorLower p B : ℝ) ≤ H248 (max 2 (typedResidual p v / v 3)) ∧
      H248 (max 2 (typedResidual p v / v 3)) ≤ (floorUpper p B : ℝ) := by
  have hr := ratio_bounds p B hg hv
  exact profileInterval_bounds hr.1 hr.2

theorem floor_range (p : Policy) (B : Box) (hg : PositiveGuards p B)
    {v : LogFour} (hv : v ∈ B.region) :
    0 ≤ floorLower p B ∧ floorLower p B ≤ floorUpper p B ∧ floorUpper p B ≤ 1 := by
  have hr := ratio_bounds p B hg hv
  have hlu : ratioLower p B ≤ ratioUpper p B := by exact_mod_cast hr.1.trans hr.2
  exact profileInterval_range hlu

theorem typed_ordinary_bounds (p : Policy) (B : Box) (hg : PositiveGuards p B)
    {v : LogFour} (hv : v ∈ B.region) :
    (ordinaryLower p B : ℝ) ≤
        4 * (1 - H248 (max 2 (typedResidual p v / v 3))) / typedResidual p v ∧
      4 * (1 - H248 (max 2 (typedResidual p v / v 3))) / typedResidual p v ≤
        (ordinaryUpper p B : ℝ) := by
  have hr := residual_bounds p B hv
  have hH := literal_floor_bounds p B hg hv
  have hRange := floor_range p B hg hv
  have hRL : (0 : ℝ) < (residualLower p B : ℝ) := by exact_mod_cast hg.2
  have hR : 0 < typedResidual p v := hRL.trans_le hr.1
  have hRU : (0 : ℝ) < (residualUpper p B : ℝ) := hR.trans_le hr.2
  have hHU : (floorUpper p B : ℝ) ≤ 1 := by exact_mod_cast hRange.2.2
  have hHL : (floorLower p B : ℝ) ≤ 1 := by exact_mod_cast hRange.2.1.trans hRange.2.2
  have hNumL : 0 ≤ 4 * (1 - (floorUpper p B : ℝ)) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hHU)
  have hNumU : 0 ≤ 4 * (1 - (floorLower p B : ℝ)) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr hHL)
  simp only [ordinaryLower, ordinaryUpper, Rat.cast_div, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_one, Rat.cast_ofNat]
  constructor
  · exact (div_le_div_of_nonneg_left hNumL hR hr.2).trans
      (div_le_div_of_nonneg_right (by linarith only [hH.2]) hR.le)
  · exact (div_le_div_of_nonneg_right (by linarith only [hH.1]) hR.le).trans
      (div_le_div_of_nonneg_left hNumU hRL hr.1)

theorem residual_policy (p : Policy) (v : LogFour) :
    residual p.val v = typedResidual p v := by
  simp only [residual, dif_pos p.isLt]

/-- The output bounds the ORIGINAL actual-bank ordinary kernel itself,
not a surrogate typed cost or a generic supplied cell envelope. -/
theorem actual_ordinary_bounds (p : Policy) (B : Box) (hg : PositiveGuards p B)
    {v : LogFour} (hv : v ∈ B.region) :
    (ordinaryLower p B : ℝ) ≤ ordinaryKernel H248 residual p.val v ∧
      ordinaryKernel H248 residual p.val v ≤ (ordinaryUpper p B : ℝ) := by
  simpa only [ordinaryKernel, residual_policy] using typed_ordinary_bounds p B hg hv

end

end ImbalancedChen.P5Z.OriginalSixteenOrdinaryBoxBounds
