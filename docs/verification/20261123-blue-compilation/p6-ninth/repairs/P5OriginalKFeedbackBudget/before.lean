import ImbalancedChen.P5OriginalQuantitativeBudget

/-!
# Original lower endpoint with a slightly larger product-density coefficient

SOURCE ONLY; UNCOMPILED. This is a conservative original numerical
majorant functional, not an assertion that the true Chen mean is affine.

The precise source of the slopes is
`proof-library/source/upper-k-to-current-lower-feedback-20261009.tex`:
U7/U8/U9 use the independent Simpson *lower* endpoints at K0, whereas
the retained U10/U11 method-zero cells use their saved rounded decreases.
One cannot replace these slopes by the saved upper endpoints/K0.

The new same-mask gross is K-linear; its saved-floor recovery is constant.
Both original lower reserves are kept fixed. All table choices are fixed
at their original anchor, and the explicit delta range stays below it.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section

def lowerU7AtK0 : ℝ :=
  7183180737282426411788973366247539 / 5192296858534827628530496329220096
def lowerU8AtK0 : ℝ :=
  21065542644621920270107869035005941 / 5192296858534827628530496329220096
def lowerU9AtK0 : ℝ :=
  16911485600294926597530591281091713 / 5192296858534827628530496329220096

def switchedSlope789 : ℝ :=
  (2 * lowerU7AtK0 + lowerU8AtK0 + lowerU9AtK0) / (4 * K0)

theorem switchedSlope789_value :
    switchedSlope789 =
      8178654643669015576752563601342614375 /
        21943620079829156838350226955345854464 := by
  norm_num [switchedSlope789, lowerU7AtK0, lowerU8AtK0, lowerU9AtK0, K0]

def savedRetainedCostDecrease : ℝ := 9254169352455641693 / 1208925819614629174706176
def oldFeedbackStep : ℝ := 1 / 10000
def retainedJointSlope : ℝ := savedRetainedCostDecrease / (4 * oldFeedbackStep)

theorem retainedJointSlope_value :
    retainedJointSlope = 5783855845284776058125 / 302231454903657293676544 := by
  norm_num [retainedJointSlope, savedRetainedCostDecrease, oldFeedbackStep]

theorem originalFeedbackSlope_decomposition :
    switchedSlope789 + retainedJointSlope = originalFeedbackSlope := by
  rw [switchedSlope789_value, retainedJointSlope_value]
  norm_num [originalFeedbackSlope]

/-- The original individual K-dependent upper envelopes. -/
def U7Envelope (k : ℝ) : ℝ := savedU7 - (K0 - k) * lowerU7AtK0 / K0
def U8Envelope (k : ℝ) : ℝ := savedU8 - (K0 - k) * lowerU8AtK0 / K0
def U9Envelope (k : ℝ) : ℝ := savedU9 - (K0 - k) * lowerU9AtK0 / K0

/-- Only the unchanged method-zero cells contribute the variable part.
Ordinary-selected cells and priority parents remain in the original constant. -/
def U1011Envelope (k : ℝ) : ℝ := savedU1011 - 4 * (K0 - k) * retainedJointSlope

/-- The entire original root with the same individual switched-cost slots. -/
def originalVariableRoot (k : ℝ) : ℝ :=
  root savedL1 savedL2 savedL5 savedL6 savedU3 savedU4
    (U7Envelope k) (U8Envelope k) (U9Envelope k) (U1011Envelope k)

theorem originalVariableRoot_exact (k : ℝ) :
    originalVariableRoot k = savedRoot + originalFeedbackSlope * (K0 - k) := by
  rw [← originalFeedbackSlope_decomposition]
  dsimp [originalVariableRoot, savedRoot, root, U7Envelope, U8Envelope,
    U9Envelope, U1011Envelope, switchedSlope789]
  norm_num [K0] <;> ring

/-- A real cost k*J remains below the original affine envelope throughout
k≤K0. The two hypotheses are the original local upper/lower enclosures of
the same analytic integral; they are not a whole-ledger estimate. -/
theorem complete_switched_cost_envelope
    (J E lower k : ℝ) (hupper : K0 * J ≤ E) (hlower : lower / K0 ≤ J)
    (hk : k ≤ K0) :
    k * J ≤ E - (K0 - k) * lower / K0 := by
  have hprod := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hlower)
  have hid : (K0 - k) * lower / K0 = (K0 - k) * (lower / K0) := by ring
  rw [hid]
  nlinarith only [hupper, hprod]

/-- The saved nonnegative method-zero slope extends to k just above currentK
as long as k≤K0. This is the same positive cell majorant as in the source. -/
theorem retained_cell_envelope
    (T A s k : ℝ) (hT : K0 * T ≤ A) (hs : s ≤ A / K0)
    (hk0 : 0 ≤ k) (hk : k ≤ K0) :
    k * T ≤ A - (K0 - k) * s := by
  have hK0 : 0 < K0 := by norm_num [K0]
  have hTa : T ≤ A / K0 := (le_div_iff₀ hK0).mpr (by nlinarith only [hT])
  have hscaled := mul_le_mul_of_nonneg_left hTa hk0
  have hremaining := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hs)
  have hcancel : K0 * (A / K0) = A := by field_simp [K0] <;> ring
  nlinarith only [hscaled, hremaining, hcancel]

/-- The removed gross estimate scales with k. Its lower-bound witness is
one local positive integral, not an upper bound for the removed true count. -/
theorem removed_gross_scaling (I G k : ℝ)
    (hG : G ≤ currentK * I / 8) (hk : 0 ≤ k) :
    G * k / currentK ≤ k * I / 8 := by
  have hK : 0 < currentK := by norm_num [currentK]
  have hm := mul_le_mul_of_nonneg_right hG (div_nonneg hk hK.le)
  have heq : (currentK * I / 8) * (k / currentK) = k * I / 8 := by
    field_simp [ne_of_gt hK] <;> ring
  rw [heq] at hm
  convert hm using 1 <;> ring

def allRemovedGross : ℝ := E0Gross + E1Gross + extraSameMaskGross
def variableRemovedGross (k : ℝ) : ℝ := allRemovedGross * k / currentK

theorem allRemovedGross_value : allRemovedGross = 3226629 / 500000000 := by
  norm_num [allRemovedGross, E0Gross, E1Gross, extraSameMaskGross]

/-- The final original raw endpoint with the literal four switched envelopes,
fixed start/table/restoration entries, and the same selected mask. -/
def adoptedRawWithDensityCoefficient (k : ℝ) : ℝ :=
  adoptedAtK0 + (originalVariableRoot k - savedRoot) + table248to312 + table312to430 +
    variableRemovedGross k - replacementSavedFloorPayment

def finalFeedbackSlope : ℝ := originalFeedbackSlope - allRemovedGross / currentK

theorem finalFeedbackSlope_value :
    finalFeedbackSlope =
      258927760442716265426451560820213255040820787 /
        662397247406248872798412414697830450253004800 := by
  rw [finalFeedbackSlope, allRemovedGross_value]
  norm_num [originalFeedbackSlope, currentK]

theorem finalFeedbackSlope_pos : 0 < finalFeedbackSlope := by
  rw [finalFeedbackSlope_value]
  norm_num

theorem finalFeedbackSlope_le_two_fifths : finalFeedbackSlope ≤ (2 / 5 : ℝ) := by
  rw [finalFeedbackSlope_value]
  norm_num

theorem adoptedRawWithDensityCoefficient_current :
    adoptedRawWithDensityCoefficient currentK = adoptedReconstruction := by
  rw [adoptedRawWithDensityCoefficient, originalVariableRoot_exact]
  dsimp [variableRemovedGross, adoptedReconstruction, baselineContinuation,
    sameMaskIncrement, allRemovedGross]
  have hK : currentK ≠ 0 := by norm_num [currentK]
  field_simp [hK] <;> ring

/-- The exact loss, including the original paired gross feedback. The loss
recovery is constant and therefore contributes no K derivative. -/
theorem density_coefficient_extra_loss (delta : ℝ) :
    adoptedRawWithDensityCoefficient (currentK + delta) =
      adoptedReconstruction - finalFeedbackSlope * delta := by
  rw [← adoptedRawWithDensityCoefficient_current]
  simp only [adoptedRawWithDensityCoefficient, originalVariableRoot_exact]
  dsimp [variableRemovedGross, finalFeedbackSlope]
  ring

/-- Exact margin condition for the fixed original two reserves. -/
theorem density_coefficient_budget_iff (delta : ℝ) :
    currentC ≤ adoptedRawWithDensityCoefficient (currentK + delta) - 2 * eachReserve ↔
      finalFeedbackSlope * delta ≤ adoptedSlack := by
  rw [density_coefficient_extra_loss]
  have h := exact_currentC_slack
  change adoptedReconstruction - 2 * eachReserve - currentC = adoptedSlack at h
  constructor <;> intro hb <;> linarith

/-- The 430 table was generated at this original larger product coefficient. -/
def originalTableAnchor : ℝ := 6761767 / 1000000

/-- A concrete strictly positive allowed interval. -/
def allowedDensityDelta : ℝ := 1 / 100000000

theorem allowedDensityDelta_pos : 0 < allowedDensityDelta := by
  norm_num [allowedDensityDelta]

theorem allowedDensityDelta_below_original_anchors :
    currentK + allowedDensityDelta < originalTableAnchor ∧
      currentK + allowedDensityDelta < K0 := by
  norm_num [currentK, allowedDensityDelta, originalTableAnchor, K0]

theorem allowedDensityDelta_fits_original_slack :
    finalFeedbackSlope * allowedDensityDelta < adoptedSlack := by
  rw [finalFeedbackSlope_value]
  norm_num [allowedDensityDelta, adoptedSlack]

/-- P4-A may supply the fixed positive error delta in this interval. This
arithmetic theorem spends it once, with both original lower reserves intact.
The actual positive-family distribution and cost-enclosure suppliers remain
separate obligations; this is not an eventual D12 lower theorem. -/
theorem currentC_of_density_coefficient_delta {delta : ℝ}
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ allowedDensityDelta) :
    currentK + delta ≤ originalTableAnchor ∧ currentK + delta ≤ K0 ∧
      currentC < adoptedRawWithDensityCoefficient (currentK + delta) - 2 * eachReserve := by
  have hanchors := allowedDensityDelta_below_original_anchors
  have hcharge := mul_le_mul_of_nonneg_left hdelta finalFeedbackSlope_pos.le
  have hstrict := allowedDensityDelta_fits_original_slack
  have hs := exact_currentC_slack
  change adoptedReconstruction - 2 * eachReserve - currentC = adoptedSlack at hs
  rw [density_coefficient_extra_loss]
  refine ⟨?_, ?_, ?_⟩ <;> linarith

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
