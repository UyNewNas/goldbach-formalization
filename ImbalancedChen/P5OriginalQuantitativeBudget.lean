import ImbalancedChen.P5OriginalCoefficientArithmetic
import ImbalancedChen.CurrentChenP5U9OriginalIntegralGap

/-!
# Quantitative budget for the original lower endpoint

SOURCE ONLY; UNCOMPILED. Proposed imports above refer to the staged names
of the two source-only drafts, not to accepted actual-tree modules.

Every discrepancy below is relative to a named original rational endpoint.
This file is coefficient arithmetic, not an assumption that the original
coefficient estimates have been proved. In particular the corrected Runbo
sixth integral and the true U9 integral remain real-valued expressions.
-/

namespace ImbalancedChen.P5OriginalCoefficientArithmetic

noncomputable section

/-- The exact unspent adopted margin after both original reserves. -/
def adoptedSlack : ℝ :=
  13457260926863633771775678584711245753 /
    2742952509978644604793778369418231808000000000

/-- The full direct reconstruction also retains its original rounding surplus. -/
def directSlack : ℝ := adoptedSlack + retainedRoundingSurplus

theorem adoptedSlack_pos : 0 < adoptedSlack := by
  norm_num [adoptedSlack]

theorem directSlack_pos : 0 < directSlack := by
  exact add_pos adoptedSlack_pos retainedRoundingSurplus_pos

theorem directSlack_exact :
    directReconstruction - 2 * eachReserve - currentC = directSlack := by
  rw [direct_eq_adopted_add_surplus]
  have h := exact_currentC_slack
  change adoptedReconstruction - 2 * eachReserve - currentC = adoptedSlack at h
  dsimp [directSlack]
  linarith

/-- Put actual or independently enclosed original coefficients into their
original slots. The joint final cost retains both original occurrences. -/
def coefficientReconstruction (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ) : ℝ :=
  root L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 + priorityParentReplacement +
    (ordinaryStartChange - removedH248 + weightedSixIntegrals + slantedRestoration) / 4 +
    baselineContinuation + sameMaskIncrement

/-- Named, oriented discrepancies: positive values always consume margin.
The multipliers 3 and 2 are the literal original signed multiplicities. -/
def originalCharge (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ) : ℝ :=
  3 * (savedL1 - L1) + (savedL2 - L2) + (savedL5 - L5) + (savedL6 - L6) +
    (U3 - savedU3) + (U4 - savedU4) + 2 * (U7 - savedU7) +
    (U8 - savedU8) + (U9 - savedU9) + (U1011 - savedU1011)

theorem originalCharge_exact (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ) :
    directReconstruction - coefficientReconstruction L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 =
      originalCharge L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 / 4 := by
  dsimp [directReconstruction, directAtK0, savedRoot,
    coefficientReconstruction, originalCharge, root]
  ring

/-- The precise margin threshold for the original coefficients. There is no
whole-weight estimate in the premises; this is an identity on real inputs. -/
theorem original_coefficients_meet_currentC_iff
    (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ) :
    currentC ≤ coefficientReconstruction L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 -
      2 * eachReserve ↔
    originalCharge L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 ≤ 4 * directSlack := by
  have he := originalCharge_exact L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011
  have hs := directSlack_exact
  constructor <;> intro h <;> linarith

/-- Separate usable bounds for each original coefficient discrepancy. The
joint U10+U11 budget is supplied as a joint cost, without a fabricated split. -/
theorem originalCharge_le_individual_budgets
    (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ)
    (e1 e2 e5 e6 e3 e4 e7 e8 e9 e1011 : ℝ)
    (h1 : savedL1 - L1 ≤ e1) (h2 : savedL2 - L2 ≤ e2)
    (h5 : savedL5 - L5 ≤ e5) (h6 : savedL6 - L6 ≤ e6)
    (h3 : U3 - savedU3 ≤ e3) (h4 : U4 - savedU4 ≤ e4)
    (h7 : U7 - savedU7 ≤ e7) (h8 : U8 - savedU8 ≤ e8)
    (h9 : U9 - savedU9 ≤ e9) (h1011 : U1011 - savedU1011 ≤ e1011) :
    originalCharge L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 ≤
      3 * e1 + e2 + e5 + e6 + e3 + e4 + 2 * e7 + e8 + e9 + e1011 := by
  dsimp [originalCharge]
  linarith only [h1, h2, h5, h6, h3, h4, h7, h8, h9, h1011]

theorem currentC_of_individual_original_budgets
    (L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 : ℝ)
    (e1 e2 e5 e6 e3 e4 e7 e8 e9 e1011 : ℝ)
    (h1 : savedL1 - L1 ≤ e1) (h2 : savedL2 - L2 ≤ e2)
    (h5 : savedL5 - L5 ≤ e5) (h6 : savedL6 - L6 ≤ e6)
    (h3 : U3 - savedU3 ≤ e3) (h4 : U4 - savedU4 ≤ e4)
    (h7 : U7 - savedU7 ≤ e7) (h8 : U8 - savedU8 ≤ e8)
    (h9 : U9 - savedU9 ≤ e9) (h1011 : U1011 - savedU1011 ≤ e1011)
    (hbudget : 3 * e1 + e2 + e5 + e6 + e3 + e4 + 2 * e7 + e8 + e9 + e1011 ≤
      4 * directSlack) :
    currentC ≤ coefficientReconstruction L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011 -
      2 * eachReserve := by
  apply (original_coefficients_meet_currentC_iff L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011).mpr
  exact (originalCharge_le_individual_budgets L1 L2 L5 L6 U3 U4 U7 U8 U9 U1011
    e1 e2 e5 e6 e3 e4 e7 e8 e9 e1011 h1 h2 h5 h6 h3 h4 h7 h8 h9 h1011).trans hbudget

/-- A concrete positive uniform allocation for the ten stored original
endpoints. Their absolute coefficient norm is 13 because U10+U11 is joint. -/
def equalStoredEndpointBudget : ℝ := adoptedSlack / 4

theorem equalStoredEndpointBudget_pos : 0 < equalStoredEndpointBudget := by
  exact div_pos adoptedSlack_pos (by norm_num)

theorem equalStoredEndpointBudget_exact_remaining :
    directSlack - (3 * equalStoredEndpointBudget + equalStoredEndpointBudget +
      equalStoredEndpointBudget + equalStoredEndpointBudget + equalStoredEndpointBudget +
      equalStoredEndpointBudget + 2 * equalStoredEndpointBudget + equalStoredEndpointBudget +
      equalStoredEndpointBudget + equalStoredEndpointBudget) / 4 =
      3 * adoptedSlack / 16 + retainedRoundingSurplus := by
  dsimp [directSlack, equalStoredEndpointBudget]
  ring

theorem equalStoredEndpointBudget_fits :
    13 * equalStoredEndpointBudget < 4 * directSlack := by
  dsimp [equalStoredEndpointBudget, directSlack]
  linarith [adoptedSlack_pos, retainedRoundingSurplus_pos]

/-- These are individual real discrepancies, not new hypotheses that the
enhanced historical estimator is equal to the corrected ordinary one. -/
def correctedSixthDiscrepancy : ℝ := savedL6 - correctedOrdinarySixth
def originalNinthDiscrepancy : ℝ :=
  currentK * currentChenUpsilon9HarmonicIntegral - savedU9
def ordinaryNinthDiscrepancy : ℝ :=
  8 * currentChenUpsilon9HarmonicIntegral - savedU9
def ninthLeadingCharge : ℝ :=
  (8 - currentK) * currentChenUpsilon9HarmonicIntegral

theorem ordinaryNinthDiscrepancy_exact :
    ordinaryNinthDiscrepancy = originalNinthDiscrepancy + ninthLeadingCharge := by
  dsimp [ordinaryNinthDiscrepancy, originalNinthDiscrepancy, ninthLeadingCharge]
  ring

/-- Actual corrected Runbo L6 and actual original-K U9, with every other
original endpoint fixed, have precisely these two unresolved discrepancies. -/
theorem corrected_sixth_original_ninth_charge :
    originalCharge savedL1 savedL2 savedL5 correctedOrdinarySixth savedU3 savedU4
      savedU7 savedU8 (currentK * currentChenUpsilon9HarmonicIntegral) savedU1011 =
      correctedSixthDiscrepancy + originalNinthDiscrepancy := by
  dsimp [originalCharge, correctedSixthDiscrepancy, originalNinthDiscrepancy]
  ring

theorem corrected_sixth_ordinary_ninth_charge :
    originalCharge savedL1 savedL2 savedL5 correctedOrdinarySixth savedU3 savedU4
      savedU7 savedU8 (8 * currentChenUpsilon9HarmonicIntegral) savedU1011 =
      correctedSixthDiscrepancy + originalNinthDiscrepancy + ninthLeadingCharge := by
  dsimp [originalCharge, correctedSixthDiscrepancy, originalNinthDiscrepancy,
    ninthLeadingCharge]
  ring

theorem corrected_sixth_original_ninth_meet_currentC_iff :
    currentC ≤ coefficientReconstruction savedL1 savedL2 savedL5 correctedOrdinarySixth
      savedU3 savedU4 savedU7 savedU8 (currentK * currentChenUpsilon9HarmonicIntegral)
      savedU1011 - 2 * eachReserve ↔
    correctedSixthDiscrepancy + originalNinthDiscrepancy ≤ 4 * directSlack := by
  rw [original_coefficients_meet_currentC_iff, corrected_sixth_original_ninth_charge]

private theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

/-- Uses the real original U9 integral floor proved by the U9 owner. -/
theorem ninthLeadingCharge_lower :
    (32504409 / 625000000 : ℝ) ≤ ninthLeadingCharge := by
  have hJ := currentChenP5U9HarmonicIntegral_ge_log_two
  have hlog := half_le_log_two
  have hJrat : (21 / 500 : ℝ) ≤ currentChenUpsilon9HarmonicIntegral := by
    linarith
  dsimp [ninthLeadingCharge]
  rw [currentChenP5U9_eight_sub_originalK]
  nlinarith only [hJrat]

theorem ninthLeadingCharge_quarter_lower :
    (32504409 / 2500000000 : ℝ) ≤ ninthLeadingCharge / 4 := by
  have h := ninthLeadingCharge_lower
  linarith

theorem ninthLeadingCharge_exceeds_all_original_slack :
    4 * directSlack < ninthLeadingCharge := by
  have hsmall : 4 * directSlack < (32504409 / 625000000 : ℝ) := by
    norm_num [directSlack, adoptedSlack, retainedRoundingSurplus]
  exact hsmall.trans_le ninthLeadingCharge_lower

/-- An ordinary coefficient-eight replacement cannot be charged to the
unspent original margin alone. This does not claim the true Chen theorem is
false; the necessary compensating improvement must be exhibited elsewhere. -/
theorem ordinary_fallback_benchmark_below_currentC :
    directReconstruction - ninthLeadingCharge / 4 - 2 * eachReserve < currentC := by
  have hs := directSlack_exact
  have hgap := ninthLeadingCharge_exceeds_all_original_slack
  linarith

/-- If the corrected sixth / ordinary ninth substitution nevertheless fits,
their remaining original discrepancies must provide an explicit negative
charge. No historical sixth equality is silently used to cancel the defect. -/
theorem ordinary_fallback_requires_compensating_credit
    (hfit : currentC ≤ coefficientReconstruction savedL1 savedL2 savedL5
      correctedOrdinarySixth savedU3 savedU4 savedU7 savedU8
      (8 * currentChenUpsilon9HarmonicIntegral) savedU1011 - 2 * eachReserve) :
    correctedSixthDiscrepancy + originalNinthDiscrepancy ≤
      4 * directSlack - ninthLeadingCharge ∧
    correctedSixthDiscrepancy + originalNinthDiscrepancy < 0 := by
  have hc := (original_coefficients_meet_currentC_iff savedL1 savedL2 savedL5
    correctedOrdinarySixth savedU3 savedU4 savedU7 savedU8
    (8 * currentChenUpsilon9HarmonicIntegral) savedU1011).mp hfit
  rw [corrected_sixth_ordinary_ninth_charge] at hc
  have hg := ninthLeadingCharge_exceeds_all_original_slack
  constructor <;> linarith

theorem ordinary_fallback_without_credit_below_currentC
    (hnoCredit : 0 ≤ correctedSixthDiscrepancy + originalNinthDiscrepancy) :
    coefficientReconstruction savedL1 savedL2 savedL5 correctedOrdinarySixth
      savedU3 savedU4 savedU7 savedU8 (8 * currentChenUpsilon9HarmonicIntegral)
      savedU1011 - 2 * eachReserve < currentC := by
  by_contra h
  have hfit := le_of_not_gt h
  have hcredit := (ordinary_fallback_requires_compensating_credit hfit).2
  linarith

end
end ImbalancedChen.P5OriginalCoefficientArithmetic
