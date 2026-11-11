import ImbalancedChen.P4AOriginalFull87EighthKernelIntegration
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Exact quantitative transport from the SAME actual, licensed sixth parent
in a REALIZED eight-prime history to the original comparison parent.
The original finite eighth cap, strict trim, Source, and original beta/physical
policies are unchanged.  This is a pointwise residual identity, NOT a
claim that a signed sieve gain is monotone, an ordinary mean asymptotic,
an actual prime-source existence theorem, or a paid density reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87ActualParentResidualGap
noncomputable section

open Set VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87ActualCommonHistory (RealizedHistory)
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87EighthKernelTransport
open P4AOriginalFull87EighthKernelIntegration

/-- Unlike mere parent monotonicity, this is the exact additional residual
from replacing the original comparison parent R by the TRUE sixth parent P.
The finite endpoint M is held fixed on both sides. -/
theorem residual_parent_gap_exact (S J P R M : ℝ)
    (hP : 0 < P - S) (hR : 0 < R - S)
    (hM : 0 < M - S) (hJ : 0 < J) :
    residual S J P M - residual S J R M =
      4 * (R - P) / ((P - S) * (R - S) * J) := by
  rw [residual_eq_reciprocal S J P M hP.ne' hM.ne' hJ.ne',
    residual_eq_reciprocal S J R M hR.ne' hM.ne' hJ.ne']
  field_simp [hP.ne', hR.ne', hM.ne', hJ.ne']
  <;> ring

/-- A one-sided, numerical parent mismatch budget. The input is the
actual parent separation R-P, not an invented constant or a certificate
field restating the final gain. The positive lower bound for BOTH residual
denominators and the original eight-prime product are charged once. -/
theorem residual_parent_gap_budget (S J P R M : ℝ)
    (hP : cutoff ≤ P - S) (hPR : P ≤ R)
    (hM : 0 < M - S) (hJ : cutoff ^ 8 ≤ J) :
    0 ≤ residual S J P M - residual S J R M ∧
    residual S J P M - residual S J R M ≤
      (4 / cutoff ^ 10) * (R - P) := by
  have hp : 0 < P - S := cutoff_pos.trans_le hP
  have hr : 0 < R - S := hp.trans_le (sub_le_sub_right hPR S)
  have hj : 0 < J := (pow_pos cutoff_pos 8).trans_le hJ
  have htwice : cutoff * cutoff ≤ (P - S) * (R - S) :=
    mul_le_mul hP (hP.trans (sub_le_sub_right hPR S)) cutoff_pos.le hp.le
  have hden : cutoff ^ 10 ≤ (P - S) * (R - S) * J := by
    calc
      cutoff ^ 10 = (cutoff * cutoff) * cutoff ^ 8 := by ring
      _ ≤ ((P - S) * (R - S)) * J :=
        mul_le_mul htwice hJ (pow_nonneg cutoff_pos.le 8) (mul_pos hp hr).le
  have hdenpos : 0 < (P - S) * (R - S) * J :=
    mul_pos (mul_pos hp hr) hj
  rw [residual_parent_gap_exact S J P R M hp hr hM hj]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hPR)) hdenpos.le
  · calc
      4 * (R - P) / ((P - S) * (R - S) * J) ≤
          4 * (R - P) / cutoff ^ 10 := by
        apply (div_le_div_iff₀ hdenpos (pow_pos cutoff_pos 10)).mpr
        exact mul_le_mul_of_nonneg_left hden (by positivity)
      _ = (4 / cutoff ^ 10) * (R - P) := by ring

/-- The actual parent is the ORIGINAL level6Exponent of its own sixth
ancestor, with real fourth/fifth history. Its discrepancy from the comparison
parent admits a pointwise invoice on an actual realized, strictly trimmed
rank-eight prime history. Nothing here assumes such a history exists. -/
theorem realized_parent_gap_budget (r n : ℕ)
    (hn : 4 * width n < width r) (e : ℚ) (q : ℕ)
    (om N : ℝ) (history : List ℕ) (hlen : history.length = 8)
    (c : Cell)
    (ht : primeHistoryLogCoordinates N 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om N history c) :
    let t := primeHistoryLogCoordinates N 8 history
    let P := actualParent n e q om N history
    let R := comparison c t
    let M := (finiteCap n c t : ℝ)
    0 ≤ residual (total t) (product t) P M -
          residual (total t) (product t) R M ∧
      residual (total t) (product t) P M -
          residual (total t) (product t) R M ≤
        (4 / cutoff ^ 10) * (R - P) := by
  dsimp only
  have hs : Source c (primeHistoryLogCoordinates N 8 history) :=
    trim_subset_source c (width_pos r) ht
  have htransport := actual_eighth_kernel_transport r n hn e q om N history hlen c ht hr
  dsimp only at htransport
  obtain ⟨hcut, hmargin, hPR, hRM, _, _⟩ := htransport
  have hp : cutoff ≤ actualParent n e q om N history -
      total (primeHistoryLogCoordinates N 8 history) := by
    linarith
  have hM : 0 < (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ) -
      total (primeHistoryLogCoordinates N 8 history) := by
    linarith
  exact residual_parent_gap_budget _ _ _ _ _ hp hPR hM (source_product_lower hs).1

/-- The old one-sided kernel transport is upgraded to a two-sided
comparison. The LOWER invoice is a single rounded-cap loss; the UPPER
invoice is the true sixth-parent mismatch. These are NOT independently
counted again as signed arithmetic costs or reserve debits. -/
theorem realized_parent_residual_two_sided (r n : ℕ)
    (hn : 4 * width n < width r) (e : ℚ) (q : ℕ)
    (om N : ℝ) (history : List ℕ) (hlen : history.length = 8)
    (c : Cell)
    (ht : primeHistoryLogCoordinates N 8 history ∈ trim c (width r))
    (hr : RealizedHistory e q om N history c) :
    let t := primeHistoryLogCoordinates N 8 history
    let P := actualParent n e q om N history
    let R := comparison c t
    let M := (finiteCap n c t : ℝ)
    kernel c t - roundingConstant * width n ≤
      residual (total t) (product t) P M ∧
    residual (total t) (product t) P M ≤
      kernel c t + (4 / cutoff ^ 10) * (R - P) := by
  dsimp only
  have htransport := actual_eighth_kernel_transport r n hn e q om N history hlen c ht hr
  dsimp only at htransport
  obtain ⟨_, _, _, _, _, hlower⟩ := htransport
  have hgap := (realized_parent_gap_budget r n hn e q om N history hlen c ht hr).2
  have hround := (rounded_kernel_loss r n hn ht).2.1
  change 0 ≤ kernel c (primeHistoryLogCoordinates N 8 history) -
      residual (total (primeHistoryLogCoordinates N 8 history))
        (product (primeHistoryLogCoordinates N 8 history))
        (comparison c (primeHistoryLogCoordinates N 8 history))
        (finiteCap n c (primeHistoryLogCoordinates N 8 history) : ℝ) at hround
  constructor <;> linarith

end
end ImbalancedChen.P4AOriginalFull87ActualParentResidualGap
