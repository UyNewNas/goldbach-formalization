import ImbalancedChen.P2N48LiteralHighQueryGeometry
import ImbalancedChen.OriginalPairedN48RawQueryFamily

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original raw omega endpoints and the same global array query for BOTH
n48 terms, including every tie pattern.  Integer endpoint extrema prove
the geometry symbolically; no row/data/Omega decision result is assumed.
-/

namespace ImbalancedChen.OriginalPairedN48AllNativeQueryGeometry

noncomputable section
open Set
open LiLiuPrereqBuchstab
open OriginalN48Q112LocalProduct
open OriginalPairedN48OmegaProducerAdapter
open OriginalPairedN48CanonicalArrays
open OriginalPairedN48CanonicalArrayProofProposals
open OriginalPairedN48PreallocatedProducerIdentity
open OriginalPairedN48RawQueryFamily
open P2N48SavedParentRowRecost P2N48ActualSixteenCostRowAttachment
open P2N48TiedParentMassReduction P2N48AllHighBandTiePatterns
open P2N48OriginalQ80DirectedRowSoundness
open P2N48OriginalStrictLogMassAndOmegaPorts
open P2N48LiteralHighQueryGeometry
open P5Z.U11Canonical

private theorem endpoint_extrema (r : SourceRow) :
    20016 ≤ leftEnd r 0 ∧ rightEnd r 0 ≤ 56640 ∧
      20016 ≤ leftEnd r 1 ∧ rightEnd r 1 ≤ 36480 ∧
      20016 ≤ leftEnd r 2 ∧ rightEnd r 2 ≤ 36480 ∧
      20016 ≤ leftEnd r 3 ∧ rightEnd r 3 ≤ 36480 := by
  have hx : r.ix.val ≤ 47 := by omega
  have hy : r.iy.val ≤ 47 := by omega
  have hz : r.iz.val ≤ 47 := by omega
  have hw : r.iw.val ≤ 47 := by omega
  have ht : r.term.val < 2 := r.term.isLt
  by_cases hzero : r.term.val = 0
  · simp [leftEnd, rightEnd, width, highLo, lowLo, hzero] <;> omega
  · have hone : r.term.val = 1 := by omega
    simp [leftEnd, rightEnd, width, highLo, lowLo, hone] <;> omega

/-- Covers the full native n48 coordinate family, not merely term1 or a
particular method-zero sublist.  The literal raw query is not clipped. -/
theorem all_native_raw_query_range (r : SourceRow) :
    (2 : ℚ) ≤ rawQueryLower r ∧ rawQueryLower r ≤ rawQueryUpper r ∧ rawQueryUpper r ≤ 8 := by
  obtain ⟨hl0, hr0, hl1, hr1, hl2, hr2, hl3, hr3⟩ := endpoint_extrema r
  have hR : (0 : ℚ) < (rightEnd r 2 : ℚ) := by exact_mod_cast rightEnd_pos r 2
  have hL : (0 : ℚ) < (leftEnd r 2 : ℚ) := by exact_mod_cast (show 0 < leftEnd r 2 by omega)
  have hLR (j : Fin 4) : leftEnd r j ≤ rightEnd r j := by unfold rightEnd; omega
  have hDen : (leftEnd r 2 : ℚ) ≤ (rightEnd r 2 : ℚ) := by exact_mod_cast hLR 2
  have hsumR : rightEnd r 0 + rightEnd r 1 + 3 * rightEnd r 2 + rightEnd r 3 ≤ 240000 := by omega
  have hsumL : 240000 ≤ leftEnd r 0 + leftEnd r 1 + 9 * leftEnd r 2 + leftEnd r 3 := by omega
  have hsumLR : leftEnd r 0 + leftEnd r 1 + leftEnd r 2 + leftEnd r 3 ≤
      rightEnd r 0 + rightEnd r 1 + rightEnd r 2 + rightEnd r 3 :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (hLR 0) (hLR 1)) (hLR 2)) (hLR 3)
  rw [rawQueryLower_original_integer_formula, rawQueryUpper_original_integer_formula]
  have hA : 2 * (rightEnd r 2 : ℚ) ≤ 240000 -
      (rightEnd r 0 + rightEnd r 1 + rightEnd r 2 + rightEnd r 3 : ℕ) := by
    have h : (rightEnd r 0 : ℚ) + rightEnd r 1 + 3 * rightEnd r 2 + rightEnd r 3 ≤ 240000 :=
      by exact_mod_cast hsumR
    push_cast
    linarith
  have hAB : (240000 : ℚ) - (rightEnd r 0 + rightEnd r 1 + rightEnd r 2 + rightEnd r 3 : ℕ) ≤
      240000 - (leftEnd r 0 + leftEnd r 1 + leftEnd r 2 + leftEnd r 3 : ℕ) := by
    have h : ((leftEnd r 0 + leftEnd r 1 + leftEnd r 2 + leftEnd r 3 : ℕ) : ℚ) ≤
        ((rightEnd r 0 + rightEnd r 1 + rightEnd r 2 + rightEnd r 3 : ℕ) : ℚ) := by exact_mod_cast hsumLR
    linarith
  have hB : (0 : ℚ) ≤ 240000 - (leftEnd r 0 + leftEnd r 1 + leftEnd r 2 + leftEnd r 3 : ℕ) :=
    (show (0 : ℚ) ≤ 2 * (rightEnd r 2 : ℚ) by positivity).trans (hA.trans hAB)
  refine ⟨(le_div_iff₀ hR).2 hA, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right hAB hR.le).trans
      (div_le_div_of_nonneg_left hB hL hDen)
  · apply (div_le_iff₀ hL).2
    have h : (240000 : ℚ) ≤ (leftEnd r 0 : ℚ) + leftEnd r 1 + 9 * leftEnd r 2 + leftEnd r 3 :=
      by exact_mod_cast hsumL
    push_cast
    linarith

/-- Contains the actual original argument for every point of the native
box, hence for its ordered physical parent, in either term. -/
theorem all_native_actual_raw_query_contains (r : SourceRow) {v : LogFour}
    (hv : v ∈ nativeBox r) :
    omegaArgument v ∈ Icc (rawQueryLower r : ℝ) (rawQueryUpper r : ℝ) := by
  have hb := mem_logPrimeBox.mp hv
  have hl : 0 < rowLower r 2 := rowLower_pos r 2
  have hu : 0 < rowUpper r 2 := rowUpper_pos r 2
  have hzl : rowLower r 2 ≤ v 2 := (hb 2).1
  have hzu : v 2 ≤ rowUpper r 2 := (hb 2).2.le
  have hz : 0 < v 2 := hl.trans_le hzl
  let n : ℝ := 1 - (v 0 + v 1 + v 2 + v 3)
  let l : ℝ := 1 - (rowUpper r 0 + rowUpper r 1 + rowUpper r 2 + rowUpper r 3)
  let u : ℝ := 1 - (rowLower r 0 + rowLower r 1 + rowLower r 2 + rowLower r 3)
  have hln : l ≤ n := by
    dsimp [l, n]
    linarith only [(hb 0).2, (hb 1).2, (hb 2).2, (hb 3).2]
  have hnu : n ≤ u := by
    dsimp [n, u]
    linarith only [(hb 0).1, (hb 1).1, (hb 2).1, (hb 3).1]
  have hraw0 : (0 : ℝ) ≤ (rawQueryLower r : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ rawQueryLower r by
      linarith only [(all_native_raw_query_range r).1])
  have hraw0' : 0 ≤ l / rowUpper r 2 := by
    simpa only [rawQueryLower, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
      Rat.cast_add, upperQ_cast, l] using hraw0
  have hl0 : 0 ≤ l := by
    simpa only [zero_mul] using (le_div_iff₀ hu).mp hraw0'
  have hn : 0 ≤ n := hl0.trans hln
  have hu0 : 0 ≤ u := hn.trans hnu
  have hlo : l / rowUpper r 2 ≤ n / v 2 :=
    (div_le_div_of_nonneg_left hl0 hz hzu).trans
      (div_le_div_of_nonneg_right hln hz.le)
  have hhi : n / v 2 ≤ u / rowLower r 2 :=
    (div_le_div_of_nonneg_right hnu hz.le).trans
      (div_le_div_of_nonneg_left hu0 hl hzl)
  simpa only [omegaArgument, rawQueryLower, rawQueryUpper, Rat.cast_div,
    Rat.cast_sub, Rat.cast_one, Rat.cast_add, lowerQ_cast, upperQ_cast, n, l, u] using
    And.intro hlo hhi

def rowCanonicalNumerator (r : SourceRow) : ℤ :=
  rawQueryNumerator canonicalSourceArrays (rawQueryLower r) (rawQueryUpper r)

def rowOriginalNumerator (r : SourceRow) : ℤ :=
  rawQueryNumerator originalFixedFields (rawQueryLower r) (rawQueryUpper r)

def rowOriginalQueryToken (r : SourceRow) : Token :=
  rawQueryToken originalFixedFields (rawQueryLower r) (rawQueryUpper r)

theorem row_original_query_identity (r : SourceRow) : rowOriginalNumerator r = rowCanonicalNumerator r :=
  preallocated_raw_query_identity (rawQueryLower r) (rawQueryUpper r)

/-- All native coordinates and all ties consume the same global original
Omega cell array.  Finite canonical producer proof terms remain unexecuted. -/
theorem all_native_query_upper_proposal (r : SourceRow) {v : LogFour} (hv : v ∈ nativeBox r) :
    buchstab (omegaArgument v) ≤ uniformOmegaUpper (rowOriginalQueryToken r) := by
  have hrange := all_native_raw_query_range r
  have hquery := all_native_actual_raw_query_contains r hv
  unfold rowOriginalQueryToken
  rw [original_fixed_fields_identity]
  exact raw_query_token_upper canonicalSourceArrays canonical_producer_valid_proposal
    (rawQueryLower r) (rawQueryUpper r) hrange.1 hrange.2.1
    (by linarith only [hrange.2.2]) hquery

theorem all_physical_parent_query_upper_proposal (r : SourceRow) {v : LogFour}
    (hv : v ∈ fullParent r) :
    buchstab (omegaArgument v) ≤ uniformOmegaUpper (rowOriginalQueryToken r) :=
  all_native_query_upper_proposal r hv.1

end
end ImbalancedChen.OriginalPairedN48AllNativeQueryGeometry
