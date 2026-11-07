import ImbalancedChen.ActualThirdOriginalStoredQueryAllBranches
import ImbalancedChen.ActualThirdOriginalFixedpointClippedChord

/-!
SOURCEONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Prospective AllBranches import is the exact source candidate
20261024w-StoredQueryAllBranches-SOURCEONLY.lean.txt; it is not installed here.

Same immutable-reader query separation, with original P160 normalization.
No plateau result is repeated. No table entry or endpoint is changed/evaluated.
For qL=238/33 and qH=61/8, compact branch gates, interval soundness, nonnegative
widths and canonical nonstrict monotonicity are closed below. Strict query
comparison remains conditional on an interval separation, or on an actual
canonical gap exceeding the high query's certified width. Neither quantitative
condition is claimed proved for this witness. The resulting strict chord-loss
API keeps a producer/true-mean deficit explicit and does not validate a leaf.
-/
namespace ImbalancedChen.P4AOriginalStoredQueryStrictComparison20261024zSourceOnly

noncomputable section
open OriginalU2StoredQueryLookupSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalThirdClippedChordSourceOnly

def queryLoInt (T : CheckedBlockTable) (q : ℚ) : ℤ :=
  readQueryLo160 (assembledRead T.blocks) q.num (q.den : ℤ)

def queryHiInt (T : CheckedBlockTable) (q : ℚ) : ℤ :=
  readQueryHi160 (assembledRead T.blocks) q.num (q.den : ℤ)

def queryLo (T : CheckedBlockTable) (q : ℚ) : ℝ := value (queryLoInt T q)
def queryHi (T : CheckedBlockTable) (q : ℚ) : ℝ := value (queryHiInt T q)
def queryWidth (T : CheckedBlockTable) (q : ℚ) : ℝ := queryHi T q - queryLo T q

/-- Certified intervals of the same original reader, valid in all query branches. -/
theorem query_interval_sound (T : CheckedBlockTable) (q : ℚ) :
    queryLo T q ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ queryHi T q := by
  simpa only [queryLo, queryHi, queryLoInt, queryHiInt, value, P160,
    Int.cast_pow, Int.cast_ofNat] using
    CheckedBlockTable.rational_query_encloses_all T q

theorem queryWidth_nonneg (T : CheckedBlockTable) (q : ℚ) :
    0 ≤ queryWidth T q := by
  have h := query_interval_sound T q
  unfold queryWidth
  linarith only [h.1, h.2]

theorem canonical_minus_queryLo_le_width (T : CheckedBlockTable) (q : ℚ) :
    actualExtendedThirdLowerFactor (q : ℝ) - queryLo T q ≤ queryWidth T q := by
  have h := (query_interval_sound T q).2
  unfold queryWidth
  linarith only [h]

theorem value_strict_mono {i j : ℤ} (h : i < j) : value i < value j := by
  apply (div_lt_div_iff_of_pos_right P160_real_pos).2
  exact_mod_cast h

theorem value_lt_implies_int_lt {i j : ℤ} (h : value i < value j) : i < j := by
  by_contra hn
  have hh : value j ≤ value i := value_mono (le_of_not_gt hn)
  exact (not_le_of_gt h) hh

/-- Disjoint certified intervals prove strict order of both stored lower
integers. The separation is a checkable reader condition, not an assumed order
between those lower integers. The canonical factors are strictly ordered too. -/
theorem lower_queries_strict_of_interval_separation
    (T : CheckedBlockTable) (qL qH : ℚ)
    (hsep : queryHi T qL < queryLo T qH) :
    queryLoInt T qL < queryLoInt T qH ∧
      actualExtendedThirdLowerFactor (qL : ℝ) <
        actualExtendedThirdLowerFactor (qH : ℝ) := by
  have hL := query_interval_sound T qL
  have hH := query_interval_sound T qH
  have hlow : queryLo T qL < queryLo T qH := by
    linarith only [hL.1, hL.2, hsep]
  refine ⟨value_lt_implies_int_lt hlow, ?_⟩
  linarith only [hL.2, hsep, hH.1]

/-- Analytic alternative: a strict canonical increase surviving the high
query's entire outward interval width forces the stored lower-query increase.
No true gap or error budget is silently supplied by monotonicity alone. -/
theorem lower_queries_strict_of_canonical_gap_gt_width
    (T : CheckedBlockTable) (qL qH : ℚ)
    (hgap : queryWidth T qH <
      actualExtendedThirdLowerFactor (qH : ℝ) -
        actualExtendedThirdLowerFactor (qL : ℝ)) :
    queryLoInt T qL < queryLoInt T qH := by
  have hL := (query_interval_sound T qL).1
  have hH := canonical_minus_queryLo_le_width T qH
  have hlow : queryLo T qL < queryLo T qH := by
    linarith only [hL, hH, hgap]
  exact value_lt_implies_int_lt hlow

/-- The two independently meaningful quantitative inputs can be provided by
a canonical-factor lemma and a stored-width certificate, respectively. -/
theorem lower_queries_strict_of_gap_and_error_certificates
    (T : CheckedBlockTable) (qL qH : ℚ) (gap error : ℝ)
    (hcanonical : gap ≤ actualExtendedThirdLowerFactor (qH : ℝ) -
      actualExtendedThirdLowerFactor (qL : ℝ))
    (hwidth : queryWidth T qH ≤ error) (hsmall : error < gap) :
    queryLoInt T qL < queryLoInt T qH := by
  apply lower_queries_strict_of_canonical_gap_gt_width T qL qH
  linarith only [hcanonical, hwidth, hsmall]

def witnessLow : ℚ := 238 / 33
def witnessHigh : ℚ := 61 / 8

theorem witness_compact_branch_gates :
    (2 : ℚ) < witnessLow ∧ witnessLow < witnessHigh ∧ witnessHigh < 12 := by
  norm_num [witnessLow, witnessHigh]

/-- Literal integer if-tests for the displayed reduced rational arguments.
Neither endpoint reaches the lower clamp or terminal extrapolation branch. -/
theorem witness_literal_reader_branch_gates :
    ¬ ((238 : ℤ) ≤ 2 * 33) ∧ ¬ (12 * (33 : ℤ) < 238) ∧
      ¬ ((61 : ℤ) ≤ 2 * 8) ∧ ¬ (12 * (8 : ℤ) < 61) := by
  norm_num

/-- Closed canonical nonstrict order. This does not imply strict stored order. -/
theorem witness_canonical_monotone :
    actualExtendedThirdLowerFactor (witnessLow : ℝ) ≤
      actualExtendedThirdLowerFactor (witnessHigh : ℝ) := by
  apply monotone_actualExtendedThirdLowerFactor
  norm_num [witnessLow, witnessHigh]

theorem witness_intervals_sound (T : CheckedBlockTable) :
    (queryLo T witnessLow ≤ actualExtendedThirdLowerFactor (238 / 33 : ℝ) ∧
      actualExtendedThirdLowerFactor (238 / 33 : ℝ) ≤ queryHi T witnessLow) ∧
    (queryLo T witnessHigh ≤ actualExtendedThirdLowerFactor (61 / 8 : ℝ) ∧
      actualExtendedThirdLowerFactor (61 / 8 : ℝ) ≤ queryHi T witnessHigh) := by
  constructor
  · simpa only [witnessLow, Rat.cast_div, Rat.cast_ofNat] using query_interval_sound T witnessLow
  · simpa only [witnessHigh, Rat.cast_div, Rat.cast_ofNat] using query_interval_sound T witnessHigh

theorem witness_strict_lower_queries_of_gap_gt_width
    (T : CheckedBlockTable)
    (hgap : queryWidth T witnessHigh <
      actualExtendedThirdLowerFactor (61 / 8 : ℝ) -
        actualExtendedThirdLowerFactor (238 / 33 : ℝ)) :
    queryLoInt T witnessLow < queryLoInt T witnessHigh := by
  apply lower_queries_strict_of_canonical_gap_gt_width T witnessLow witnessHigh
  simpa only [witnessLow, witnessHigh, Rat.cast_div, Rat.cast_ofNat] using hgap

/-- Real chord induced by the two literal P160 lower queries. Its mean
argument is left visible so producer and symmetric true means can be compared. -/
def queryChord (T : CheckedBlockTable) (qL qH : ℚ) (mean : ℝ) : ℝ :=
  queryLo T qL + (mean - (qL : ℝ)) / ((qH : ℝ) - (qL : ℝ)) *
    (queryLo T qH - queryLo T qL)

theorem queryChord_exact_mean_difference
    (T : CheckedBlockTable) (qL qH : ℚ) (producer trueMean : ℝ) :
    queryChord T qL qH trueMean - queryChord T qL qH producer =
      (trueMean - producer) / ((qH : ℝ) - (qL : ℝ)) *
        (queryLo T qH - queryLo T qL) := by
  unfold queryChord
  ring

/-- Once strict interval separation is actually certified, a strict negative
producer-mean deficit creates a strict chord deficit. No rounding repair or
saved symmetric-branch validity is inferred from this real identity. -/
theorem queryChord_strict_of_separation_and_mean_deficit
    (T : CheckedBlockTable) (qL qH : ℚ) (producer trueMean : ℝ)
    (hq : qL < qH) (hmean : producer < trueMean)
    (hsep : queryHi T qL < queryLo T qH) :
    queryChord T qL qH producer < queryChord T qL qH trueMean := by
  have hi := (lower_queries_strict_of_interval_separation T qL qH hsep).1
  have hval : queryLo T qL < queryLo T qH := value_strict_mono hi
  have hspan : (0 : ℝ) < (qH : ℝ) - (qL : ℝ) := by exact_mod_cast sub_pos.mpr hq
  have hp : 0 < (trueMean - producer) / ((qH : ℝ) - (qL : ℝ)) *
      (queryLo T qH - queryLo T qL) :=
    mul_pos (div_pos (sub_pos.mpr hmean) hspan) (sub_pos.mpr hval)
  have he := queryChord_exact_mean_difference T qL qH producer trueMean
  linarith only [he, hp]

/-- Concrete witness API with no assumed query comparison. The outstanding
quantitative canonical-gap/width condition remains visible in the statement. -/
theorem witness_queryChord_strict_of_gap_and_mean_deficit
    (T : CheckedBlockTable) (producer trueMean : ℝ)
    (hmean : producer < trueMean)
    (hgap : queryWidth T witnessHigh <
      actualExtendedThirdLowerFactor (61 / 8 : ℝ) -
        actualExtendedThirdLowerFactor (238 / 33 : ℝ)) :
    queryChord T witnessLow witnessHigh producer <
      queryChord T witnessLow witnessHigh trueMean := by
  have hi := witness_strict_lower_queries_of_gap_gt_width T hgap
  have hval : queryLo T witnessLow < queryLo T witnessHigh := value_strict_mono hi
  have hspan : (0 : ℝ) < (witnessHigh : ℝ) - (witnessLow : ℝ) := by
    norm_num [witnessLow, witnessHigh]
  have hp : 0 < (trueMean - producer) /
      ((witnessHigh : ℝ) - (witnessLow : ℝ)) *
        (queryLo T witnessHigh - queryLo T witnessLow) :=
    mul_pos (div_pos (sub_pos.mpr hmean) hspan) (sub_pos.mpr hval)
  have he := queryChord_exact_mean_difference T witnessLow witnessHigh producer trueMean
  linarith only [he, hp]

end
end ImbalancedChen.P4AOriginalStoredQueryStrictComparison20261024zSourceOnly
