-- SOURCEONLY / UNCOMPILED / OPEN30.
-- Proposed module: ImbalancedChen.Certificates.OriginalNodeArraysV1.All40QueryComparisonAPI
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQuery

namespace ImbalancedChen.P0All40QueryComparisonAPI

open OriginalThirdClippedChordSourceOnly
open P0All40PublicQuery

noncomputable section

/-- Two independent concrete queries enclose the difference of the actual
function values. No relation between the query arguments is required. -/
theorem difference_encloses {q r : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hr2 : 2 ≤ r) (hr12 : r ≤ 12) :
    value (queryLo160 q) - value (queryHi160 r) ≤
        actualExtendedThirdLowerFactor (q : ℝ) - actualExtendedThirdLowerFactor (r : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) - actualExtendedThirdLowerFactor (r : ℝ) ≤
        value (queryHi160 q) - value (queryLo160 r) := by
  have hq := compact_query_value_encloses hq2 hq12
  have hr := compact_query_value_encloses hr2 hr12
  constructor <;> linarith [hq.1, hq.2, hr.1, hr.2]

/-- The complete absolute-difference interval from the four real endpoints.
The lower bound is zero for overlapping certified intervals; it becomes
positive precisely when a certified endpoint gap supplies that information. -/
theorem abs_difference_encloses {q r : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hr2 : 2 ≤ r) (hr12 : r ≤ 12) :
    max 0 (max (value (queryLo160 q) - value (queryHi160 r))
      (value (queryLo160 r) - value (queryHi160 q))) ≤
        |actualExtendedThirdLowerFactor (q : ℝ) - actualExtendedThirdLowerFactor (r : ℝ)| ∧
    |actualExtendedThirdLowerFactor (q : ℝ) - actualExtendedThirdLowerFactor (r : ℝ)| ≤
      max (value (queryHi160 q) - value (queryLo160 r))
        (value (queryHi160 r) - value (queryLo160 q)) := by
  have hd := difference_encloses hq2 hq12 hr2 hr12
  constructor
  · apply max_le
    · exact abs_nonneg _
    · apply max_le
      · exact hd.1.trans (le_abs_self _)
      · have hn := neg_le_abs
          (actualExtendedThirdLowerFactor (q : ℝ) - actualExtendedThirdLowerFactor (r : ℝ))
        linarith [hd.2]
  · apply abs_le.mpr
    constructor
    · have hm := le_max_right
        (value (queryHi160 q) - value (queryLo160 r))
        (value (queryHi160 r) - value (queryLo160 q))
      linarith [hd.1]
    · exact hd.2.trans (le_max_left _ _)

/-- Strict separation of the certified endpoints proves strict ordering of
the actual values, even when the rational arguments are in arbitrary order. -/
theorem strict_compare_of_separated {q r : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hr2 : 2 ≤ r) (hr12 : r ≤ 12)
    (hsep : value (queryHi160 q) < value (queryLo160 r)) :
    actualExtendedThirdLowerFactor (q : ℝ) < actualExtendedThirdLowerFactor (r : ℝ) := by
  have hq := compact_query_value_encloses hq2 hq12
  have hr := compact_query_value_encloses hr2 hr12
  exact lt_of_le_of_lt hq.2 (lt_of_lt_of_le hsep hr.1)

/-- The reversed separation uses the same checked endpoint API. -/
theorem strict_compare_of_reverse_separated {q r : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hr2 : 2 ≤ r) (hr12 : r ≤ 12)
    (hsep : value (queryHi160 r) < value (queryLo160 q)) :
    actualExtendedThirdLowerFactor (r : ℝ) < actualExtendedThirdLowerFactor (q : ℝ) := by
  exact strict_compare_of_separated hr2 hr12 hq2 hq12 hsep

/-- Integer endpoint separation is enough; no floating-point comparison
or additional query verification is required by this consumer. -/
theorem strict_compare_of_integer_separated {q r : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hr2 : 2 ≤ r) (hr12 : r ≤ 12)
    (hsep : queryHi160 q < queryLo160 r) :
    actualExtendedThirdLowerFactor (q : ℝ) < actualExtendedThirdLowerFactor (r : ℝ) := by
  apply strict_compare_of_separated hq2 hq12 hr2 hr12
  unfold value
  apply (div_lt_div_iff_of_pos_right (show (0 : ℝ) < (P160 : ℝ) by
    norm_num [P160])).2
  exact_mod_cast hsep

/-- A strict endpoint gap certifies distinct actual values. -/
theorem values_ne_of_separated {q r : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hr2 : 2 ≤ r) (hr12 : r ≤ 12)
    (hsep : value (queryHi160 q) < value (queryLo160 r)) :
    actualExtendedThirdLowerFactor (q : ℝ) ≠ actualExtendedThirdLowerFactor (r : ℝ) := by
  exact ne_of_lt (strict_compare_of_separated hq2 hq12 hr2 hr12 hsep)

end
end ImbalancedChen.P0All40QueryComparisonAPI
