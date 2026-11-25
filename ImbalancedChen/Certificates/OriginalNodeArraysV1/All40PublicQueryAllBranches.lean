import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQuery
import ImbalancedChen.ActualThirdOriginalStoredQueryAllBranches

namespace ImbalancedChen.P0All40PublicQuery

open OriginalU2All40CheckedTable20261024wSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- The concrete 40-block reader encloses the actual factor at every rational query. -/
theorem query_encloses_all (q : ℚ) :
    (queryLo160 q : ℝ) / 2^160 ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (queryHi160 q : ℝ) / 2^160 := by
  simpa only [queryLo160, queryHi160, literalCheckedBlockTable] using
    CheckedBlockTable.rational_query_encloses_all literalCheckedBlockTable q

/-- The same reader accepts the caller's signed numerator and positive denominator. -/
theorem query_integer_encloses_all (a b : ℤ) (hb : 0 < b) :
    (readQueryLo160 (assembledRead literalBlocks) a b : ℝ) / 2^160 ≤
        actualExtendedThirdLowerFactor ((a : ℝ) / (b : ℝ)) ∧
      actualExtendedThirdLowerFactor ((a : ℝ) / (b : ℝ)) ≤
        (readQueryHi160 (assembledRead literalBlocks) a b : ℝ) / 2^160 := by
  simpa only [literalCheckedBlockTable] using
    CheckedBlockTable.query_encloses_all literalCheckedBlockTable a b hb

/-- The two endpoint queries enclose the actual factor throughout the closed interval. -/
theorem query_range_encloses_all {lo hi : ℚ} {x : ℝ} (hx : x ∈ Set.Icc (lo : ℝ) (hi : ℝ)) :
    (queryLo160 lo : ℝ) / 2^160 ≤ actualExtendedThirdLowerFactor x ∧
      actualExtendedThirdLowerFactor x ≤ (queryHi160 hi : ℝ) / 2^160 :=
  ⟨(query_encloses_all lo).1.trans (monotone_actualExtendedThirdLowerFactor hx.1),
    (monotone_actualExtendedThirdLowerFactor hx.2).trans (query_encloses_all hi).2⟩

end ImbalancedChen.P0All40PublicQuery
