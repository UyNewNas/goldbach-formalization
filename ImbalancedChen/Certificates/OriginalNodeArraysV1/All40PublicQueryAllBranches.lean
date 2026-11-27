import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQuery
import ImbalancedChen.ActualThirdOriginalStoredQueryAllBranches

namespace ImbalancedChen.P0All40PublicQuery

open OriginalU2All40CheckedTable20261024wSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- The concrete 40-block reader encloses the actual factor at every rational query. -/
theorem query_encloses_all (q : ℚ) :
    (queryLo160 q : ℝ) / 2^160 ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (queryHi160 q : ℝ) / 2^160 := by
  simpa only [queryLo160, queryHi160, literalCheckedBlockTable] using
    CheckedBlockTable.rational_query_encloses_all literalCheckedBlockTable q

/-- The concrete reader and the original public query return identical scaled integers. -/
theorem query_eq_original_all (q : ℚ) :
    queryLo160 q = originalQueryLo160 q ∧ queryHi160 q = originalQueryHi160 q := by
  have hb : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hfrac : (q.num : ℚ) / ((q.den : ℤ) : ℚ) = q := by
    simpa only [Int.cast_natCast] using q.num_div_den
  have hclamp : q ≤ 2 ↔ q.num ≤ 2 * (q.den : ℤ) := by
    simpa only [hfrac] using (original_query_clamps_literal q.num (q.den : ℤ) hb).1
  have h112 : originalQueryLo112 q = literalQueryLo112 q.num (q.den : ℤ) ∧
      originalQueryHi112 q = literalQueryHi112 q.num (q.den : ℤ) := by
    by_cases hq : q ≤ 2
    · have ha := hclamp.mp hq
      constructor <;> simp only [originalQueryLo112, originalQueryHi112,
        literalQueryLo112, literalQueryHi112, if_pos hq, if_pos ha]
    · have ha := mt hclamp.mpr hq
      have hnum : 0 ≤ q.num := by omega
      simpa only [hfrac] using original_query_112bit_literal q.num (q.den : ℤ) hb hnum
  have hs := literalBlocks_query_eq_original q.num (q.den : ℤ)
  constructor
  · simpa only [queryLo160, originalQueryLo160, literalQueryLo160, h112.1] using hs.1
  · simpa only [queryHi160, originalQueryHi160, literalQueryHi160, h112.2] using hs.2

/-- All rational inputs to the original public names enclose the actual factor. -/
theorem public_query_encloses_all (q : ℚ) :
    (originalQueryLo160 q : ℝ) / 2^160 ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (originalQueryHi160 q : ℝ) / 2^160 := by
  have he := query_eq_original_all q
  simpa only [he.1, he.2] using query_encloses_all q

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
