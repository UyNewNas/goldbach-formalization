-- SOURCEONLY / UNCOMPILED / OPEN30. No final C closure claim.
-- Proposed module: ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQuery
-- Requires installation/acceptance of All40CheckedTableV2 and its dependencies.
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable
import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup
import ImbalancedChen.ActualThirdOriginalFixedpointClippedChord

namespace ImbalancedChen.P0All40PublicQuery

open OriginalU2StoredNodeBlockDataSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalU2All40CheckedTable20261024wSourceOnly
open OriginalThirdClippedChordSourceOnly

noncomputable section

/-- Canonical rational queries use the existing concrete reader, with no
second table, recurrence, interpolation rule, or enclosure hypothesis. -/
def queryLo160 (q : ℚ) : ℤ :=
  readQueryLo160 (assembledRead literalBlocks) q.num (q.den : ℤ)

def queryHi160 (q : ℚ) : ℤ :=
  readQueryHi160 (assembledRead literalBlocks) q.num (q.den : ℤ)

private theorem canonical_fraction (q : ℚ) :
    (q.num : ℚ) / ((q.den : ℤ) : ℚ) = q := by
  simpa only [Int.cast_natCast] using q.num_div_den

/-- Rational interval hypotheses discharge the actual integer reader API.
Both endpoints are included, as in the original compact query theorem. -/
theorem canonical_integer_bounds {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    (0 : ℤ) < (q.den : ℤ) ∧
      2 * (q.den : ℤ) ≤ q.num ∧ q.num ≤ 12 * (q.den : ℤ) := by
  have hb : (0 : ℤ) < (q.den : ℤ) := by exact_mod_cast q.den_pos
  have hbQ : (0 : ℚ) < ((q.den : ℤ) : ℚ) := by exact_mod_cast hb
  have hl : (2 : ℚ) * ((q.den : ℤ) : ℚ) ≤ (q.num : ℚ) := by
    apply (le_div_iff₀ hbQ).mp
    simpa only [canonical_fraction] using hq2
  have hu : (q.num : ℚ) ≤ (12 : ℚ) * ((q.den : ℤ) : ℚ) := by
    apply (div_le_iff₀ hbQ).mp
    simpa only [canonical_fraction] using hq12
  refine ⟨hb, ?_, ?_⟩
  · exact_mod_cast hl
  · exact_mod_cast hu

/-- The stored rational adapter agrees exactly with the existing public
rational query functions, including all integer rounding and scaling. -/
theorem query_eq_original {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    queryLo160 q = originalQueryLo160 q ∧
      queryHi160 q = originalQueryHi160 q := by
  have hb := canonical_integer_bounds hq2 hq12
  have ha : (0 : ℤ) ≤ q.num := by omega
  have he := original_query_112bit_literal q.num (q.den : ℤ) hb.1 ha
  have he' : originalQueryLo112 q = literalQueryLo112 q.num (q.den : ℤ) ∧
      originalQueryHi112 q = literalQueryHi112 q.num (q.den : ℤ) := by
    simpa only [canonical_fraction] using he
  have hs := literalBlocks_query_eq_original q.num (q.den : ℤ)
  constructor
  · unfold queryLo160
    rw [hs.1]
    simp only [literalQueryLo160, originalQueryLo160, he'.1]
  · unfold queryHi160
    rw [hs.2]
    simp only [literalQueryHi160, originalQueryHi160, he'.2]

/-- Concrete All40 soundness with the rational input used by mean callers. -/
theorem compact_query_encloses {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    (queryLo160 q : ℝ) / 2^160 ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (queryHi160 q : ℝ) / 2^160 := by
  have hb := canonical_integer_bounds hq2 hq12
  have h := literalBlocks_compact_query_encloses q.num (q.den : ℤ)
    hb.1 hb.2.1 hb.2.2
  have hqR : (q.num : ℝ) / ((q.den : ℤ) : ℝ) = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_intCast] using
      congrArg (fun r : ℚ => (r : ℝ)) (canonical_fraction q)
  simpa only [queryLo160, queryHi160, hqR] using h

/-- Exact P160 normalization used by the existing clipped-mean and
ordinary-chord APIs; the denominator is their imported P160 constant. -/
theorem compact_query_value_encloses {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    value (queryLo160 q) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ value (queryHi160 q) := by
  simpa only [value, P160, Int.cast_pow, Int.cast_ofNat] using
    compact_query_encloses hq2 hq12

/-- Supplies hfl/hfh in original_symmetric_clipped_mean_candidate when
its real endpoint is the cast of the caller's rational query. -/
theorem lower_at_rational {q : ℚ} {x : ℝ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hx : x = (q : ℝ)) :
    value (queryLo160 q) ≤ actualExtendedThirdLowerFactor x := by
  rw [hx]
  exact (compact_query_value_encloses hq2 hq12).1

/-- Supplies hquery in original_symmetric_clipped_mean_candidate. -/
theorem upper_at_rational {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    actualExtendedThirdLowerFactor (q : ℝ) ≤ value (queryHi160 q) := by
  exact (compact_query_value_encloses hq2 hq12).2

/-- Public rational names may be retained by callers while their proof is
obtained by transporting the concrete checked-reader theorem. -/
theorem public_compact_query_value_encloses {q : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    value (originalQueryLo160 q) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ value (originalQueryHi160 q) := by
  have h := compact_query_value_encloses hq2 hq12
  have he := query_eq_original hq2 hq12
  rw [he.1, he.2] at h
  exact h

end
end ImbalancedChen.P0All40PublicQuery

