import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40CheckedTable
import ImbalancedChen.Certificates.OriginalNodeArraysV1.All40PublicQuery
import Mathlib.Tactic

/-! SOURCE_ONLY / UNCOMPILED / NOT PASS.
Public quantitative consumer of the concrete immutable All40 checked reader.
The original recurrence, integer rules and normalisation 2^160 are unchanged.
This module supplies a midpoint approximation with a proved radius; it does
not assert numerical smallness of that radius or close the original theorem.
-/
namespace ImbalancedChen.P0ContinuationPublicEntry
noncomputable section
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalU2All40CheckedTable20261024wSourceOnly

/-- Public lower endpoint in the original real normalisation. -/
def queryLower (a b : ℤ) : ℝ :=
  (readQueryLo160 (assembledRead literalBlocks) a b : ℝ) / 2^160

/-- Public upper endpoint in the original real normalisation. -/
def queryUpper (a b : ℤ) : ℝ :=
  (readQueryHi160 (assembledRead literalBlocks) a b : ℝ) / 2^160

def queryMidpoint (a b : ℤ) : ℝ := (queryLower a b + queryUpper a b) / 2

def queryRadius (a b : ℤ) : ℝ := (queryUpper a b - queryLower a b) / 2

theorem query_endpoint_bounds (a b : ℤ)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    queryLower a b ≤ actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) ∧
    actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) ≤ queryUpper a b := by
  exact literalBlocks_compact_query_encloses a b hb ha2 ha12

theorem queryRadius_nonneg (a b : ℤ)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    0 ≤ queryRadius a b := by
  obtain ⟨hl, hu⟩ := query_endpoint_bounds a b hb ha2 ha12
  unfold queryRadius
  linarith

/-- An actual approximation theorem at the finite immutable certificate.
No separately assumed analytic endpoint bound is passed by the caller. -/
theorem queryMidpoint_error (a b : ℤ)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    |actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) - queryMidpoint a b| ≤
      queryRadius a b := by
  obtain ⟨hl, hu⟩ := query_endpoint_bounds a b hb ha2 ha12
  unfold queryMidpoint queryRadius
  apply abs_le.mpr
  constructor <;> linarith

/-- A caller can enlarge the certified radius without opening the table. -/
theorem queryMidpoint_error_le (a b : ℤ) (ε : ℝ)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b)
    (hε : queryRadius a b ≤ ε) :
    |actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) - queryMidpoint a b| ≤ ε := by
  exact (queryMidpoint_error a b hb ha2 ha12).trans hε

/-- Endpoint compatibility with the original finite recurrence. -/
theorem public_endpoints_eq_original (a b : ℤ) :
    queryLower a b = (literalQueryLo160 a b : ℝ)/2^160 ∧
    queryUpper a b = (literalQueryHi160 a b : ℝ)/2^160 := by
  obtain ⟨hl, hu⟩ := literalBlocks_query_eq_original a b
  constructor
  · unfold queryLower
    rw [hl]
  · unfold queryUpper
    rw [hu]

/-- Rational callers discharge the original integer domain conditions by
canonical_integer_bounds from the concrete public query adapter. -/
theorem queryMidpoint_error_rational {q : ℚ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    |actualExtendedThirdLowerFactor (q : ℝ) - queryMidpoint q.num (q.den : ℤ)| ≤
      queryRadius q.num (q.den : ℤ) := by
  have hb := P0All40PublicQuery.canonical_integer_bounds hq2 hq12
  have hqR : (q.num : ℝ) / ((q.den : ℤ) : ℝ) = (q : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, Int.cast_natCast] using
      congrArg (fun s : ℚ => (s : ℝ)) q.num_div_den
  have h := queryMidpoint_error q.num (q.den : ℤ) hb.1 hb.2.1 hb.2.2
  simpa only [hqR] using h

/-- The same rational specialization with any enlarged certified tolerance. -/
theorem queryMidpoint_error_rational_le {q : ℚ} (ε : ℝ)
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12)
    (hε : queryRadius q.num (q.den : ℤ) ≤ ε) :
    |actualExtendedThirdLowerFactor (q : ℝ) - queryMidpoint q.num (q.den : ℤ)| ≤ ε := by
  exact (queryMidpoint_error_rational hq2 hq12).trans hε

/-- Exact compatibility with the public stored rational endpoints in the
existing P160/value normalization. -/
theorem queryMidpoint_rational_eq (q : ℚ) :
    queryMidpoint q.num (q.den : ℤ) =
      (OriginalThirdClippedChordSourceOnly.value (P0All40PublicQuery.queryLo160 q) +
       OriginalThirdClippedChordSourceOnly.value (P0All40PublicQuery.queryHi160 q)) / 2 := by
  simp only [queryMidpoint, queryLower, queryUpper,
    P0All40PublicQuery.queryLo160, P0All40PublicQuery.queryHi160,
    OriginalThirdClippedChordSourceOnly.value, OriginalThirdClippedChordSourceOnly.P160,
    Int.cast_pow, Int.cast_ofNat]

end
end ImbalancedChen.P0ContinuationPublicEntry


