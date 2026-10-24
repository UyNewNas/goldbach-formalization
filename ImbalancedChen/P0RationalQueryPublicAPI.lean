import ImbalancedChen.ActualThirdOriginalRationalQuery
import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup
import ImbalancedChen.ActualThirdOriginalRoundedNewOperations
import ImbalancedChen.ActualExtendedThirdOrderedIntegral

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
Public endpoint and interval adapters for the literal original rational query.
The output type is the existing original 160-bit IV; the scale is the existing
P160. Uniform real-argument enclosures follow from the actual factor's proved
monotonicity and the two computed endpoint queries. In particular no monotonicity
of rounded query integers is asserted or required. This module neither builds
the all-40 checked table nor regenerates any node or numerical certificate.
-/

namespace ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly

noncomputable section
open Set
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredNodeCertificateSourceOnly
open OriginalThirdClippedChordSourceOnly
open OriginalThirdRoundedNewSourceOnly

/-- The actual rational query, packaged in the producer's existing IV type. -/
def pointQuery (q : ℚ) : IV :=
  ⟨originalQueryLo160 q, originalQueryHi160 q⟩

/-- The two original integer queries on the actual a/b representation. -/
def literalPointQuery (a b : ℤ) : IV :=
  ⟨literalQueryLo160 a b, literalQueryHi160 a b⟩

theorem pointQuery_sound {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    Encloses (pointQuery q) (actualExtendedThirdLowerFactor (q : ℝ)) := by
  simpa only [Encloses, pointQuery, value, P160, Int.cast_pow, Int.cast_ofNat]
    using original_compact_query_160bit_encloses hq2 hq12

/-- Representation transport keeps both rounds and the exact 2^48 scaling. -/
theorem pointQuery_int_div (a b : ℤ) (hb : 0 < b) (ha : 0 ≤ a) :
    pointQuery ((a : ℚ)/(b : ℚ)) = literalPointQuery a b := by
  have h := original_query_112bit_literal a b hb ha
  simp only [pointQuery, literalPointQuery, originalQueryLo160, originalQueryHi160,
    literalQueryLo160, literalQueryHi160, h.1, h.2]

theorem literalPointQuery_sound (a b : ℤ)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    Encloses (literalPointQuery a b)
      (actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ))) := by
  simpa only [Encloses, literalPointQuery, value, P160, Int.cast_pow, Int.cast_ofNat]
    using literal_compact_query_160bit_encloses a b hb ha2 ha12

/-- Public rational endpoint bounds use the same exact P160 scale. -/
def lowerEndpoint (q : ℚ) : ℚ := ((pointQuery q).lo : ℚ)/(P160 : ℚ)

def upperEndpoint (q : ℚ) : ℚ := ((pointQuery q).hi : ℚ)/(P160 : ℚ)

theorem lowerEndpoint_cast (q : ℚ) :
    (lowerEndpoint q : ℝ) = value (pointQuery q).lo := by
  simp only [lowerEndpoint, value, Rat.cast_div, Rat.cast_intCast]

theorem upperEndpoint_cast (q : ℚ) :
    (upperEndpoint q : ℝ) = value (pointQuery q).hi := by
  simp only [upperEndpoint, value, Rat.cast_div, Rat.cast_intCast]

theorem rational_endpoints_sound {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    (lowerEndpoint q : ℝ) ≤ actualExtendedThirdLowerFactor (q : ℝ) ∧
      actualExtendedThirdLowerFactor (q : ℝ) ≤ (upperEndpoint q : ℝ) := by
  rw [lowerEndpoint_cast, upperEndpoint_cast]
  exact pointQuery_sound hq2 hq12

theorem lowerEndpoint_le_upperEndpoint {q : ℚ} (hq2 : 2 ≤ q) (hq12 : q ≤ 12) :
    lowerEndpoint q ≤ upperEndpoint q := by
  have h := rational_endpoints_sound hq2 hq12
  have hcast : (lowerEndpoint q : ℝ) ≤ (upperEndpoint q : ℝ) := h.1.trans h.2
  exact_mod_cast hcast

/-- A computed lower endpoint is usable at any larger real argument. -/
theorem pointQuery_lower_le_at {q : ℚ} {x : ℝ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hqx : (q : ℝ) ≤ x) :
    value (pointQuery q).lo ≤ actualExtendedThirdLowerFactor x := by
  exact (pointQuery_sound hq2 hq12).1.trans
    (monotone_actualExtendedThirdLowerFactor hqx)

/-- A computed upper endpoint is usable at any smaller real argument. -/
theorem at_le_pointQuery_upper {q : ℚ} {x : ℝ}
    (hq2 : 2 ≤ q) (hq12 : q ≤ 12) (hxq : x ≤ (q : ℝ)) :
    actualExtendedThirdLowerFactor x ≤ value (pointQuery q).hi := by
  exact (monotone_actualExtendedThirdLowerFactor hxq).trans
    (pointQuery_sound hq2 hq12).2

/-- A single usable enclosure for every real argument in a rational interval. -/
def rangeQuery (lo hi : ℚ) : IV := ⟨(pointQuery lo).lo, (pointQuery hi).hi⟩

theorem rangeQuery_sound {lo hi : ℚ}
    (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 12)
    {x : ℝ} (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    Encloses (rangeQuery lo hi) (actualExtendedThirdLowerFactor x) := by
  constructor
  · exact pointQuery_lower_le_at hlo (horder.trans hhi) hx.1
  · exact at_le_pointQuery_upper (hlo.trans horder) hhi hx.2

/-- Restriction reuses the already selected endpoint queries; no new rounding
or query evaluation is introduced at the smaller interval's endpoints. -/
theorem rangeQuery_restrict {lo hi a b : ℚ}
    (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 12)
    (hla : lo ≤ a) (hbh : b ≤ hi)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    Encloses (rangeQuery lo hi) (actualExtendedThirdLowerFactor x) := by
  have hlaR : (lo : ℝ) ≤ (a : ℝ) := by exact_mod_cast hla
  have hbhR : (b : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hbh
  exact rangeQuery_sound hlo horder hhi ⟨hlaR.trans hx.1, hx.2.trans hbhR⟩

/-- Rational endpoint output for consumers whose coefficients live in ℚ. -/
theorem rangeQuery_rational_bounds {lo hi : ℚ}
    (hlo : 2 ≤ lo) (horder : lo ≤ hi) (hhi : hi ≤ 12)
    {x : ℝ} (hx : x ∈ Icc (lo : ℝ) (hi : ℝ)) :
    (lowerEndpoint lo : ℝ) ≤ actualExtendedThirdLowerFactor x ∧
      actualExtendedThirdLowerFactor x ≤ (upperEndpoint hi : ℝ) := by
  rw [lowerEndpoint_cast, upperEndpoint_cast]
  exact rangeQuery_sound hlo horder hhi hx

/-- The checked lookup can expose precisely the same public IV. The concrete
all-40 checked table remains the separate assembly module's responsibility. -/
def storedPointQuery (T : CheckedBlockTable) (a b : ℤ) : IV :=
  ⟨readQueryLo160 (assembledRead T.blocks) a b,
    readQueryHi160 (assembledRead T.blocks) a b⟩

theorem storedPointQuery_eq_literal (T : CheckedBlockTable) (a b : ℤ) :
    storedPointQuery T a b = literalPointQuery a b := by
  have h := CheckedBlockTable.query_eq_original T a b
  simp only [storedPointQuery, literalPointQuery, h.1, h.2]

theorem storedPointQuery_eq_rational (T : CheckedBlockTable) (a b : ℤ)
    (hb : 0 < b) (ha : 0 ≤ a) :
    storedPointQuery T a b = pointQuery ((a : ℚ)/(b : ℚ)) := by
  rw [storedPointQuery_eq_literal, pointQuery_int_div a b hb ha]

theorem storedPointQuery_sound (T : CheckedBlockTable) (a b : ℤ)
    (hb : 0 < b) (ha2 : 2*b ≤ a) (ha12 : a ≤ 12*b) :
    Encloses (storedPointQuery T a b)
      (actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ))) := by
  rw [storedPointQuery_eq_literal]
  exact literalPointQuery_sound a b hb ha2 ha12

end
end ImbalancedChen.OriginalU2RationalQueryPublicAPIP0SourceOnly
