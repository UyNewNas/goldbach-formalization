import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup

/-! SOURCEONLY / UNCOMPILED / OPEN30.
Additive all-branch soundness for the ORIGINAL stored integer query.
The zero clamp includes negative numerators. The terminal branch uses
Llo(12*n) for the lower endpoint and Hhi(12*n) for the upper endpoint,
exactly as IndependentSieve.at; it is NOT extrapolated Lhi.
No range gate, target query bound, saved output or new analytic hypothesis
is supplied. The all-40 same-reader CheckedBlockTable remains explicit.
No concrete table, saved leaf, elaboration or kernel result is claimed. -/

namespace ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly
noncomputable section
open Set
open OriginalU2CoupledRecurrenceSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly

/-- Both literal signed divisions by 12 are outward for arbitrary integers.
This is the same floor/ceiling rule as the original query, at P112. -/
theorem terminal_division_node_rounding (lo hi : ℤ) :
    nodeValue (lo/12) ≤ nodeValue lo/12 ∧
      nodeValue hi/12 ≤ nodeValue (-(-hi/12)) := by
  have hp : (0 : ℝ) < (originalWeightP : ℝ) := by
    norm_num [originalWeightP]
  have hloQ := Int.floor_le ((lo : ℚ)/12)
  have hhiQ := Int.le_ceil ((hi : ℚ)/12)
  rw [query_floor_div_literal lo 12 (by norm_num)] at hloQ
  rw [query_ceil_div_literal hi 12 (by norm_num)] at hhiQ
  have hloR : ((lo/12 : ℤ) : ℝ) ≤ (lo : ℝ)/12 := by exact_mod_cast hloQ
  have hhiR : (hi : ℝ)/12 ≤ ((-(-hi/12) : ℤ) : ℝ) := by exact_mod_cast hhiQ
  constructor
  · calc
      nodeValue (lo/12) ≤ ((lo : ℝ)/12)/(originalWeightP : ℝ) :=
        div_le_div_of_nonneg_right hloR hp.le
      _ = nodeValue lo/12 := by unfold nodeValue; ring
  · calc
      nodeValue hi/12 = ((hi : ℝ)/12)/(originalWeightP : ℝ) := by
        unfold nodeValue
        ring
      _ ≤ nodeValue (-(-hi/12)) := div_le_div_of_nonneg_right hhiR hp.le

/-- Genuine tail enclosure, derived from the accepted terminal NODE and
the already-defined actual factor order/monotonicity. No tail bound is an
input. The upper comparison deliberately passes through upper s, because
the producer's terminal upper integer is Hhi rather than Lhi. -/
theorem original_terminal_query_112bit_encloses (s : ℝ) (hs : 12 ≤ s) :
    nodeValue ((originalFinalNodes 196608).Llo/12) ≤
      actualExtendedThirdLowerFactor s ∧
    actualExtendedThirdLowerFactor s ≤
      nodeValue (-(-(originalFinalNodes 196608).Hhi/12)) := by
  have hn := originalFinalNodes_enclose_actual 196608 (by norm_num) (by norm_num)
  have hgrid : cellLeft 196608=(12 : ℝ) := by norm_num [cellLeft]
  unfold NodeEncloses at hn
  rw [hgrid] at hn
  have hl : nodeValue (originalFinalNodes 196608).Llo/12 ≤ lower 12 := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ)<12)).2
    simpa only [L, mul_comm] using hn.1.1
  have hh : upper 12 ≤ nodeValue (originalFinalNodes 196608).Hhi/12 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<12)).2
    simpa only [H, mul_comm] using hn.2.2
  have hs2 : 2 ≤ s := by linarith
  have hmono : lower 12 ≤ lower s :=
    lower_monotone (by norm_num : (12 : ℝ) ∈ Ici 2) hs2 hs
  have hanti : upper s ≤ upper 12 :=
    upper_antitone (by norm_num : (12 : ℝ) ∈ Ici 2) hs2 hs
  have hr := terminal_division_node_rounding
    (originalFinalNodes 196608).Llo (originalFinalNodes 196608).Hhi
  constructor
  · exact hr.1.trans (hl.trans (hmono.trans (lower_eq_actual hs2).le))
  · exact (lower_eq_actual hs2).symm.le.trans
      ((lower_le_upper hs2).trans (hanti.trans (hh.trans hr.2)))

/-- Original P112 -> P160 rescaling, with no altered normalization. -/
theorem query160_scale_eq_nodeValue (z : ℤ) :
    ((z*2^48 : ℤ) : ℝ)/2^160=nodeValue z := by
  dsimp [nodeValue]
  push_cast
  norm_num [originalWeightP]
  ring

/-- The ORIGINAL total query has all three branches certified for every
integer numerator and positive denominator. There is no hidden a≥0 gate:
negative numerators reach the producer's exact zero clamp. Every stored
access uses this ONE checked immutable reader, as in compact_query_encloses. -/
theorem CheckedBlockTable.query_encloses_all (T : CheckedBlockTable)
    (a b : ℤ) (hb : 0<b) :
    (readQueryLo160 (assembledRead T.blocks) a b : ℝ)/2^160 ≤
      actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) ∧
    actualExtendedThirdLowerFactor ((a : ℝ)/(b : ℝ)) ≤
      (readQueryHi160 (assembledRead T.blocks) a b : ℝ)/2^160 := by
  have hbR : (0 : ℝ)<(b : ℝ) := by exact_mod_cast hb
  by_cases hc : a≤2*b
  · have hcR : (a : ℝ)≤2*(b : ℝ) := by exact_mod_cast hc
    have harg : (a : ℝ)/(b : ℝ)≤2 := (div_le_iff₀ hbR).2 hcR
    rw [actualExtendedThirdLowerFactor_of_le_two harg]
    simp only [readQueryLo160, readQueryHi160, if_pos hc,
      zero_mul, Int.cast_zero, zero_div, le_refl, and_self]
  · by_cases hf : 12*b<a
    · have hfR : 12*(b : ℝ)<(a : ℝ) := by exact_mod_cast hf
      have harg : 12≤(a : ℝ)/(b : ℝ) := ((lt_div_iff₀ hbR).2 hfR).le
      rw [CheckedBlockTable.read_eq_original T]
      simpa only [readQueryLo160, readQueryHi160, if_neg hc, if_pos hf,
        query160_scale_eq_nodeValue] using
        original_terminal_query_112bit_encloses ((a : ℝ)/(b : ℝ)) harg
    · exact CheckedBlockTable.compact_query_encloses T a b hb
        (by omega) (by omega)

/-- Rational wrapper without compact-domain premises. This uses q's own
positive denominator; no saved decimal or representation equality is assumed. -/
theorem CheckedBlockTable.rational_query_encloses_all (T : CheckedBlockTable)
    (q : ℚ) :
    (readQueryLo160 (assembledRead T.blocks) q.num (q.den : ℤ) : ℝ)/2^160 ≤
      actualExtendedThirdLowerFactor (q : ℝ) ∧
    actualExtendedThirdLowerFactor (q : ℝ) ≤
      (readQueryHi160 (assembledRead T.blocks) q.num (q.den : ℤ) : ℝ)/2^160 := by
  have hd : (0 : ℤ)<(q.den : ℤ) := by exact_mod_cast q.den_pos
  have h := CheckedBlockTable.query_encloses_all T q.num (q.den : ℤ) hd
  have hrat : (q : ℝ)=(q.num : ℝ)/((q.den : ℤ) : ℝ) := by
    simp only [Rat.cast_def, Int.cast_natCast]
  rw [← hrat] at h
  exact h

end
end ImbalancedChen.OriginalU2StoredQueryLookupSourceOnly
