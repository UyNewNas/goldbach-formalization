import ImbalancedChen.P4ASymmetricRawOptionOuterAssembly
import ImbalancedChen.P4AOriginalSeedRange32Invariant

/-! SOURCEONLY / UNCOMPILED / OPEN30.
Exact original above-mu fixed-C(x) mean_upper branch, before all-mu assembly.
The B/six finite selector is not used here. Global source bounds discharge
unit log ratio, positive raw log lower endpoint and the fixed-plane residual.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricAboveMuSource

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4ASymmetricFiniteDispatch
open OriginalThirdP4ASymmetricRawOptionOuterAssembly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open P4AOriginalMuSplitInvariantSourceOnly P4AOriginalSeedRange32InvariantSourceOnly
open P4AClosedTreeCoordinatePropagationSourceOnly
open P4ASymmetricNewOnlyLeafSourceOnly

local notation "D₀" => (48000*2^24:ℤ)

/-- The original fixed tuple is (57,-96,0,0,64). -/
def aboveBadCoefficients : Prop := (-96:ℤ)>64 ∨ (0:ℤ)>64
def aboveResidual (x1 : ℤ) : Prop := 0 < 57*D₀-224*x1

def aboveRawChordHigh (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : ℤ :=
  let low := oldLowQ b d
  let high := oldHighQ a c
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let wt := rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ)))
  meanHigh wt.lo wt.hi fl fh (newOut table x0 x1 z0 z1)

def aboveRawMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if aboveBadCoefficients then none
    else if aboveResidual x1 then
      if oldLowQ b d<2 ∧ 2<oldHighQ a c then none
      else if oldHighQ a c≤2 then some (newOut table x0 x1 z0 z1)
      else if oldLowQ b d=oldHighQ a c then
        some (max 0 (newOut table x0 x1 z0 z1-
          readQueryLo160 (assembledRead table.blocks) (oldLowQ b d).num ((oldLowQ b d).den:ℤ)))
      else some (aboveRawChordHigh table x0 x1 z0 z1 a b c d)
    else none

def aboveMeanCost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  Option.map (literalSymmetricUpper x0 x1 z0 z1)
    (aboveRawMeanOption table x0 x1 z0 z1 a b c d)

theorem above_coefficients_pass : ¬aboveBadCoefficients := by
  norm_num [aboveBadCoefficients]

theorem above_raw_chord_cost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) :
    literalSymmetricUpper x0 x1 z0 z1 (aboveRawChordHigh table x0 x1 z0 z1 a b c d) =
      storedSymmetricCost table x0 x1 z0 z1 a b c d := by
  rfl

/-- The original H..R coordinate invariant discharges ALL above-side log
and residual tests; no extra unit-ratio or log-positive premise is retained. -/
theorem above_source_integer_guards (x0 x1 z0 z1 : ℤ)
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (habove : originalMuInteger ≤ x0) :
    x1 ≤ 2*x0 ∧ 0 < (originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo ∧ aboveResidual x1 := by
  have hx : x0 < x1 := by
    simpa only [symmetricRaw, Matrix.cons_val_zero] using (hr 0).2.1
  have hxR : x1 ≤ originalRInteger := by
    simpa only [symmetricRaw, Matrix.cons_val_zero] using (hr 0).2.2
  have hmuI : 25*D₀ ≤ 128*x0 := by
    calc
      25*D₀ = 128*originalMuInteger := original_integer_ranges.2.2.2.2.1.symm
      _ ≤ 128*x0 := mul_le_mul_of_nonneg_left habove (by norm_num)
  have hrhoI : 96*x1 ≤ 19*D₀ := by
    calc
      96*x1 ≤ 96*originalRInteger := mul_le_mul_of_nonneg_left hxR (by norm_num)
      _ = 19*D₀ := original_integer_ranges.2.2.2.2.2
  have hunit : x1 ≤ 2*x0 := hxR.trans (original_integer_ranges.2.2.2.1.trans
    (mul_le_mul_of_nonneg_left habove (by norm_num)))
  have hRres : 224*originalRInteger < 57*D₀ := by norm_num [originalRInteger]
  have hres : aboveResidual x1 := by
    unfold aboveResidual
    have hh := (mul_le_mul_of_nonneg_left hxR (by norm_num : (0:ℤ) ≤ 224)).trans_lt hRres
    omega
  exact ⟨hunit,(original_integer_above_mu_log_guards x0 x1 hx hmuI hrhoI).2.1,hres⟩

theorem above_source_ln32_is_unit (x0 x1 z0 z1 : ℤ)
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (habove : originalMuInteger ≤ x0) :
    originalLn32 ((x1:ℝ)/(x0:ℝ)) = originalLnUnit ((x1:ℝ)/(x0:ℝ)) := by
  have hx0 : 0 < x0 := by
    simpa only [symmetricRaw, Matrix.cons_val_zero] using
      (integerBoxRange_ratio32 _ _ hr 0).1
  have hx0R : (0:ℝ) < (x0:ℝ) := by exact_mod_cast hx0
  apply originalLn32_eq_originalLnUnit_of_le_two
  apply (div_le_iff₀ hx0R).2
  exact_mod_cast (above_source_integer_guards x0 x1 z0 z1 hr habove).1

theorem above_old_span (a b c d : ℚ)
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) :
    oldLow (b:ℝ) (d:ℝ) < oldHigh (a:ℝ) (c:ℝ) := by
  have hcpos : (0:ℝ) < (c:ℝ) := (by norm_num : (0:ℝ) < 1/100).trans_le hg.cutoff
  have hdpos := hcpos.trans hg.width_z
  have hN : (0:ℝ) < 57/64-(7/2)*(b:ℝ) := by
    have hb := hg.upper_rho
    norm_num [thirdPrefixRho] at hb
    linarith
  have hnum : (57/64:ℝ)-(7/2)*(b:ℝ) < 57/64-(7/2)*(a:ℝ) := by
    linarith [hg.width_xy]
  have hfirst := (div_lt_div_iff_of_pos_right hdpos).2 hnum
  have hsecond := div_le_div₀ (hN.trans hnum).le
    (le_refl ((57/64:ℝ)-(7/2)*(a:ℝ))) hcpos hg.width_z.le
  exact sub_lt_sub_right (hfirst.trans_le hsecond) 1

theorem above_old_rational_span (a b c d : ℚ)
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) : oldLowQ b d < oldHighQ a c := by
  have h := above_old_span a b c d hg
  rw [← cast_oldLowQ, ← cast_oldHighQ] at h
  exact_mod_cast h

/-- Above-side success routes early NEW-only or supported actual fixed-C(x)
chord to real existing suppliers. Rejection remains None; equality is proved
unreachable. No factor query, leaf bound or target K premise is accepted. -/
theorem above_raw_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (high : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu ≤ (a:ℝ))
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (habove : originalMuInteger ≤ x0)
    (hhigh : aboveRawMeanOption table x0 x1 z0 z1 a b c d=some high) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤
      value (literalSymmetricUpper x0 x1 z0 z1 high) := by
  classical
  obtain ⟨hunit,hpositive,hres⟩ := above_source_integer_guards x0 x1 z0 z1 hr habove
  unfold aboveRawMeanOption at hhigh
  rw [if_neg above_coefficients_pass, if_pos hres] at hhigh
  by_cases hcross : oldLowQ b d<2 ∧ 2<oldHighQ a c
  · rw [if_pos hcross] at hhigh
    cases hhigh
  · rw [if_neg hcross] at hhigh
    by_cases hearly : oldHighQ a c≤2
    · rw [if_pos hearly] at hhigh
      have he := Option.some.inj hhigh
      rw [← he]
      exact original_stored_symmetric_new_only_same_reader_integer_upper_general table
        x0 x1 z0 z1 a b c d ha hb hc hd hg hunit hpositive
    · rw [if_neg hearly, if_neg (ne_of_lt (above_old_rational_span a b c d hg))] at hhigh
      have hlow : (2:ℚ) ≤ oldLowQ b d := by
        by_contra hn
        exact hcross ⟨lt_of_not_ge hn,lt_of_not_ge hearly⟩
      have hlowR : (2:ℝ) ≤ oldLow (b:ℝ) (d:ℝ) := by
        rw [← cast_oldLowQ]
        exact_mod_cast hlow
      have he := Option.some.inj hhigh
      rw [← he, above_raw_chord_cost]
      exact original_stored_query_symmetric_integer_upper table x0 x1 z0 z1 a b c d
        ha hb hc hd hg hmu hlowR (above_old_span a b c d hg)

theorem above_cost_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu ≤ (a:ℝ))
    (hr : integerBoxRange (symmetricRaw x0 z0) (symmetricRaw x1 z1))
    (habove : originalMuInteger ≤ x0)
    (hcost : aboveMeanCost table x0 x1 z0 z1 a b c d=some cost) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤ value cost := by
  unfold aboveMeanCost at hcost
  cases hs : aboveRawMeanOption table x0 x1 z0 z1 a b c d with
  | none => simp only [hs,Option.map_none] at hcost
  | some high =>
      have he : literalSymmetricUpper x0 x1 z0 z1 high=cost := by
        simpa only [hs,Option.map_some,Option.some.injEq] using hcost
      rw [← he]
      exact above_raw_success_integer_upper table x0 x1 z0 z1 a b c d high
        ha hb hc hd hg hmu hr habove hs

end
end ImbalancedChen.OriginalThirdP4ASymmetricAboveMuSource
