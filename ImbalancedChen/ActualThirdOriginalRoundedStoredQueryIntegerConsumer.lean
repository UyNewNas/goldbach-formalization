import ImbalancedChen.ActualThirdOriginalSymmetricMassCeil
import ImbalancedChen.ActualThirdOriginalStoredNodeQueryLookup
import ImbalancedChen.ActualThirdOriginalStoredQueryAllBranches

/-! SOURCEONLY / HOLD_ELABORATION / OPEN30. Additive proposed module.
One symmetric above-mu, full-box, ALL-QUERY-BRANCH mean_upper consumer.
No concrete CheckedBlockTable or saved leaf is claimed. No compilation run.
The query facts, OLD/NEW enclosures, guards and final integer bound are derived.
The original clamp, compact and terminal query branches are all covered. -/
namespace ImbalancedChen.OriginalThirdRoundedStoredConsumerSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdRoundedOldWeightSourceOnly OriginalThirdSymmetricMassCeilSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- Literal V(F(width,D)) / lx with both original signed endpoints. -/
def storedGridEx (x0 x1 : ℤ) (lx : IV) : IV :=
  divide ⟨(x1-x0)*P160/(48000*2^24:ℤ),
    up ((x1-x0)*P160) (48000*2^24:ℤ)⟩ lx

/-- Literal rational reciprocal-z mean with both original F endpoints. -/
def storedGridInvZ (z0 z1 : ℤ) : IV :=
  ⟨((48000*2^24:ℤ)*(z0+z1))*P160/(2*z0*z1),
    up (((48000*2^24:ℤ)*(z0+z1))*P160) (2*z0*z1)⟩

/-- Original symmetric NEW tree, with the actual integer-ratio log operand. -/
def storedGridNew (x0 x1 z0 z1 : ℤ) : IV :=
  let lx := originalLnUnit ((x1:ℝ)/(x0:ℝ))
  sub (mul (sub (sub (ofReal thirdPrefixTheta) (storedGridEx x0 x1 lx))
    (storedGridEx x0 x1 lx)) (storedGridInvZ z0 z1)) (ofReal 1)

private theorem positive_grid_integer (z : ℤ) (r : ℚ)
    (hr : r=(z:ℚ)/((48000*2^24:ℤ):ℚ)) (hp : (0:ℝ)<(r:ℝ)) : 0<z := by
  have hD : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by norm_num
  have hrR : (r:ℝ)=(z:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hr]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have h := (lt_div_iff₀ hD).mp (by simpa only [hrR] using hp)
  have hz : (0:ℝ)<(z:ℝ) := by simpa only [zero_mul] using h
  exact_mod_cast hz

theorem stored_grid_ex_eq (x0 x1 : ℤ) (a b : ℚ) (lx : IV)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ)) :
    symmetricEx (a:ℝ) (b:ℝ) lx=storedGridEx x0 x1 lx := by
  have hD : (0:ℤ)<48000*2^24 := by norm_num
  have hDr : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by exact_mod_cast hD
  have haR : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hwidth : (b:ℝ)-(a:ℝ)=((x1-x0:ℤ):ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [haR,hbR]
    push_cast
    field_simp [hDr.ne']
    ring
  unfold symmetricEx storedGridEx
  rw [hwidth,ofReal_int_div_source (x1-x0) (48000*2^24:ℤ) hD]

theorem stored_grid_invz_eq (z0 z1 : ℤ) (c d : ℚ)
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hz0 : 0<z0) (hz1 : 0<z1) :
    ofReal (invZMean (c:ℝ) (d:ℝ))=storedGridInvZ z0 z1 := by
  have hD : (0:ℤ)<48000*2^24 := by norm_num
  have hDr : (0:ℝ)<((48000*2^24:ℤ):ℝ) := by exact_mod_cast hD
  have hz0r : (0:ℝ)<(z0:ℝ) := by exact_mod_cast hz0
  have hz1r : (0:ℝ)<(z1:ℝ) := by exact_mod_cast hz1
  have hcR : (c:ℝ)=(z0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hc]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hdR : (d:ℝ)=(z1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hd]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hden : (0:ℤ)<2*z0*z1 := by positivity
  have harg : invZMean (c:ℝ) (d:ℝ)=
      (((48000*2^24:ℤ)*(z0+z1):ℤ):ℝ)/((2*z0*z1:ℤ):ℝ) := by
    rw [hcR,hdR]
    unfold invZMean
    push_cast
    field_simp [hDr.ne',hz0r.ne',hz1r.ne'] <;> ring
  rw [harg]
  exact ofReal_int_div_source ((48000*2^24:ℤ)*(z0+z1)) (2*z0*z1) hden

/-- This equality is used below to transport the saved integer NEW query. -/
theorem stored_grid_new_eq (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hx0 : 0<x0) (hz0 : 0<z0) (hz1 : 0<z1) :
    symmetricNew (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
      (originalLnUnit ((b:ℝ)/(a:ℝ)))=storedGridNew x0 x1 z0 z1 := by
  have haR : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hx0r : (0:ℝ)<(x0:ℝ) := by exact_mod_cast hx0
  have hratio : (b:ℝ)/(a:ℝ)=(x1:ℝ)/(x0:ℝ) := by
    rw [haR,hbR]
    exact producer_log_ratio _ _ _ (by norm_num) hx0r.ne'
  unfold symmetricNew storedGridNew
  simp only [stored_grid_ex_eq x0 x1 a b _ ha hb,
    stored_grid_invz_eq z0 z1 c d hc hd hz0 hz1]
  rw [hratio]

/-- Same-reader original query at every rational argument, including both
noncompact branches; no compact-domain gates remain. -/
theorem stored_rat_query_encloses (T : CheckedBlockTable) (q : ℚ) :
    value (readQueryLo160 (assembledRead T.blocks) q.num (q.den:ℤ))≤
      actualExtendedThirdLowerFactor (q:ℝ) ∧
    actualExtendedThirdLowerFactor (q:ℝ)≤
      value (readQueryHi160 (assembledRead T.blocks) q.num (q.den:ℤ)) := by
  simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using
    CheckedBlockTable.rational_query_encloses_all T q
/-- The literal integer cost for this one original candidate. -/
def storedSymmetricCost (T : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let read := assembledRead T.blocks
  let lo := oldLowQ b d
  let hi := oldHighQ a c
  let fl := readQueryLo160 read lo.num (lo.den:ℤ)
  let fh := readQueryLo160 read hi.num (hi.den:ℤ)
  let out := readQueryHi160 read (storedGridNew x0 x1 z0 z1).hi P160
  let wt := rawWeight a b c d (originalLnUnit ((b:ℝ)/(a:ℝ)))
  literalSymmetricUpper x0 x1 z0 z1 (meanHigh wt.lo wt.hi fl fh out)

/-- Actual saved-reader queries -> OLD/NEW means -> clipped RAW weight ->
original mass.hi -> final UP. No semantic factor-query result, desired mean
enclosure, divisor guard, or target integer/integral bound is a premise.
T remains the honest all-40 same-reader checking obligation. -/
theorem original_stored_query_symmetric_integer_upper
    (T : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : VariableEnvelope.mu≤(a:ℝ))
    (hlo : 2≤oldLow (b:ℝ) (d:ℝ))
    (hspan : oldLow (b:ℝ) (d:ℝ)<oldHigh (a:ℝ) (c:ℝ)) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (storedSymmetricCost T x0 x1 z0 z1 a b c d) := by
  have hp : (0 : ℝ) < (a : ℝ) ∧ (0 : ℝ) < (c : ℝ) := by
    have hcpos : (0 : ℝ) < (c : ℝ) :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/100) hg.cutoff
    exact ⟨hcpos.trans_le (hg.width_z.le.trans hg.z_below_xy), hcpos⟩
  have hx0 := positive_grid_integer x0 a ha hp.1
  have hz0 := positive_grid_integer z0 c hc hp.2
  have hz1 := positive_grid_integer z1 d hd (hp.2.trans hg.width_z)
  have htree := stored_grid_new_eq x0 x1 z0 z1 a b c d ha hb hc hd hx0 hz0 hz1
  have hfl := (stored_rat_query_encloses T (oldLowQ b d)).1
  have hfh := (stored_rat_query_encloses T (oldHighQ a c)).1
  have hq := (CheckedBlockTable.query_encloses_all T
    (storedGridNew x0 x1 z0 z1).hi P160 P160_pos).2
  have harg :
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)=
      ((storedGridNew x0 x1 z0 z1).hi:ℝ)/(P160:ℝ) := by
    simp only [symmetricNewQuery,Rat.cast_div,Rat.cast_intCast,htree]
  have hquery : actualExtendedThirdLowerFactor
      (symmetricNewQuery (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)
        (originalLnUnit ((b:ℝ)/(a:ℝ))):ℝ)≤
      value (readQueryHi160 (assembledRead T.blocks)
        (storedGridNew x0 x1 z0 z1).hi P160) := by
    rw [harg]
    simpa only [value,P160,Int.cast_pow,Int.cast_ofNat] using hq
  have hceil := original_stored_symmetric_leaf_integer_upper
    x0 x1 z0 z1 a b c d
    (readQueryLo160 (assembledRead T.blocks) (oldLowQ b d).num ((oldLowQ b d).den:ℤ))
    (readQueryLo160 (assembledRead T.blocks) (oldHighQ a c).num ((oldHighQ a c).den:ℤ))
    (readQueryHi160 (assembledRead T.blocks) (storedGridNew x0 x1 z0 z1).hi P160)
    ha hb hc hd hg hmu hlo hspan
    (by simpa only [cast_oldLowQ] using hfl)
    (by simpa only [cast_oldHighQ] using hfh) hquery
  simpa only [storedSymmetricCost] using hceil

end
end ImbalancedChen.OriginalThirdRoundedStoredConsumerSourceOnly
