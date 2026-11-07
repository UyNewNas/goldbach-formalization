import ImbalancedChen.ActualThirdOriginalP4ASymmetricBLeaf
import ImbalancedChen.P4ASixTentRange32Moments
import ImbalancedChen.P4ASixTentRange32OldWeight
import ImbalancedChen.P4AOriginalRange32MassCeil

/-!
SOURCE_WRITTEN / UNCOMPILED / MAIN OPEN30.
The original B tuple (153,0,0,-96,256) on a symmetric below-mu full box,
through TRUE range32 EX/EY/InvZ/NEW, exact OLD rational queries, original
signed/clipped meanHigh, full-ln32 half mass and final UP. B's two OLD
coefficients are both -1, so its true ordered mean is the producer square
mean, paid by the imported actual symmetric B integral theorem.
No ratio<=2, positive log.lo, query output, mean or leaf bound is a premise.
NEW-only early dispatch is a separate supplier and is not duplicated here.
-/
namespace ImbalancedChen.P4ASymmetricBRange32Leaf

noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly OriginalThirdBelowMuBRoundedSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ASymmetricBLeaf
open OriginalThirdP4ASixTentRange32Moments OriginalThirdP4ASixTentRange32OldWeight
open P4AOriginalRange32MassCeil20261024zSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- Original signed B affine OLD operation tree. The EX/EY intervals stay
on the left of their -1 multipliers, and the two additions stay distinct. -/
def symmetricBOld32 (a b c d : ℝ) : IV :=
  let left := symmetricLeft a c
  let right := symmetricRight b d
  add (mul (add (add (ofReal (153/256))
    (mul (ordinaryEx32 left right) (ofReal (-1))))
    (mul (ordinaryEy32 left right) (ofReal (-1))))
    (ordinaryInvZ32 left right)) (ofReal (-11/8))

theorem symmetricBOld32_source_tree (a b c d : ℝ) :
    symmetricBOld32 a b c d = roundedOld (symmetricLeft a c) (symmetricRight b d)
      (originalLn32 (b/a)) (originalLn32 (b/a)) := by
  rfl

/-- Direct Fraction division, not an interval reciprocal. -/
def symmetricBWeight32 (a b c d : ℝ) (low high : ℚ) : IV :=
  OriginalThirdBelowMuBRoundedSourceOnly.divRat
    (sub (symmetricBOld32 a b c d) (ofReal (low:ℝ))) (high-low)

theorem symmetric_BOld32_encloses (x0 x1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    Encloses (symmetricBOld32 (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
      (bOldMean (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))) := by
  have hl := symmetric_log32_enclosure_and_guard x0 x1 a b c d ha hb hg hmu
  rw [symmetricBOld32_source_tree]
  exact roundedOld_encloses hl.1 hl.1 hl.2 hl.2

theorem symmetric_BWeight32_encloses
    (x0 x1 : ℤ) (a b c d : ℚ) (low high : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hlow : (low:ℝ)=bOldLow (symmetricRight (b:ℝ) (d:ℝ)))
    (hhigh : (high:ℝ)=bOldHigh (symmetricLeft (a:ℝ) (c:ℝ))) :
    Encloses (symmetricBWeight32 (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) low high)
      ((bOldMean (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))-
        bOldLow (symmetricRight (b:ℝ) (d:ℝ)))/
       (bOldHigh (symmetricLeft (a:ℝ) (c:ℝ))-
        bOldLow (symmetricRight (b:ℝ) (d:ℝ)))) := by
  have hm := symmetric_BOld32_encloses x0 x1 a b c d ha hb hg hmu
  have hq : (0:ℚ)<high-low := by
    have hr : (0:ℝ)<((high-low:ℚ):ℝ) := by
      simpa only [Rat.cast_sub,hlow,hhigh] using sub_pos.mpr (symmetric_B_old_span hg hmu)
    exact_mod_cast hr
  simpa only [symmetricBWeight32,Rat.cast_sub,hlow,hhigh] using
    OriginalThirdBelowMuBRoundedSourceOnly.divRat_sound
      (sub_sound hm (ofReal_sound (low:ℝ))) hq

/-- Original signed, clipped mean_upper integer before mass multiplication.
OLD uses its exact B Fractions; NEW is the unreduced true NEW32.hi/P160
call, all through the one checked stored reader. -/
def symmetricBMeanHigh32 (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let low := savedBLow x1 z1
  let high := savedBHigh x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks)
    (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))).hi P160
  let wt := symmetricBWeight32 (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) low high
  meanHigh wt.lo wt.hi fl fh out

def symmetricBRange32Cost (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  up (symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d *
    (symmetricMass32 x0 x1 z0 z1).hi) P160

theorem symmetricBMeanHigh32_value_nonneg (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    0 ≤ value (symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d) := by
  unfold symmetricBMeanHigh32
  rw [meanHigh,value_max,value_zero]
  exact le_max_left _ _

/-- Complete B32 strict-chord mean bound. Actual ordered cap minorant,
range, span and affine OLD mean come from the true symmetric B supplier.
The interval operations and the NEW query here all use full ln32. -/
theorem original_symmetric_B_range32_mean_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hlow : (2:ℚ)≤savedBLow x1 z1) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤
      prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) *
        value (symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d) := by
  have he := saved_B_endpoints_eq x0 x1 z0 z1 a b c d ha hb hc hd hg
  have hspan := symmetric_B_old_span hg hmu
  have hr := symmetric_B_old_mean_mem_range hg hmu
  let low := savedBLow x1 z1
  let high := savedBHigh x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks)
    (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))).hi P160
  let wt := symmetricBWeight32 (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) low high
  have hw := symmetric_BWeight32_encloses x0 x1 a b c d low high ha hb hg hmu he.1 he.2
  have hw0 : 0 ≤ (bOldMean (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))-
      bOldLow (symmetricRight (b:ℝ) (d:ℝ)))/
      (bOldHigh (symmetricLeft (a:ℝ) (c:ℝ))-bOldLow (symmetricRight (b:ℝ) (d:ℝ))) :=
    div_nonneg (sub_nonneg.mpr hr.1) (sub_pos.mpr hspan).le
  have hw1 : (bOldMean (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))-
      bOldLow (symmetricRight (b:ℝ) (d:ℝ)))/
      (bOldHigh (symmetricLeft (a:ℝ) (c:ℝ))-bOldLow (symmetricRight (b:ℝ) (d:ℝ))) ≤ 1 :=
    (div_le_one (sub_pos.mpr hspan)).mpr (by linarith [hr.2])
  have hround := meanHigh_sound (fl:=fl) (fh:=fh) (out:=out) hw0 hw1 hw.1 hw.2
  have hfl : value fl ≤ actualExtendedThirdLowerFactor
      (bOldLow (symmetricRight (b:ℝ) (d:ℝ))) := by
    rw [← he.1]
    exact (stored_rat_query_encloses table low).1
  have hfh : value fh ≤ actualExtendedThirdLowerFactor
      (bOldHigh (symmetricLeft (a:ℝ) (c:ℝ))) := by
    rw [← he.2]
    exact (stored_rat_query_encloses table high).1
  have hl := symmetric_log32_enclosure_and_guard x0 x1 a b c d ha hb hg hmu
  have hn := ordinaryNew32_symmetric_encloses hl.1 hl.1 hl.2 hl.2
  have hq := (CheckedBlockTable.query_encloses_all table
    (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))).hi
    P160 P160_pos).2
  have hout : actualExtendedThirdLowerFactor (newMean (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)) ≤ value out := by
    have hquery : actualExtendedThirdLowerFactor
        (value (ordinaryNew32 (symmetricLeft (a:ℝ) (c:ℝ))
          (symmetricRight (b:ℝ) (d:ℝ))).hi) ≤ value out := by
      simpa only [out,value,P160,Int.cast_pow,Int.cast_ofNat] using hq
    exact (monotone_actualExtendedThirdLowerFactor hn.2).trans hquery
  have hloR : (2:ℝ) ≤ bOldLow (symmetricRight (b:ℝ) (d:ℝ)) := by
    rw [← he.1]
    exact_mod_cast hlow
  have hleaf := symmetric_B_exact_leaf_upper hg hmu hloR hfl hfh hout
  have hchord : max 0 (value out-bOldChord (symmetricLeft (a:ℝ) (c:ℝ))
      (symmetricRight (b:ℝ) (d:ℝ)) (value fl) (value fh)) ≤
      value (meanHigh wt.lo wt.hi fl fh out) := by
    simpa only [bOldChord] using hround
  exact hleaf.trans (mul_le_mul_of_nonneg_left hchord (symmetric_prism_mass_pos hg).le)

/-- Full original B symmetric range32 leaf. All SAME-reader queries,
rounding, signed clipping, exactly one half mass and final UP are internal.
Only original source geometry/bindings and low>=2 remain caller premises. -/
theorem original_symmetric_B_range32_stored_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hlow : (2:ℚ)≤savedBLow x1 z1) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t) ≤
      value (symmetricBRange32Cost table x0 x1 z0 z1 a b c d) := by
  have hleaf := original_symmetric_B_range32_mean_upper table x0 x1 z0 z1
    a b c d ha hb hc hd hg hmu hlow
  have hmass := (symmetric_mass32_encloses x0 x1 z0 z1 a b c d ha hb hc hd hg
    (symmetric_ratio_le_32 hg hmu)).2
  have hnonneg := symmetricBMeanHigh32_value_nonneg table x0 x1 z0 z1 a b c d
  calc
    _ ≤ prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ)*
        value (symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d) := hleaf
    _ ≤ value (symmetricMass32 x0 x1 z0 z1).hi *
        value (symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d) :=
      mul_le_mul_of_nonneg_right hmass hnonneg
    _ = value (symmetricBMeanHigh32 table x0 x1 z0 z1 a b c d)*
        value (symmetricMass32 x0 x1 z0 z1).hi := mul_comm _ _
    _ ≤ value (symmetricBRange32Cost table x0 x1 z0 z1 a b c d) :=
      literal_product_UP_ge _ _

end
end ImbalancedChen.P4ASymmetricBRange32Leaf
