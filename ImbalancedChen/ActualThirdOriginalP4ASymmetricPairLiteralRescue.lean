import ImbalancedChen.ActualThirdOriginalP4ABalancedSymmetricLeaf
import ImbalancedChen.ActualThirdOriginalP4ASymmetricBranchPermutation

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Literal x/y-pair invariance of the original ordinary OLD tree on symmetric
integer endpoints. Only exact integer addition is rearranged. Every rounded
product, reciprocal, division, query, clipping and final UP node is retained.
The imported cost definition applies to every s; its balanced-only theorem
is not used here. No analytic leaf estimate is asserted by this module.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricPairLiteralRescue

noncomputable section
open OriginalThirdBoxMomentsSourceOnly OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedOldWeightSourceOnly
open OriginalThirdSymmetricJensenSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdP4ASymmetricBranchPermutationSourceOnly

/-- V addition has no rounding. This is an integer identity at each endpoint,
not associativity of rounded interval multiplication or division. -/
theorem add_three_swap (u v w : IV) : add (add u v) w = add (add u w) v := by
  cases u
  cases v
  cases w
  simp only [add]
  congr 1 <;> omega

/-- Identical source endpoints force identical width and log calls. -/
theorem ordinaryEx_symmetric_eq (a b c d : ℝ) :
    ordinaryEx (symmetricLeft a c) (symmetricRight b d) 1 =
      ordinaryEx (symmetricLeft a c) (symmetricRight b d) 0 := by
  rfl

/-- Even the two inner rounded scalar products keep interval self on the
left. Only their completed integer sums are exchanged. -/
theorem ordinaryTentOld_swap (s : TentSum) (k : TentSide) (a b c d : ℝ) :
    ordinaryTentOld (swapSum s) k (symmetricLeft a c) (symmetricRight b d) =
      ordinaryTentOld s k (symmetricLeft a c) (symmetricRight b d) := by
  unfold ordinaryTentOld
  rw [oldX_swapSum,oldY_swapSum,oldZ_swapSum,ordinaryEx_symmetric_eq]
  rw [add_three_swap]

theorem literalTentX_swap (s : TentSum) : literalTentX (swapSum s)=literalTentY s := by
  cases s <;> rfl

theorem literalTentY_swap (s : TentSum) : literalTentY (swapSum s)=literalTentX s := by
  cases s <;> rfl

theorem literalTentZ_swap (s : TentSum) : literalTentZ (swapSum s)=literalTentZ s := by
  cases s <;> rfl

/-- Equality is proved before constructing Fraction, at its exact integer
numerator and unchanged denominator. No positivity or desired equality is
assumed, and zero denominators do not invalidate this algebraic identity. -/
theorem literalTentEndpoint_swap (s : TentSum) (k : TentSide) (x z D : ℤ) :
    literalTentEndpoint (swapSum s) k ![x,x,z] D =
      literalTentEndpoint s k ![x,x,z] D := by
  cases k with
  | rise =>
      simp only [literalTentEndpoint,literalTentX_swap,literalTentY_swap,
        literalTentZ_swap,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      apply congrArg (fun n : ℤ => (n:ℚ)/((2*z:ℤ):ℚ))
      ring
  | fall =>
      simp only [literalTentEndpoint,literalTentX_swap,literalTentY_swap,
        literalTentZ_swap,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      apply congrArg (fun n : ℤ => (n:ℚ)/((64*z:ℤ):ℚ))
      ring

theorem savedTentLow_swap (s : TentSum) (k : TentSide) (x z : ℤ) :
    savedTentLow (swapSum s) k x z=savedTentLow s k x z := by
  exact literalTentEndpoint_swap s k x z _

theorem savedTentHigh_swap (s : TentSum) (k : TentSide) (x z : ℤ) :
    savedTentHigh (swapSum s) k x z=savedTentHigh s k x z := by
  exact literalTentEndpoint_swap s k x z _

/-- Canonical Fraction numerator and denominator, hence the literal reader
ABI, are equal; equality of real-valued query semantics alone is not used. -/
theorem saved_endpoint_query_pairs_swap (s : TentSum) (k : TentSide) (x z : ℤ) :
    ((savedTentLow (swapSum s) k x z).num,(savedTentLow (swapSum s) k x z).den) =
      ((savedTentLow s k x z).num,(savedTentLow s k x z).den) ∧
    ((savedTentHigh (swapSum s) k x z).num,(savedTentHigh (swapSum s) k x z).den) =
      ((savedTentHigh s k x z).num,(savedTentHigh s k x z).den) := by
  rw [savedTentLow_swap,savedTentHigh_swap]
  exact ⟨rfl,rfl⟩

theorem saved_same_reader_queries_swap (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) :
    readQueryLo160 (assembledRead table.blocks)
        (savedTentLow (swapSum s) k x1 z1).num
        ((savedTentLow (swapSum s) k x1 z1).den:ℤ) =
      readQueryLo160 (assembledRead table.blocks)
        (savedTentLow s k x1 z1).num ((savedTentLow s k x1 z1).den:ℤ) ∧
    readQueryLo160 (assembledRead table.blocks)
        (savedTentHigh (swapSum s) k x0 z0).num
        ((savedTentHigh (swapSum s) k x0 z0).den:ℤ) =
      readQueryLo160 (assembledRead table.blocks)
        (savedTentHigh s k x0 z0).num ((savedTentHigh s k x0 z0).den:ℤ) := by
  rw [savedTentLow_swap,savedTentHigh_swap]
  exact ⟨rfl,rfl⟩

theorem ordinaryTentWeight_swap (s : TentSum) (k : TentSide)
    (a b c d : ℝ) (low high : ℚ) :
    ordinaryTentWeight (swapSum s) k (symmetricLeft a c) (symmetricRight b d) low high =
      ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high := by
  unfold ordinaryTentWeight
  rw [ordinaryTentOld_swap]

/-- The original integer-grid OLD tree, before raw weight and clipping. The
products and outer reciprocal-z multiplication have the producer order. -/
def storedPairOld (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) : IV :=
  let ex := storedGridEx x0 x1 (originalLnUnit ((x1:ℝ)/(x0:ℝ)))
  add (mul (add (add (ofReal (planeConst k)) (mul ex (ofReal (oldX s k))))
    (mul ex (ofReal (oldY s k)))) (storedGridInvZ z0 z1)) (ofReal (oldZ s k))

theorem storedPairOld_swap (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) :
    storedPairOld (swapSum s) k x0 x1 z0 z1=storedPairOld s k x0 x1 z0 z1 := by
  unfold storedPairOld
  rw [oldX_swapSum,oldY_swapSum,oldZ_swapSum,add_three_swap]

/-- The physical readable tree is exactly the original integer-grid tree.
This pays both rational constructor endpoints; it is not just an enclosure. -/
theorem ordinaryTentOld_eq_storedPairOld (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hx0 : 0<x0) (hz0 : 0<z0) (hz1 : 0<z1) :
    ordinaryTentOld s k (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ)) =
      storedPairOld s k x0 x1 z0 z1 := by
  have haR : (a:ℝ)=(x0:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [ha]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hbR : (b:ℝ)=(x1:ℝ)/((48000*2^24:ℤ):ℝ) := by
    rw [hb]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hx0R : (0:ℝ)<(x0:ℝ) := by exact_mod_cast hx0
  have hr : (b:ℝ)/(a:ℝ)=(x1:ℝ)/(x0:ℝ) := by
    rw [haR,hbR]
    exact producer_log_ratio _ _ _ (by norm_num) hx0R.ne'
  have he : ordinaryEx (symmetricLeft (a:ℝ) (c:ℝ))
      (symmetricRight (b:ℝ) (d:ℝ)) 0 =
      storedGridEx x0 x1 (originalLnUnit ((x1:ℝ)/(x0:ℝ))) := by
    change symmetricEx (a:ℝ) (b:ℝ) (originalLnUnit ((b:ℝ)/(a:ℝ))) = _
    rw [stored_grid_ex_eq x0 x1 a b _ ha hb,hr]
  have hz : ofReal (boxEZInv (symmetricLeft (a:ℝ) (c:ℝ))
      (symmetricRight (b:ℝ) (d:ℝ)))=storedGridInvZ z0 z1 := by
    change ofReal (invZMean (c:ℝ) (d:ℝ))=storedGridInvZ z0 z1
    exact stored_grid_invz_eq z0 z1 c d hc hd hz0 hz1
  unfold ordinaryTentOld storedPairOld
  rw [ordinaryEx_symmetric_eq,he,hz]

def storedPairWeight (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) : IV :=
  divRat (sub (storedPairOld s k x0 x1 z0 z1)
    (ofReal (savedTentLow s k x1 z1:ℝ)))
    (savedTentHigh s k x0 z0-savedTentLow s k x1 z1)

theorem storedPairWeight_swap (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) :
    storedPairWeight (swapSum s) k x0 x1 z0 z1=storedPairWeight s k x0 x1 z0 z1 := by
  unfold storedPairWeight
  rw [storedPairOld_swap,savedTentLow_swap,savedTentHigh_swap]

/-- A cost containing only integer endpoint data and the unchanged log
operand; it uses the existing original mass and reader implementations. -/
def storedPairCost (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) : ℤ :=
  let low := savedTentLow s k x1 z1
  let high := savedTentHigh s k x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let out := readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160
  let wt := storedPairWeight s k x0 x1 z0 z1
  literalSymmetricUpper x0 x1 z0 z1 (meanHigh wt.lo wt.hi fl fh out)

theorem storedPairCost_swap (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) :
    storedPairCost table (swapSum s) k x0 x1 z0 z1=
      storedPairCost table s k x0 x1 z0 z1 := by
  unfold storedPairCost
  rw [savedTentLow_swap,savedTentHigh_swap,storedPairWeight_swap]

theorem balancedSymmetricCost_eq_storedPairCost (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hx0 : 0<x0) (hz0 : 0<z0) (hz1 : 0<z1) :
    balancedSymmetricCost table s k x0 x1 z0 z1 a b c d =
      storedPairCost table s k x0 x1 z0 z1 := by
  unfold balancedSymmetricCost storedPairCost ordinaryTentWeight storedPairWeight
  rw [ordinaryTentOld_eq_storedPairOld s k x0 x1 z0 z1 a b c d ha hb hc hd hx0 hz0 hz1]

/-- Full V chord from the original clip, not only its semantic value. -/
def literalClippedChord (wt : IV) (fl fh : ℤ) : IV :=
  add ⟨fl,fl⟩ (mul ⟨clippedLo wt.lo,clippedHi wt.hi⟩ ⟨fh-fl,fh-fl⟩)

theorem literalClippedChord_lo (wt : IV) (fl fh : ℤ) :
    (literalClippedChord wt fl fh).lo=oldChordLo wt.lo wt.hi fl fh := by
  simp [literalClippedChord,add,mul,fourLo,oldChordLo,signedProductLo]

/-- All final integer endpoints are invariant, including signed negative
query differences. No flo<=fhi or query monotonicity is needed. -/
theorem original_OLD_lower_swap (s : TentSum) (k : TentSide)
    (a b c d : ℝ) (low high : ℚ) (fl fh out : ℤ) :
    let u := ordinaryTentWeight (swapSum s) k
      (symmetricLeft a c) (symmetricRight b d) low high
    let v := ordinaryTentWeight s k (symmetricLeft a c) (symmetricRight b d) low high
    literalClippedChord u fl fh=literalClippedChord v fl fh ∧
      oldChordLo u.lo u.hi fl fh=oldChordLo v.lo v.hi fl fh ∧
      meanHigh u.lo u.hi fl fh out=meanHigh v.lo v.hi fl fh out := by
  dsimp only
  rw [ordinaryTentWeight_swap]
  exact ⟨rfl,rfl,rfl⟩

/-- Existing stored candidate cost, including its SAME-reader queries,
original half mass.hi and final signed integer UP, is exactly preserved. -/
theorem balancedSymmetricCost_swap (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    balancedSymmetricCost table (swapSum s) k x0 x1 z0 z1 a b c d =
      balancedSymmetricCost table s k x0 x1 z0 z1 a b c d := by
  unfold balancedSymmetricCost
  rw [savedTentLow_swap,savedTentHigh_swap,ordinaryTentWeight_swap]

/-- In particular the selected source label xz/fall and the safe yz/fall
supplier have the same stored integer cost. Selection is not relabelled. -/
theorem xz_fall_cost_eq_yz_fall (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    balancedSymmetricCost table .xz .fall x0 x1 z0 z1 a b c d =
      balancedSymmetricCost table .yz .fall x0 x1 z0 z1 a b c d := by
  exact (balancedSymmetricCost_swap table .xz .fall x0 x1 z0 z1 a b c d).symm

end
end ImbalancedChen.OriginalThirdP4ASymmetricPairLiteralRescue
