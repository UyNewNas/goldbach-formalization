import ImbalancedChen.P4ASixTentRange32OldWeight
import ImbalancedChen.P4AOriginalRange32MassCeil

/-!
# P4A: all six symmetric tent sums through the original range32 integer leaf

The actual paired OLD chord, NEW Jensen, SAME-reader queries, direct rational
weight and signed clipping are supplied by Range32OldWeight. The range32 mass
supplier keeps the two original log calls and exactly one symmetric /2.
The final original UP(high*mass.hi,P160) is then paid by its actual supplier.

All source sums and both sides are quantified as the original TentSum and
TentSide. No ratio<=2, positive log.lo, hquery, mean/weight/clipping bound,
mass bound, whole-leaf bound, integer cost or K estimate is an input.
The original below-mu geometry, selected branch, root, residual and low>=2
guards remain explicit finite input data. No stored tree is modified.

SOURCE ONLY / UNCOMPILED. Draft imports require their documented staging.
-/

namespace ImbalancedChen.P4ASymmetricSixTentRange32Leaf

noncomputable section

open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdTriangleMomentsSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdRoundedOldWeightSourceOnly OriginalThirdPositiveLogSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly OriginalThirdP4ASymmetricTentPrerequisites
open OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdP4ASixTentRange32Moments OriginalThirdP4ASixTentRange32OldWeight
open P4AOriginalRange32MassCeil20261024zSourceOnly

/-- Exact final original integer operation: the SAME-reader signed clipped
mean times the range32 half-mass high endpoint, followed by the original UP. -/
def symmetricSixTentRange32Cost (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  up (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d *
    (symmetricMass32 x0 x1 z0 z1).hi) P160

/-- Literal mass-tree dictionary: full ln32 twice, original rational factor
four, exactly one divNat2, and exactly the final original raw UP. -/
theorem symmetricSixTentRange32Cost_source_tree
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    symmetricSixTentRange32Cost table s k x0 x1 z0 z1 a b c d =
      up (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d *
        (divNat (mul (mul (originalLn32 ((x1:ℝ)/(x0:ℝ)))
          (originalLn32 ((x1:ℝ)/(x0:ℝ))))
          (ofReal (((4*(48000*2^24:ℤ)*(z1-z0):ℤ):ℝ)/
            ((z0*z1:ℤ):ℝ)))) 2).hi) P160 := by
  rw [symmetricSixTentRange32Cost, symmetricMass32_source_tree]

/-- Nonnegativity comes from the original max-zero clipping, even for
negative OLD slopes. Query endpoints need not be artificially reordered. -/
theorem symmetricMeanHigh32_value_nonneg
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    0 ≤ value (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d) := by
  unfold symmetricMeanHigh32
  rw [meanHigh, value_max, value_zero]
  exact le_max_left _ _

/-- Full stored symmetric strict-chord leaf for every original six-tent
sum and either active side. Both the <=32 ratio and q-integer positive
divisor checks are internal actual suppliers. The same table reader is
used for the two OLD queries and the one original range32 NEW query. -/
theorem original_symmetric_six_tent_range32_stored_integer_upper
    (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hb : b=(x1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hc : c=(z0:ℚ)/((48000*2^24:ℤ):ℚ))
    (hd : d=(z1:ℚ)/((48000*2^24:ℤ):ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hbranch : literalSymmetricBranch s k x0 x1 z0 z1)
    (hroot : literalSymmetricRoot s k x0 x1 z0 z1)
    (hres : literalSymmetricResidual s k x1)
    (hlow : (2:ℚ)≤savedTentLow s k x1 z1) :
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ), compactKernel t) ≤
      value (symmetricSixTentRange32Cost table s k x0 x1 z0 z1 a b c d) := by
  have hLeaf := original_symmetric_tent_range32_mean_upper table s k x0 x1 z0 z1
    a b c d ha hb hc hd hg hmu hbranch hroot hres hlow
  have hRatio32 : (b:ℝ)/(a:ℝ)≤32 := symmetric_ratio_le_32 hg hmu
  have hMass := (symmetric_mass32_encloses x0 x1 z0 z1 a b c d
    ha hb hc hd hg hRatio32).2
  have hNonneg := symmetricMeanHigh32_value_nonneg table s k x0 x1 z0 z1 a b c d
  calc
    (∫ t in compactRegion ∩ symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ), compactKernel t) ≤
        prismMass (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) *
          value (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d) := hLeaf
    _ ≤ value (symmetricMass32 x0 x1 z0 z1).hi *
        value (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d) :=
      mul_le_mul_of_nonneg_right hMass hNonneg
    _ = value (symmetricMeanHigh32 table s k x0 x1 z0 z1 a b c d) *
        value (symmetricMass32 x0 x1 z0 z1).hi := mul_comm _ _
    _ ≤ value (symmetricSixTentRange32Cost table s k x0 x1 z0 z1 a b c d) :=
      literal_product_UP_ge _ _

end
end ImbalancedChen.P4ASymmetricSixTentRange32Leaf
