import ImbalancedChen.P4ARange32IntegerOuterABI
import ImbalancedChen.P4AOriginalExecutableLog32

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Bind the genuine original positive256 integer/rational logarithm to the
integer outer reader. P2 supplies its complete unconditional operation-tree
identity. This module therefore has no open primitive log ABI premise.
Original full K, the stored tree certificate and formal acceptance remain OPEN.
-/

namespace ImbalancedChen.P4ARange32ExecutableReaderABI

open OriginalThirdRoundedNewSourceOnly OriginalThirdPositiveLogSourceOnly
open P4ARange32IntegerOuterABI
open OriginalThirdP4ASixTentRange32Moments
open OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdP4AOrdinarySixTentRange32Leaf
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

/-- Integer denominator then numerator, with the actual positive256 backend. -/
def integerLog32 (u v : ℤ) : IV :=
  P4AOriginalExecutableLog32SourceOnly.ln32 ((v:ℚ)/(u:ℚ))

theorem integerLog32_eq_original (u v : ℤ) :
    integerLog32 u v=originalLn32 ((v:ℝ)/(u:ℝ)) := by
  simpa only [integerLog32,Rat.cast_div,Rat.cast_intCast] using
    P4AOriginalExecutableLog32SourceOnly.ln32_eq_original ((v:ℚ)/(u:ℚ))

theorem integerLog32_ABI : Log32ABI integerLog32 := by
  intro u v _ _ _
  exact integerLog32_eq_original u v

/-- Concrete ordinary outer program with all original ln32 calls supplied. -/
def ordinaryReaderCost (readLo readHi : ℤ → ℤ → ℤ) (s : TentSum) (k : TentSide)
    (lo hi : Fin 3 → ℤ) : ℤ :=
  ordinaryCost integerLog32 readLo readHi s k lo hi

/-- Concrete symmetric outer program, including exactly one half-mass step. -/
def symmetricReaderCost (readLo readHi : ℤ → ℤ → ℤ) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) : ℤ :=
  symmetricCost integerLog32 readLo readHi s k x0 x1 z0 z1

theorem ordinaryReaderCost_eq_original (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i,a i=(lo i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,b i=(hi i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤lo i) (hwidth : ∀ i,lo i<hi i) :
    ordinaryReaderCost (readQueryLo160 (assembledRead table.blocks))
      (readQueryHi160 (assembledRead table.blocks)) s k lo hi=
        ordinaryCost32 table s k lo hi a b := by
  exact ordinaryCost_eq_original integerLog32 table s k lo hi a b haBind hbBind hH hwidth
    (fun i => integerLog32_eq_original (lo i) (hi i))

theorem symmetricReaderCost_eq_original (table : CheckedBlockTable)
    (s : TentSum) (k : TentSide) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (haBind : ∀ i,(![a,a,c]) i=((![x0,x0,z0]) i:ℚ)/(sourceD:ℚ))
    (hbBind : ∀ i,(![b,b,d]) i=((![x1,x1,z1]) i:ℚ)/(sourceD:ℚ))
    (hH : ∀ i,sourceH≤(![x0,x0,z0]) i)
    (hwidth : ∀ i,(![x0,x0,z0]) i<(![x1,x1,z1]) i) :
    symmetricReaderCost (readQueryLo160 (assembledRead table.blocks))
      (readQueryHi160 (assembledRead table.blocks)) s k x0 x1 z0 z1=
        P4ASymmetricSixTentRange32Leaf.symmetricSixTentRange32Cost table s k
          x0 x1 z0 z1 a b c d := by
  exact symmetricCost_eq_original integerLog32 table s k x0 x1 z0 z1 a b c d
    haBind hbBind hH hwidth (fun i => integerLog32_eq_original _ _)

end ImbalancedChen.P4ARange32ExecutableReaderABI
