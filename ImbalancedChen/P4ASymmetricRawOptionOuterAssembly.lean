import ImbalancedChen.P4ASymmetricFiniteDispatch
import ImbalancedChen.P0SymmetricOuterMinBridge

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
Original BELOW-mu raw mean_upper Option, followed by box's raw min BEFORE its one
mass multiplication and final UP. Identity with the prior charged Option
dispatcher is proved by real branches, never supplied as a premise.
The boundary wrapper suppresses mean_upper before any full-leaf supplier;
the algebraic outer identity needs no full-cell geometry. The above-mu
fixed-C(x) mean branch has its separate existing stored consumer. No claim
that the below-mu selector represents that different branch is made here.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricRawOptionOuterAssembly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdP4ASymmetricBLeaf OriginalThirdP4ASixTentSymmetricLeaf
open OriginalThirdP4ASymmetricFiniteDispatch
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

/-- Raw B mean_upper, using the SAME s/k-independent B tree and reader as
the actual B stored supplier, before its mass/UP charge. -/
def rawBChordHigh (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let low := savedBLow x1 z1
  let high := savedBHigh x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let wt := symmetricBOldWeight (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ) low high
  meanHigh wt.lo wt.hi fl fh (newOut table x0 x1 z0 z1)

/-- Raw selected six-tent mean_upper, retaining its original s/k and every
rounded interval node. No averaged/relabelled numeric expression is used. -/
def rawTentChordHigh (table : CheckedBlockTable) (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) : ℤ :=
  let low := savedTentLow s k x1 z1
  let high := savedTentHigh s k x0 z0
  let fl := readQueryLo160 (assembledRead table.blocks) low.num (low.den:ℤ)
  let fh := readQueryLo160 (assembledRead table.blocks) high.num (high.den:ℤ)
  let wt := ordinaryTentWeight s k (symmetricLeft (a:ℝ) (c:ℝ))
    (symmetricRight (b:ℝ) (d:ℝ)) low high
  meanHigh wt.lo wt.hi fl fh (newOut table x0 x1 z0 z1)

def rawCandidateChordHigh (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Candidate → ℤ
  | .base => rawBChordHigh table x0 x1 z0 z1 a b c d
  | .tent s k => rawTentChordHigh table s k x0 x1 z0 z1 a b c d

theorem literal_upper_raw_candidate_chord (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (p : Candidate) :
    literalSymmetricUpper x0 x1 z0 z1
        (rawCandidateChordHigh table x0 x1 z0 z1 a b c d p) =
      candidateChordCost table x0 x1 z0 z1 a b c d p := by
  cases p <;> rfl

/-- Exact uncharged source branch order. Rejected candidates produce None,
high<=2 returns raw out, and the equal-endpoint fallback is raw max(0,out-fl).
Clipping and all signed chord arithmetic remain inside the raw chord high. -/
def rawCandidateMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (p : Candidate) : Option ℤ := by
  classical
  exact if candidateBadCoefficients p then none
    else if candidateResidual x1 p then
      if candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p then none
      else if candidateHigh x0 z0 p≤2 then some (newOut table x0 x1 z0 z1)
      else if candidateLow x1 z1 p=candidateHigh x0 z0 p then
        some (max 0 (newOut table x0 x1 z0 z1-
          readQueryLo160 (assembledRead table.blocks)
            (candidateLow x1 z1 p).num ((candidateLow x1 z1 p).den:ℤ)))
      else some (rawCandidateChordHigh table x0 x1 z0 z1 a b c d p)
    else none

/-- Actual ABI equality, by every original branch. It does not need a
geometry, span, source-success or desired output equality hypothesis. -/
theorem rawCandidateMeanOption_map (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (p : Candidate) :
    Option.map (literalSymmetricUpper x0 x1 z0 z1)
        (rawCandidateMeanOption table x0 x1 z0 z1 a b c d p) =
      candidateMeanCost table x0 x1 z0 z1 a b c d p := by
  classical
  unfold rawCandidateMeanOption candidateMeanCost
  split_ifs <;>
    simp only [Option.map_none,Option.map_some,literal_upper_raw_candidate_chord]

def rawMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  match originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => none
  | some p => rawCandidateMeanOption table x0 x1 z0 z1 a b c d p

theorem rawMeanOption_map (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    Option.map (literalSymmetricUpper x0 x1 z0 z1)
        (rawMeanOption table x0 x1 z0 z1 a b c d) =
      symmetricMeanCost table x0 x1 z0 z1 a b c d := by
  unfold rawMeanOption symmetricMeanCost
  cases originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => rfl
  | some p => exact rawCandidateMeanOption_map table x0 x1 z0 z1 a b c d p

/-- Raw mean success receives its actual leaf estimate from the proved
charged dispatcher via the derived map identity. The raw integer itself,
rather than an assumed mass-scaled cost identity, is the data input. -/
theorem rawMeanOption_success_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (j : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) (hratio : x1≤2*x0)
    (hpositive : 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo)
    (hraw : rawMeanOption table x0 x1 z0 z1 a b c d=some j) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (literalSymmetricUpper x0 x1 z0 z1 j) := by
  apply original_symmetric_finite_dispatch_integer_upper table x0 x1 z0 z1
    a b c d (literalSymmetricUpper x0 x1 z0 z1 j)
    ha hb hc hd hg hmu hratio hpositive
  rw [←rawMeanOption_map,hraw]
  rfl

/-- On the true symmetric flag z1<=x0, this is precisely box's full test.
Boundary cells do not call mean_upper, even if its standalone Option exists. -/
def sourceFull (x1 z1 : ℤ) : Prop := x1+x1+3*z1≤T₀

theorem sourceFull_eq_original (x0 x1 z1 : ℤ) (hzy : z1≤x0) :
    sourceFull x1 z1 ↔ ((x1≤x0 ∨ True) ∧ z1≤x0 ∧ x1+x1+3*z1≤T₀) := by
  constructor
  · intro h
    exact ⟨Or.inr trivial,hzy,h⟩
  · rintro ⟨_,_,h⟩
    exact h

def rawBoxMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if sourceFull x1 z1 then rawMeanOption table x0 x1 z0 z1 a b c d else none

def chargedBoxMeanOption (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ := by
  classical
  exact if sourceFull x1 z1 then symmetricMeanCost table x0 x1 z0 z1 a b c d else none

theorem rawBoxMeanOption_map (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) :
    Option.map (literalSymmetricUpper x0 x1 z0 z1)
        (rawBoxMeanOption table x0 x1 z0 z1 a b c d) =
      chargedBoxMeanOption table x0 x1 z0 z1 a b c d := by
  classical
  unfold rawBoxMeanOption chargedBoxMeanOption
  by_cases hf : sourceFull x1 z1
  · rw [if_pos hf,if_pos hf]
    exact rawMeanOption_map table x0 x1 z0 z1 a b c d
  · rw [if_neg hf,if_neg hf]
    rfl

theorem rawBoxMeanOption_boundary (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (hboundary : ¬sourceFull x1 z1) :
    rawBoxMeanOption table x0 x1 z0 z1 a b c d=none := by
  classical
  exact if_neg hboundary

/-- The exact original final box upper: raw min first, one original half
mass and one final UP afterwards. The fallback remains an uncharged high. -/
def sourceBoxUpper (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (fallbackHigh : ℤ) : ℤ :=
  literalSymmetricUpper x0 x1 z0 z1
    (applyOptionalMean fallbackHigh (rawBoxMeanOption table x0 x1 z0 z1 a b c d))

/-- Increasing final UP preserves the raw Option minimum exactly. This
reuses P0's proved integer bridge and our branch-derived Option.map identity.
No mass/UP Option identity or minimum identity is an input. -/
theorem sourceBoxUpper_eq_charged_optional (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (hmass : 0≤(literalSymmetricMass x0 x1 z0 z1).hi) :
    sourceBoxUpper table x0 x1 z0 z1 a b c d fallbackHigh =
      applyOptionalMean (literalSymmetricUpper x0 x1 z0 z1 fallbackHigh)
        (chargedBoxMeanOption table x0 x1 z0 z1 a b c d) := by
  have hbridge := P0SymmetricOuterMinBridge.literal_upper_optional_mean
    x0 x1 z0 z1 fallbackHigh (rawBoxMeanOption table x0 x1 z0 z1 a b c d) hmass
  have hmap := rawBoxMeanOption_map table x0 x1 z0 z1 a b c d
  rw [←hmap]
  unfold sourceBoxUpper
  cases hm : rawBoxMeanOption table x0 x1 z0 z1 a b c d with
  | none =>
      simpa only [hm,Option.map_none,applyOptionalMean] using hbridge
  | some j =>
      simpa only [hm,Option.map_some,applyOptionalMean] using hbridge

/-- Boundary identity has no full-cell hypothesis, query-domain condition,
mean-supplier premise or raw fallback nonnegativity premise. -/
theorem sourceBoxUpper_boundary (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (hboundary : ¬sourceFull x1 z1) :
    sourceBoxUpper table x0 x1 z0 z1 a b c d fallbackHigh =
      literalSymmetricUpper x0 x1 z0 z1 fallbackHigh := by
  rw [sourceBoxUpper,rawBoxMeanOption_boundary table x0 x1 z0 z1 a b c d hboundary]
  rfl

/-- A geometry-bound form obtains the nonnegative mass from the actual
half-mass enclosure internally; sourceBoxUpper itself remains general. -/
theorem sourceBoxUpper_eq_charged_optional_of_full_geometry (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (fallbackHigh : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hratio : (b:ℝ)/(a:ℝ)≤2) :
    sourceBoxUpper table x0 x1 z0 z1 a b c d fallbackHigh =
      applyOptionalMean (literalSymmetricUpper x0 x1 z0 z1 fallbackHigh)
        (chargedBoxMeanOption table x0 x1 z0 z1 a b c d) := by
  exact sourceBoxUpper_eq_charged_optional table x0 x1 z0 z1 a b c d fallbackHigh
    (P0SymmetricOuterMinBridge.literal_mass_hi_nonneg x0 x1 z0 z1 a b c d
      ha hb hc hd hg hratio)

end
end ImbalancedChen.OriginalThirdP4ASymmetricRawOptionOuterAssembly
