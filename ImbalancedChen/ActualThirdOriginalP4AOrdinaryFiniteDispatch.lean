import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
import ImbalancedChen.ActualThirdOriginalP4AOrdinaryBCandidateLeaf

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The second import is the sibling ordinary_saved_leaf/OrdinaryBCandidateLeaf.lean
draft. This module gives one finite selection theorem for the true original
B-or-six-tent winner. All query expressions and rounded operations are explicit.
Usable below is only the post-selection scalar residual/OLD-domain test; it
contains no integral bound, K bound, selected maximum assertion, or saved cost.

The enclosing box() fallback minimum still needs the independent fallback
suppliers. The optional-mean arithmetic is in FiniteSelector; no fallback bound
is smuggled in here as a target hypothesis.
-/
namespace ImbalancedChen.OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdSixTentOrdinaryMassCeilSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4AOrdinaryBCandidateSourceOnly
open OriginalThirdBelowMuBCandidateSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

abbrev realBox := OriginalThirdBelowMuBRoundedSourceOnly.realBox

def tentHigh (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) (s : TentSum) (k : TentSide) : ℤ :=
  meanHigh
    (ordinaryTentWeight s k (realBox a) (realBox b)
      (literalTentEndpoint s k hi D₀) (literalTentEndpoint s k lo D₀)).lo
    (ordinaryTentWeight s k (realBox a) (realBox b)
      (literalTentEndpoint s k hi D₀) (literalTentEndpoint s k lo D₀)).hi
    (readQueryLo160 (assembledRead table.blocks)
      (literalTentEndpoint s k hi D₀).num ((literalTentEndpoint s k hi D₀).den:ℤ))
    (readQueryLo160 (assembledRead table.blocks)
      (literalTentEndpoint s k lo D₀).num ((literalTentEndpoint s k lo D₀).den:ℤ))
    (readQueryHi160 (assembledRead table.blocks) (ordinaryNew (realBox a) (realBox b)).hi P160)

def baseHigh (table : CheckedBlockTable) (a b : Fin 3 → ℚ) : ℤ :=
  meanHigh
    (OriginalThirdBelowMuBRoundedSourceOnly.rawWeight a b
      (originalLn32 (realBox b 0/realBox a 0))
      (originalLn32 (realBox b 1/realBox a 1))).lo
    (OriginalThirdBelowMuBRoundedSourceOnly.rawWeight a b
      (originalLn32 (realBox b 0/realBox a 0))
      (originalLn32 (realBox b 1/realBox a 1))).hi
    (bStoredFl table b) (bStoredFh table a) (bStoredOut table a b)

def candidateIntegerUpper (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ)
    (a b : Fin 3 → ℚ) : Candidate → ℤ
  | .base => OriginalThirdBelowMuBMassCeilSourceOnly.literalOrdinaryUpper lo hi
      (baseHigh table a b)
  | .tent s k => OriginalThirdSixTentOrdinaryMassCeilSourceOnly.literalOrdinaryUpper lo hi
      (tentHigh table lo hi a b s k)

/-- These guards are evaluated AFTER originalMinorant; they do not modify
the source candidate list or replace an unusable winner with a later plane. -/
def usableCandidate (hi : Fin 3 → ℤ) (b : Fin 3 → ℚ) : Candidate → Prop
  | .base => 2≤bOldLow (realBox b)
  | .tent s k =>
      (match k with
        | .rise => 0<D₀+(literalTentX s-2)*hi 0+(literalTentY s-2)*hi 1
        | .fall => 0<57*D₀+(-96*literalTentX s-64)*hi 0+(-96*literalTentY s-64)*hi 1) ∧
      2≤(literalTentEndpoint s k hi D₀:ℝ)

theorem realBox_grid_binding (lo : Fin 3 → ℤ) (a : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/(D₀:ℚ)) :
    ∀ i, realBox a i=(lo i:ℝ)/(D₀:ℝ) := by
  intro i
  simpa only [realBox,OriginalThirdBelowMuBRoundedSourceOnly.realBox,
    Rat.cast_div,Rat.cast_intCast] using
    congrArg (fun q : ℚ => (q:ℝ)) (haBind i)

/-- All ordinary original candidates, including B and all six tent sums with
their true if/elif sides, are assembled through the SAME finite max selector.
The selected winner's same-reader integer upper is derived, rather than
accepted as a hypothesis. Earlier-score strictness is provided separately by
selected_is_original_first_max; thus ties have the original Python priority. -/
theorem original_finite_winner_stored_integer_upper
    (table : CheckedBlockTable) (lo hi : Fin 3 → ℤ) (a b : Fin 3 → ℚ)
    (haBind : ∀ i, a i=(lo i:ℚ)/(D₀:ℚ))
    (hbBind : ∀ i, b i=(hi i:ℚ)/(D₀:ℚ))
    (ha : ∀ i, 0<realBox a i) (hab : ∀ i, realBox a i<realBox b i)
    (hcut : (1:ℝ)/100≤realBox a 2)
    (hyx : realBox b 1≤realBox a 0) (hzy : realBox b 2≤realBox a 1)
    (hmu : realBox b 0≤VariableEnvelope.mu)
    (hfull : realBox b 0+realBox b 1+3*realBox b 2≤thirdPrefixTheta)
    (hratio : ∀ i : Fin 2, realBox b i.castSucc/realBox a i.castSucc≤2)
    (hpositive : ∀ i : Fin 2,
      0<(originalLnUnit (realBox b i.castSucc/realBox a i.castSucc)).lo)
    (p : Candidate) (hselected : originalMinorant lo hi D₀ T₀=some p)
    (husable : usableCandidate hi b p) :
    (∫ t in compactRegion ∩ Icc (realBox a) (realBox b), compactKernel t)≤
      value (candidateIntegerUpper table lo hi a b p) := by
  cases p with
  | base =>
      exact ordinary_B_stored_integer_upper_of_grid table lo hi a b haBind hbBind
        ha hab hcut hyx hzy hmu hfull husable
  | tent s k =>
      exact original_finite_selected_tent_integer_upper table s k lo hi D₀ T₀
        (realBox a) (realBox b) rfl rfl
        (realBox_grid_binding lo a haBind) (realBox_grid_binding hi b hbBind)
        ha hab hcut hyx hzy hmu hfull hselected husable.1 husable.2 hratio hpositive

/-- Presence follows from the initial B candidate on an actual positive grid.
This is the finite dispatch disjunction, with no assertion that mean_upper
necessarily succeeds on the subsequently selected winner. -/
theorem original_finite_winner_cases (lo hi : Fin 3 → ℤ)
    (hz : 0≤lo 2) :
    originalMinorant lo hi D₀ T₀=some .base ∨
      ∃ s k, originalMinorant lo hi D₀ T₀=some (.tent s k) := by
  have hn := originalMinorant_ne_none lo hi D₀ T₀ rfl rfl hz
  cases hs : originalMinorant lo hi D₀ T₀ with
  | none => exact (hn hs).elim
  | some p =>
      cases p with
      | base => exact Or.inl hs
      | tent s k => exact Or.inr ⟨s,k,hs⟩

end
end ImbalancedChen.OriginalThirdP4AOrdinaryFiniteDispatchSourceOnly
