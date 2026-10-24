import ImbalancedChen.ActualThirdOriginalP4AOrdinaryFiniteSelector
import ImbalancedChen.ActualThirdOriginalP4ASymmetricBLeaf
import ImbalancedChen.ActualThirdOriginalP4ASixTentSymmetricLeaf
import ImbalancedChen.P4ASymmetricNewOnlySameReader

/-!
SOURCEONLY / UNCOMPILED / HOLD_ELABORATION / OPEN30.
The original BELOW-mu symmetric mean_upper dispatcher. The finite selector
retains B first and the original six-loop order and first-maximum policy.
Post-selection coefficient/residual/crossing rejection never selects a
different plane. The high<=2 return precedes OLD/chord evaluation. The
low==high fallback is represented exactly and proved unreachable on the
actual positive-width geometry after a successful residual test.
-/
namespace ImbalancedChen.OriginalThirdP4ASymmetricFiniteDispatch
noncomputable section
open Set MeasureTheory
open OriginalThirdBoxMomentsSourceOnly OriginalThirdSixTentCandidatesSourceOnly
open OriginalThirdLiteralTentSelectorGuardBridgeSourceOnly
open OriginalThirdSixTentRoundedConsumerSourceOnly
open OriginalThirdP4AOrdinaryFiniteSelectorSourceOnly
open OriginalThirdP4ASymmetricTentPrerequisites OriginalThirdP4ABalancedSymmetricLeaf
open OriginalThirdP4ASymmetricBLeaf OriginalThirdP4ASixTentSymmetricLeaf
open P4ASymmetricNewOnlyLeafSourceOnly
open OriginalThirdClippedChordSourceOnly OriginalThirdRoundedNewSourceOnly
open OriginalThirdPositiveLogSourceOnly OriginalThirdRoundedStoredConsumerSourceOnly
open OriginalThirdSymmetricMassCeilSourceOnly OriginalThirdSymmetricJensenSourceOnly
open OriginalThirdSortedHalfIntegralSourceOnly OriginalThirdCompactPartitionSourceOnly
open OriginalU2StoredNodeBlockDataSourceOnly OriginalU2StoredNodeBlockCheckerSourceOnly
open OriginalU2StoredQueryLookupSourceOnly

local notation "D₀" => (48000*2^24:ℤ)
local notation "T₀" => (481573208064:ℤ)

def symmetricRaw (x z : ℤ) : Fin 3 → ℤ := ![x,x,z]

def candidateLow (x1 z1 : ℤ) : Candidate → ℚ
  | .base => savedBLow x1 z1
  | .tent s k => savedTentLow s k x1 z1

def candidateHigh (x0 z0 : ℤ) : Candidate → ℚ
  | .base => savedBHigh x0 z0
  | .tent s k => savedTentHigh s k x0 z0

def candidateBadCoefficients : Candidate → Prop
  | .base => (0:ℤ)>256 ∨ (0:ℤ)>256
  | .tent s .rise => literalTentX s>2 ∨ literalTentY s>2
  | .tent s .fall => -96*literalTentX s>64 ∨ -96*literalTentY s>64

theorem candidate_coefficients_pass (p : Candidate) : ¬candidateBadCoefficients p := by
  cases p with
  | base => norm_num [candidateBadCoefficients]
  | tent s k =>
      cases s <;> cases k <;>
        norm_num [candidateBadCoefficients,literalTentX,literalTentY]

/-- The original low_num positivity gate, before adding the z term. -/
def candidateResidual (x1 : ℤ) : Candidate → Prop
  | .base => 0<153*D₀-256*x1-256*x1
  | .tent s k => literalSymmetricResidual s k x1

def newOut (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ) : ℤ :=
  readQueryHi160 (assembledRead table.blocks) (storedGridNew x0 x1 z0 z1).hi P160

def candidateChordCost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Candidate → ℤ
  | .base => symmetricBCost table x0 x1 z0 z1 a b c d
  | .tent s k => sixTentSymmetricCost table s k x0 x1 z0 z1 a b c d

/-- This Option is the producer's mean candidate AFTER its chosen plane.
None denotes absence of a mean candidate, never a zero-cost leaf. -/
def candidateMeanCost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) (p : Candidate) : Option ℤ := by
  classical
  exact if candidateBadCoefficients p then none
    else if candidateResidual x1 p then
      if candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p then none
      else if candidateHigh x0 z0 p≤2 then
        some (literalSymmetricUpper x0 x1 z0 z1 (newOut table x0 x1 z0 z1))
      else if candidateLow x1 z1 p=candidateHigh x0 z0 p then
        some (literalSymmetricUpper x0 x1 z0 z1
          (max 0 (newOut table x0 x1 z0 z1-
            readQueryLo160 (assembledRead table.blocks)
              (candidateLow x1 z1 p).num ((candidateLow x1 z1 p).den:ℤ))))
      else some (candidateChordCost table x0 x1 z0 z1 a b c d p)
    else none

def symmetricMeanCost (table : CheckedBlockTable) (x0 x1 z0 z1 : ℤ)
    (a b c d : ℚ) : Option ℤ :=
  match originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => none
  | some p => candidateMeanCost table x0 x1 z0 z1 a b c d p

/-- The producer's symmetric flag and the below-mu branch of minorant are
derived from the actual bound coordinates, including the strict x0<M test. -/
theorem original_symmetric_raw_geometry (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) :
    symmetricRaw x0 z0 0=symmetricRaw x0 z0 1 ∧
      symmetricRaw x1 z1 0=symmetricRaw x1 z1 1 ∧
      z1≤x0 ∧ x0<25*D₀/128 := by
  have hD : (0:ℝ)<(D₀:ℝ) := by norm_num
  have haR : (a:ℝ)=(x0:ℝ)/(D₀:ℝ) := by
    rw [ha]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hdR : (d:ℝ)=(z1:ℝ)/(D₀:ℝ) := by
    rw [hd]
    simp only [Rat.cast_div,Rat.cast_intCast]
  have hza : (z1:ℝ)≤(x0:ℝ) :=
    (div_le_div_iff_of_pos_right hD).1 (by
      simpa only [haR,hdR] using hg.z_below_xy)
  have hx : (x0:ℝ)/(D₀:ℝ)<25/128 := by
    simpa only [←haR,VariableEnvelope.mu] using hg.width_xy.trans_le hmu
  have hxscaled := (div_lt_iff₀ hD).1 hx
  have hM : (25*(D₀:ℝ)/128)=(25*D₀/128:ℤ) := by norm_num
  have hxM : (x0:ℝ)<(25*D₀/128:ℤ) := by
    rw [←hM]
    linarith only [hxscaled]
  exact ⟨rfl,rfl,by exact_mod_cast hza,by exact_mod_cast hxM⟩

theorem candidateMeanCost_crossing_none (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (p : Candidate)
    (hcross : candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p) :
    candidateMeanCost table x0 x1 z0 z1 a b c d p=none := by
  classical
  unfold candidateMeanCost
  rw [if_neg (candidate_coefficients_pass p)]
  by_cases hr : candidateResidual x1 p
  · rw [if_pos hr,if_pos hcross]
  · rw [if_neg hr]

theorem symmetricMeanCost_missing_selector (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (hn : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀=none) :
    symmetricMeanCost table x0 x1 z0 z1 a b c d=none := by
  simp only [symmetricMeanCost,hn]

theorem selected_tent_literal_guards (s : TentSum) (k : TentSide)
    (x0 x1 z0 z1 : ℤ)
    (hselected : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1)
      D₀ T₀=some (.tent s k)) :
    literalSymmetricBranch s k x0 x1 z0 z1 ∧
      literalSymmetricRoot s k x0 x1 z0 z1 := by
  have hg := selected_tent_guards _ _ _ _ s k hselected
  cases k <;>
    simpa only [branchTest,rootTest,deltaNumerator,rawSum,symmetricRaw,
      literalSymmetricBranch,literalSymmetricRoot,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,add_assoc] using hg

/-- Strict span is proved for the actual selected B-or-six plane; neither
an endpoint equality nor a desired leaf bound is a caller premise. -/
theorem selected_candidate_span (p : Candidate) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hselected : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1)
      D₀ T₀=some p) (hres : candidateResidual x1 p) :
    candidateLow x1 z1 p<candidateHigh x0 z0 p := by
  cases p with
  | base => exact saved_B_span x0 x1 z0 z1 a b c d ha hb hc hd hg hmu
  | tent s k =>
      obtain ⟨hbranch,hroot⟩ := selected_tent_literal_guards s k x0 x1 z0 z1 hselected
      have hguards := original_selected_tent_guard_bridge s k
        ![x0,x0,z0] ![x1,x1,z1] D₀ T₀
        (symmetricLeft (a:ℝ) (c:ℝ)) (symmetricRight (b:ℝ) (d:ℝ))
        rfl rfl (symmetric_grid_bind x0 z0 a c ha hc)
        (symmetric_grid_bind x1 z1 b d hb hd)
        (by simpa only [literalSymmetricBranch,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val_two] using hbranch)
        (by simpa only [literalSymmetricRoot,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val_two] using hroot)
        (by simpa only [candidateResidual,literalSymmetricResidual,Matrix.cons_val_zero,
          Matrix.cons_val_one,Matrix.cons_val_two] using hres)
      have hz0 := positive_grid_binding z0 c hc (symmetric_positive hg).2
      have hz1 := positive_grid_binding z1 d hd ((symmetric_positive hg).2.trans hg.width_z)
      have hl := saved_tent_endpoint_cast s k x1 z1 b d hb hd hz1
      have hh := saved_tent_endpoint_cast s k x0 z0 a c ha hc hz0
      have hs := symmetric_tent_span s k hg hguards.2.2
      have hsR : (savedTentLow s k x1 z1:ℝ)<(savedTentHigh s k x0 z0:ℝ) := by
        rw [hl,hh]
        exact hs
      exact_mod_cast hsR

theorem selected_candidate_chord_upper (table : CheckedBlockTable)
    (p : Candidate) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hselected : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1)
      D₀ T₀=some p) (hres : candidateResidual x1 p)
    (hlow : (2:ℚ)≤candidateLow x1 z1 p)
    (hratio : x1≤2*x0)
    (hpositive : 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value (candidateChordCost table x0 x1 z0 z1 a b c d p) := by
  cases p with
  | base =>
      exact original_B_symmetric_stored_integer_upper table x0 x1 z0 z1 a b c d
        ha hb hc hd hg hmu hlow hratio hpositive
  | tent s k =>
      obtain ⟨hbranch,hroot⟩ := selected_tent_literal_guards s k x0 x1 z0 z1 hselected
      exact original_six_tent_symmetric_stored_integer_upper table s k
        x0 x1 z0 z1 a b c d ha hb hc hd hg hmu hbranch hroot hres hlow hratio hpositive

/-- Actual positive-width source geometry has precisely these OLD-domain
outcomes: early return, crossing rejection, or strict supported chord.
Thus neither the midpoint crossing nor equality can be routed to a chord. -/
theorem selected_candidate_dispatch_domain (p : Candidate)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu)
    (hselected : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1)
      D₀ T₀=some p) (hres : candidateResidual x1 p) :
    candidateHigh x0 z0 p≤2 ∨
      (candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p) ∨
      (2≤candidateLow x1 z1 p ∧ candidateLow x1 z1 p<candidateHigh x0 z0 p) := by
  by_cases he : candidateHigh x0 z0 p≤2
  · exact Or.inl he
  · by_cases hl : candidateLow x1 z1 p<2
    · exact Or.inr (Or.inl ⟨hl,lt_of_not_ge he⟩)
    · exact Or.inr (Or.inr ⟨le_of_not_gt hl,
        selected_candidate_span p x0 x1 z0 z1 a b c d ha hb hc hd hg hmu hselected hres⟩)

/-- Real source success, including the early branch, derives an actual
stored integer bound. All sieve queries are supplied by the leaf suppliers.
The successful Option equation binds output data, not a target inequality. -/
theorem original_selected_symmetric_mean_upper (table : CheckedBlockTable)
    (p : Candidate) (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) (hratio : x1≤2*x0)
    (hpositive : 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo)
    (hselected : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1)
      D₀ T₀=some p)
    (hcost : candidateMeanCost table x0 x1 z0 z1 a b c d p=some cost) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value cost := by
  classical
  unfold candidateMeanCost at hcost
  rw [if_neg (candidate_coefficients_pass p)] at hcost
  by_cases hres : candidateResidual x1 p
  · rw [if_pos hres] at hcost
    by_cases hcross : candidateLow x1 z1 p<2 ∧ 2<candidateHigh x0 z0 p
    · rw [if_pos hcross] at hcost
      cases hcost
    · rw [if_neg hcross] at hcost
      by_cases hearly : candidateHigh x0 z0 p≤2
      · rw [if_pos hearly] at hcost
        have hcst := Option.some.inj hcost
        rw [←hcst]
        exact original_stored_symmetric_new_only_same_reader_integer_upper_general table
          x0 x1 z0 z1 a b c d ha hb hc hd hg hratio hpositive
      · rw [if_neg hearly] at hcost
        have hspan := selected_candidate_span p x0 x1 z0 z1 a b c d
          ha hb hc hd hg hmu hselected hres
        rw [if_neg (ne_of_lt hspan)] at hcost
        have hlow : (2:ℚ)≤candidateLow x1 z1 p := by
          by_contra hn
          exact hcross ⟨lt_of_not_ge hn,lt_of_not_ge hearly⟩
        have hcst := Option.some.inj hcost
        rw [←hcst]
        exact selected_candidate_chord_upper table p x0 x1 z0 z1 a b c d
          ha hb hc hd hg hmu hselected hres hlow hratio hpositive
  · rw [if_neg hres] at hcost
    cases hcost

/-- Single below-mu symmetric source dispatcher, B and all six tents with
the original first-max selector, and the true high<=2 early return. -/
theorem original_symmetric_finite_dispatch_integer_upper (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (ha : a=(x0:ℚ)/(D₀:ℚ)) (hb : b=(x1:ℚ)/(D₀:ℚ))
    (hc : c=(z0:ℚ)/(D₀:ℚ)) (hd : d=(z1:ℚ)/(D₀:ℚ))
    (hg : SymmetricFullBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ))
    (hmu : (b:ℝ)≤VariableEnvelope.mu) (hratio : x1≤2*x0)
    (hpositive : 0<(originalLnUnit ((x1:ℝ)/(x0:ℝ))).lo)
    (hcost : symmetricMeanCost table x0 x1 z0 z1 a b c d=some cost) :
    (∫ t in compactRegion∩symmetricBox (a:ℝ) (b:ℝ) (c:ℝ) (d:ℝ),compactKernel t)≤
      value cost := by
  cases hselected : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none =>
      simp only [symmetricMeanCost,hselected] at hcost
  | some p =>
      have hp : candidateMeanCost table x0 x1 z0 z1 a b c d p=some cost := by
        simpa only [symmetricMeanCost,hselected] using hcost
      exact original_selected_symmetric_mean_upper table p x0 x1 z0 z1 a b c d cost
        ha hb hc hd hg hmu hratio hpositive hselected hp

/-- Successful mean dispatch retains the original first-maximum witness,
including strict scores before the winner and weak scores after it. -/
theorem symmetric_dispatch_retains_first_max (table : CheckedBlockTable)
    (x0 x1 z0 z1 : ℤ) (a b c d : ℚ) (cost : ℤ)
    (hcost : symmetricMeanCost table x0 x1 z0 z1 a b c d=some cost) :
    ∃ p before after,
      originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀=some p ∧
      candidateMeanCost table x0 x1 z0 z1 a b c d p=some cost ∧
      sourceCandidates (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀=before++p::after ∧
      (∀ q∈before, sourceScore (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ q<
        sourceScore (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ p) ∧
      (∀ q∈after, sourceScore (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ q≤
        sourceScore (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ p) := by
  cases hs : originalMinorant (symmetricRaw x0 z0) (symmetricRaw x1 z1) D₀ T₀ with
  | none => simp only [symmetricMeanCost,hs] at hcost
  | some p =>
      obtain ⟨before,after,hlist,hbefore,hafter⟩ :=
        selected_is_original_first_max _ _ _ _ p hs
      exact ⟨p,before,after,hs,
        by simpa only [symmetricMeanCost,hs] using hcost,hlist,hbefore,hafter⟩

end
end ImbalancedChen.OriginalThirdP4ASymmetricFiniteDispatch
