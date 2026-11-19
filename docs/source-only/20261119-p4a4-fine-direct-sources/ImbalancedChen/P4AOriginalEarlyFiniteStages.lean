import ImbalancedChen.P4AOriginalEarlyHistoricalFloors
import ImbalancedChen.P4AOriginalEarlyMovingPlus
import ImbalancedChen.P4AOriginalFiniteFallbackSectorTransport
import ImbalancedChen.P4AOrderedThirdGlobalRange
import ImbalancedChen.P4AOriginalOrderedSixthSigned

namespace ImbalancedChen.P4AOriginalEarlyFiniteStages
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P5OriginalCommonFourthSourceNavigation (firstCoordinate firstCoordinate_ancestor guards_false_below_mu)
open P4AOrderedThirdArithmeticOccurrence (fresh)
open P4AOriginalFiniteFallbackPolicy (high dispatch)
open P4AOriginalOrderedThirdFullPolicy (Root current current_ancestor base common third fourth fifth cap5)
open P4AOriginalOrderedThirdTable (rawExponent)
open P4AOriginalOrderedSixthStages (orderedFifth orderedFifth_splice ownFifth)
open P1GuardFrozenFiniteCapAlgebra (protect protect_nested)
open P1OriginalVariableFourthContinuation (finiteMax_seed_le)
open P4AOriginalFull87RawChronology (cutoff rawRoot)
open P5OriginalCommonPositivePresieve (normalize normalize_add)
open P4AOriginalFull87HistoryCore (width)
open Set

abbrev parent (d : OriginalData) (N : ℝ) := HistoricalThirdCoarse.initialPolicy d.e d.m N
abbrev seed (d : OriginalData) (w N : ℝ) (h : List ℕ) := (current d w N h).scalar
abbrev Q3 (d : OriginalData) (w N : ℝ) (h : List ℕ) := N^rawExponent (d.e:ℝ) d.m w N h

def level4 (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) : ℝ :=
  let R := current d w N h
  if high N h then R.scalar else if R.lower then protect n R.scalar (fourth R d N h) else fourth R d N h

def level5 (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) : ℝ :=
  if high N h then seed d w N h else ownFifth n d w N h

abbrev Q4 (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) := N^level4 n d w N h
abbrev Q5 (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) := N^level5 n d w N h

theorem third_le_fourth (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    third R N h ≤ fourth R d N h := by
  unfold fourth
  split
  · exact finiteMax_seed_le _ _ _ _
  · rfl

theorem fourth_le_fifth (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    fourth R d N (rosserAncestor 4 h) ≤ fifth R d N h := by
  unfold fifth
  split
  · exact finiteMax_seed_le _ _ _ _
  · rfl

theorem cap5_as_protect (R : Root) (d : OriginalData) (N : ℝ) (n : ℕ) (h : List ℕ) :
    cap5 R d N n h=protect n R.scalar (fifth R d N h) :=
  protect_nested n _ _ _ (fourth_le_fifth R d N h)

theorem seed_le_four (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) :
    seed d w N h≤level4 n d w N h := by
  unfold level4
  split_ifs
  · rfl
  · exact le_max_left _ _
  · exact (le_max_left _ _).trans (third_le_fourth _ _ _ h)

theorem four_le_five (n : ℕ) (d : OriginalData) (w N : ℝ) (h : List ℕ) :
    level4 n d w N (rosserAncestor 4 h) ≤ level5 n d w N h := by
  have hh : high N (rosserAncestor 4 h) ↔ high N h := by
    change VariableEnvelope.mu<firstCoordinate N (rosserAncestor 4 h) ↔ _
    rw [firstCoordinate_ancestor N 4 (by decide)]
    rfl
  simp only [level4,level5,ownFifth,hh,current_ancestor d w N h 4 (by decide)]
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _
  · exact fourth_le_fifth _ _ _ _

theorem base_is_fresh (d : OriginalData) (w : ℝ) (N : ℕ) (b : Bool) (h : List ℕ) :
    base (current d w N h) d N b h=fresh d w N b h := by rfl

theorem low_common (d : OriginalData) (w : ℝ) (N : ℕ) (b : Bool) (h : List ℕ) (hlo : ¬high N h) :
    common (current d w N h) d N b h = fresh d w N b h := by
  rw [←base_is_fresh]
  by_cases h2 : h.length≤2
  · have h3 := h2.trans (by decide : 2≤3)
    simp only [common,if_pos h2,if_pos h3,Bool.or_self]
  · obtain ⟨hS,hT⟩ := guards_false_below_mu N h (by omega) (le_of_not_gt hlo)
    by_cases h3 : h.length≤3 <;> simp [common,h2,h3,hS,hT]

/-- One common upper branch reads the fresh tree on every high word.
Every lower descendant reads the actual finite fourth/fifth ancestry. -/
theorem actual_dispatch (n : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) :
    dispatch N (fresh d w N) (orderedFifth n d w N) =
      fifthCappedUpperPolicy (parent d N) (Q3 d w N) (Q5 n d w N) := by
  funext b h
  have hhigh : high N (rosserAncestor 5 h) ↔ high N h := by
    change VariableEnvelope.mu<firstCoordinate N (rosserAncestor 5 h) ↔ _
    rw [firstCoordinate_ancestor N 5 (by decide)]
    rfl
  rw [orderedFifth_splice]
  by_cases hlo : high N h
  · rw [dispatch,if_pos hlo]
    by_cases h4 : h.length≤4
    · simp [fifthCappedUpperPolicy,firstExitDepthSplicePolicy,h4,fresh,P4AOriginalOrderedThirdTable.policy]
    · have h2 : ¬h.length≤2 := by omega
      simp only [fresh,P4AOriginalOrderedThirdTable.policy,fifthCappedUpperPolicy,thirdCappedUpperPolicy,
        firstExitDepthSplicePolicy,if_neg h4,if_neg h2,frozenParityRosserPolicy,ancestorFrozenPolicy,
        Q5,level5,hhigh,if_pos hlo,seed,current,Q3,rosserAncestor_nested 3 5 (by decide)]
  · rw [dispatch,if_neg hlo]
    by_cases h4 : h.length≤4
    · simp only [P4AOriginalSavedSixthFrontier.afterFour,fifthCappedUpperPolicy,firstExitDepthSplicePolicy,if_pos h4]
      exact low_common d w N b h hlo
    · simp only [P4AOriginalSavedSixthFrontier.afterFour,fifthCappedUpperPolicy,
        firstExitDepthSplicePolicy,if_neg h4,frozenParityRosserPolicy,ancestorFrozenPolicy,Q5,level5,hhigh,if_neg hlo]

abbrev A4 (d : OriginalData) (w : ℝ) (N cap : ℕ) (z : ℝ) :=
  firstExitAdmittedTuples 4 (fresh d w N) (roughPrimeUniverse N cap 0 z)
abbrev A5 (d : OriginalData) (w : ℝ) (N cap : ℕ) (z : ℝ) :=
  firstExitFrontierTuples 4 (fresh d w N) (roughPrimeUniverse N cap 0 z)
abbrev W {k : ℕ} (p : Fin k→ℕ) := ∏ i,1/((p i:ℝ)-1)
abbrev F4 (n : ℕ) (d : OriginalData) (w : ℝ) (N cap : ℕ) :=
  P1OriginalCoarseFourthResidual.literalTupleResidualDifference (Q3 d w N) (Q4 n d w N) N cap
abbrev F5 (n : ℕ) (d : OriginalData) (w : ℝ) (N cap : ℕ) :=
  P1CorrectedFifthCausalTupleDictionary.literalTupleDifference (Q4 n d w N) (Q5 n d w N) N cap

/-- Exact signed ordinary root decomposition before any estimates. Four
is admitted through rank four. Five enumerates all next candidates,
including prefixes newly restored at their own cube. -/
theorem signed_lower_early (n : ℕ) (d : OriginalData) (w : ℝ) (N : ℕ) (hN : 1≤(N:ℝ)) :
    normalize N (rawRoot (fresh d w N) N-rawRoot (dispatch N (fresh d w N) (orderedFifth n d w N)) N) =
    (∑p∈A4 d w N N (cutoff N),W p*F4 n d w N N p)+(∑p∈A5 d w N N (cutoff N),W p*F5 n d w N N p) := by
  let B := parent d N
  let T := Q3 d w N
  let A := Q4 n d w N
  let U := Q5 n d w N
  have hx := actualHistoricalThirdToFifthSaving_eq B T A U N N (cutoff N)
    (fun s _=>Real.rpow_le_rpow_of_exponent_le hN (seed_le_four n d w N s.selectedPrefix))
    (by intro s hs c hc
        have hlen := firstExitDepthFrontier_selected_length 4 (fresh d w N)
          (fun p : ℕ=>1/((p:ℝ)-1)) [] (roughPrimeUniverse N N 0 (cutoff N)) true 1 (by simp) s hs
        obtain ⟨before,p,after,_,rfl⟩ := (mem_firstExitNextSelectionCandidates_iff _ _ _ _ _ c).mp hc
        apply Real.rpow_le_rpow_of_exponent_le hN
        simpa only [rosserAncestor_cons 4 p s.selectedPrefix hlen.ge,
          rosserAncestor_self_of_length 4 s.selectedPrefix hlen] using
          four_le_five n d w N (p::s.selectedPrefix))
  have even1 (p : List ℕ) : fresh d w N true p=true := by
    simp [fresh,P4AOriginalOrderedThirdTable.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,
      parent,HistoricalThirdCoarse.initialPolicy,frozenParityRosserPolicy,ancestorFrozenPolicy,
      ordinaryParityRosserPolicy,oddFirstExitPolicy]
  have even2 (p : List ℕ) : dispatch N (fresh d w N) (orderedFifth n d w N) true p=true := by
    simp [dispatch,even1,P4AOriginalOrderedSixthSigned.fifth_even]
  change firstExitRetainedPolynomial (fresh d w N) _ _ _ _ _ -
    firstExitRetainedPolynomial (fifthCappedUpperPolicy B T U) _ _ _ _ _ = _ at hx
  rw [←actual_dispatch n d w N,
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _ even1 N N 0 (cutoff N),
    UpperPolicyFiniteBridge.firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained _ even2 N N 0 (cutoff N)] at hx
  change rawRoot (fresh d w N) N-rawRoot (dispatch N (fresh d w N) (orderedFifth n d w N)) N=_ at hx
  rw [hx,normalize_add]
  change _*Real.log (N:ℝ)/singularSeries N+_*Real.log (N:ℝ)/singularSeries N=_
  rw [P1OriginalCoarseFourthResidual.actualHistoricalFourthSaving_eq_literalTupleSum,
    P1CorrectedFifthCausalTupleDictionary.actualHistoricalFifthSaving_eq_literalTupleSum]

end
end ImbalancedChen.P4AOriginalEarlyFiniteStages
