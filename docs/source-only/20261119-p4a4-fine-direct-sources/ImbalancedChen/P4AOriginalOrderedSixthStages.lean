import ImbalancedChen.P4AOriginalLaterSixthStages
import ImbalancedChen.P4AOriginalR17EighthParent
import ImbalancedChen.P4AOriginalSixthResidualFloor

/-! The physical fifth frontier, the saved sixth, the original eleven
and the eight later updates use one whole ordered third root. The early
activation of the old+new fifth rows is stored in d.omega. The later
physical cutoff is the separate omega argument of current. -/
namespace ImbalancedChen.P4AOriginalOrderedSixthStages
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4AOriginalOrderedThirdFullPolicy (Root current prior common five six cap5 cap6 fifth saved eleven after accepted
  current_ancestor prior_ancestor root_on_old_owner cap5_prior after_prior fifth_prior eligible_prior)
open P1OriginalVariableFourthContinuation (finiteMax finiteMax_seed_le finiteMax_row_le finiteMax_le)
open P4AOriginalSixthActionBank (Action allActions endpoint mem_allActions)
open P1GuardFrozenFiniteCapAlgebra (rounded)
open P4AOriginalSixthLaterLiteral (Cell stage)

def savedRaw (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℝ :=
  finiteMax Finset.univ (fun i => saved R d N i h)
    (fun i => P4AOriginalSavedSixthArchive.endpoint i (primeHistoryLogCoordinates N 6 h))
    (fifth R d N (rosserAncestor 5 h))

def rawAt (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℕ→ℝ
  | 0 => fifth R d N (rosserAncestor 5 h)
  | 1 => savedRaw R d N h
  | k+2 => after R d N h k

def value (n : ℕ) (N : ℝ) (h : List ℕ) (a : Action) : ℝ :=
  rounded n (endpoint a (primeHistoryLogCoordinates N 6 h))
def savedLicensed (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℝ :=
  finiteMax Finset.univ (fun i => accepted R d N n h (.saved i))
    (fun i => value n N h (.saved i)) (cap5 R d N n (rosserAncestor 5 h))
def laterLicensed (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℕ→ℝ
  | 0 => finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
      (fun c => accepted R d N n h (.eleven c)) (fun c => value n N h (.eleven c))
      (savedLicensed n R d N h)
  | k+1 => finiteMax Finset.univ (fun c : Cell => stage c=k ∧ accepted R d N n h (.later c))
      (fun c => value n N h (.later c)) (laterLicensed n R d N h k)

def finiteAt (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℕ→ℝ
  | 0 => cap5 R d N n (rosserAncestor 5 h)
  | 1 => savedLicensed n R d N h
  | k+2 => laterLicensed n R d N h k

def level (m n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) : ℝ :=
  if R.lower then finiteAt n R d N h m else rawAt R d N h m

theorem level_mono (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    Monotone (fun m => level m n R d N h) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hh : R.lower <;> simp only [level,hh,if_true,if_false]
  all_goals
    rcases k with _|k
    · exact finiteMax_seed_le _ _ _ _
    rcases k with _|k
    · exact finiteMax_seed_le _ _ _ _
    · exact finiteMax_seed_le _ _ _ _

theorem later_le_final (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    ∀ k,laterLicensed n R d N h k≤cap6 R d N n h := by
  have seed : cap5 R d N n (rosserAncestor 5 h)≤cap6 R d N n h := finiteMax_seed_le _ _ _ _
  have adm (a : Action) (ha : accepted R d N n h a) : value n N h a≤cap6 R d N n h :=
    finiteMax_row_le _ _ _ _ a (mem_allActions a) ha
  have hs : savedLicensed n R d N h≤cap6 R d N n h :=
    finiteMax_le _ _ _ _ _ seed (fun i _ hi => adm (.saved i) hi)
  intro k
  induction k with
  | zero => exact finiteMax_le _ _ _ _ _ hs (fun c _ hc => adm (.eleven c) hc)
  | succ k ih => exact finiteMax_le _ _ _ _ _ ih (fun c _ hc => adm (.later c) hc.2)

theorem licensed_ten (n : ℕ) (R : Root) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    finiteAt n R d N h 10=cap6 R d N n h := by
  have hl : Monotone (laterLicensed n R d N h) :=
    monotone_nat_of_le_succ (fun k => finiteMax_seed_le _ _ _ _)
  have hz := hl (show 0≤8 by omega)
  have hs : savedLicensed n R d N h≤laterLicensed n R d N h 0 := finiteMax_seed_le _ _ _ _
  apply le_antisymm (later_le_final n R d N h 8)
  apply finiteMax_le
  · exact (finiteMax_seed_le _ _ _ _).trans (hs.trans hz)
  · intro a _ ha
    cases a with
    | saved i => exact (finiteMax_row_le _ _ _ _ i (Finset.mem_univ _) ha).trans (hs.trans hz)
    | eleven c =>
      exact (finiteMax_row_le _ _ _ _ c (by cases c <;> decide) ha).trans hz
    | later c =>
      have hc : value n N h (.later c)≤laterLicensed n R d N h (stage c+1) :=
        finiteMax_row_le _ _ _ _ c (Finset.mem_univ _) ⟨rfl,ha⟩
      exact hc.trans (hl (Nat.succ_le_of_lt (P4AOriginalSixthLaterSemantics.original_stage_range c)))

def ownFifth (n : ℕ) (d : OriginalData) (omega N : ℝ) (h : List ℕ) : ℝ :=
  let R := current d omega N h
  if R.lower then cap5 R d N n h else fifth R d N h
def orderedFifth (n : ℕ) (d : OriginalData) (omega N : ℝ) (b : Bool) (h : List ℕ) : Bool :=
  five (current d omega N h) d N n b h
def orderedLevel (m n : ℕ) (d : OriginalData) (omega N : ℝ) (h : List ℕ) : ℝ :=
  level m n (current d omega N h) d N h
def policy (m n : ℕ) (d : OriginalData) (omega N : ℝ) :=
  firstExitDepthSplicePolicy 6 (orderedFifth n d omega N)
    (frozenParityRosserPolicy false 6 (fun h => N^orderedLevel m n d omega N h))

theorem orderedFifth_splice (n : ℕ) (d : OriginalData) (omega N : ℝ) :
    orderedFifth n d omega N = P4AOriginalSavedSixthFrontier.afterFour
      (fun b h => common (current d omega N h) d N b h)
      (fun h => N^ownFifth n d omega N h) := by
  funext b h
  simp only [orderedFifth,five,P4AOriginalSavedSixthFrontier.afterFour,firstExitDepthSplicePolicy,
    frozenParityRosserPolicy,ancestorFrozenPolicy,ownFifth,current_ancestor d omega N h 5 (by decide)]

theorem ordered_zero (n : ℕ) (d : OriginalData) (omega N : ℝ) (h : List ℕ) :
    orderedLevel 0 n d omega N h=ownFifth n d omega N (rosserAncestor 5 h) := by
  simp only [orderedLevel,level,ownFifth,finiteAt,rawAt,current_ancestor d omega N h 5 (by decide)]

theorem policy_zero (n : ℕ) (d : OriginalData) (omega N : ℝ) :
    policy 0 n d omega N=orderedFifth n d omega N := by
  funext b h
  by_cases hl : h.length≤6
  · simp only [policy,firstExitDepthSplicePolicy,if_pos hl]
  · have hl4 : ¬h.length≤4 := by omega
    rw [policy,orderedFifth_splice]
    simp only [firstExitDepthSplicePolicy,if_neg hl,P4AOriginalSavedSixthFrontier.afterFour,
      if_neg hl4,frozenParityRosserPolicy,ancestorFrozenPolicy,ordered_zero,rosserAncestor_nested 5 6 (by decide)]

theorem policy_ten (n : ℕ) (d : OriginalData) (omega N : ℝ) (b : Bool) (h : List ℕ) :
    policy 10 n d omega N b h=six (current d omega N h) d N n b h := by
  simp only [policy,orderedFifth,six,firstExitDepthSplicePolicy,frozenParityRosserPolicy,
    ancestorFrozenPolicy,orderedLevel,current_ancestor d omega N h 6 (by decide),
    level,licensed_ten,rawAt]

theorem ten_is_original_parent (n : ℕ) (e : ℚ) (q : ℕ) (a omega N : ℝ) :
    policy 10 n (P4AOriginalNewFifthUnion.data e q a) omega N =
    P4AOriginalR17EighthParent.orderedSixth n e q a omega N := by
  funext b h
  exact policy_ten n _ omega N b h

theorem prior_finite (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) (a : Action) :
    accepted (prior d N h) d N n h a ↔ P4AOriginalFull87DataPolicy.Accepted n d N h a := by
  simp only [accepted,P4AOriginalFull87DataPolicy.Accepted,eligible_prior]

theorem prior_saved (n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level 1 n (prior d N h) d N h=P4AOriginalSavedSixthStage.level n d N h := by
  simp only [level,finiteAt,rawAt,savedLicensed,savedRaw,value,prior_finite,
    P4AOriginalOrderedThirdFullPolicy.saved_prior,←cap5_prior n d N (rosserAncestor 5 h),
    ←fifth_prior d N (rosserAncestor 5 h),prior_ancestor d N h 5 (by decide),
    P4AOriginalSavedSixthStage.level,P4AOriginalFull87DataPolicy.savedExponent,
    P5OriginalCommonRefinedConstructor.actualParent5,endpoint] <;> rfl

theorem prior_later (k n : ℕ) (d : OriginalData) (N : ℝ) (h : List ℕ) :
    level (k+2) n (prior d N h) d N h=P4AOriginalLaterSixthStages.level n d N h k := by
  by_cases ha : P4AOriginalFull87DataPolicy.active d N h
  · have hp : (prior d N h).lower := ha
    have hs : savedLicensed n (prior d N h) d N h=P4AOriginalSavedSixthStage.level n d N h := by
      simpa only [level,if_pos hp,finiteAt] using prior_saved n d N h
    simp only [level,if_pos hp,finiteAt,P4AOriginalLaterSixthStages.level,if_pos ha]
    induction k with
    | zero =>
      simp only [laterLicensed,P4AOriginalLaterSixthStages.licensed,
        P4AOriginalElevenSixthStage.level,if_pos ha,prior_finite,value,endpoint,hs]
    | succ k ih =>
      simp only [laterLicensed,P4AOriginalLaterSixthStages.licensed,prior_finite,value,endpoint,ih]
  · have hp : ¬(prior d N h).lower := ha
    simp only [level,if_neg hp,rawAt,after_prior,P4AOriginalLaterSixthStages.level,if_neg ha]

theorem level_on_owner (m n : ℕ) (d : OriginalData) (omega N : ℝ)
    (he : 0≤(d.e:ℝ)) (hN : 1≤N) (hc : omega≤d.omega) (h : List ℕ)
    (hs : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N h) :
    orderedLevel m n d omega N h=level m n (prior d N h) d N h := by
  rw [orderedLevel,root_on_old_owner he hN hc hs]

end
end ImbalancedChen.P4AOriginalOrderedSixthStages
