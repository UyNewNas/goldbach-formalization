import ImbalancedChen.P4AOriginalOrderedThirdAgreement
import ImbalancedChen.P4AOriginalNewFifthCounting

/-! Evaluate the existing fourth, old+new fifth, saved/eleven/later sixth
and original eighth actions against one literal third ancestor. Each row
bank and its coordinate ownership continues to come from the same d+. -/
namespace ImbalancedChen.P4AOriginalOrderedThirdFullPolicy
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P5OriginalCommonRefinedConstructor (OriginalData SixthCell)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (secondGuard thirdGuard thirdQ)
open P1OriginalVariableFourthContinuation (finiteMax)
open P2OriginalFourthCapProducerInterface (producerEligible)
open P1GuardFrozenFiniteCapAlgebra P4AOriginalFull87HistoryCore (width)
open P4AOriginalSixthActionBank (Action allActions endpoint selected)
open P4AOriginalCompleteSixthChronology (laterEligible applyLater)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P4AOriginalOrderedThirdTable (retained atPoint rawExponent)
open P1QuantizedActionLicense (LowerLicense)

structure Root where
  scalar : ℝ
  lower : Prop

def current (d : OriginalData) (omega N : ℝ) (pre : List ℕ) : Root :=
  let h := rosserAncestor 3 pre
  let t := primeHistoryLogCoordinates N 3 h
  ⟨rawExponent (d.e:ℝ) d.m omega N h, t 0≤mu ∧ HistoricalThirdCoarse.active omega N h ∧
    ∃ j ∈ retained (d.e:ℝ) d.m, t ∈ logPrimeMeshCell 0 (19/96) d.m j⟩

def prior (d : OriginalData) (N : ℝ) (pre : List ℕ) : Root :=
  ⟨P5OriginalCommonRefinedConstructor.originalSeed d N pre,
    P4AOriginalFull87DataPolicy.active d N pre⟩

variable (R : Root) (d : OriginalData) (N : ℝ)

def base (pos : Bool) (pre : List ℕ) : Bool :=
  if pre.length≤2 then HistoricalThirdCoarse.initialPolicy d.e d.m N pos pre
  else ordinaryParityRosserPolicy false (N^R.scalar) pos pre

def common (pos : Bool) (pre : List ℕ) : Bool :=
  let b := base R d N pos pre
  let s := if pre.length≤2 then b else
    if secondGuard N pre then ordinaryParityRosserPolicy false
      (N^v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)) pos pre else b
  b || (if pre.length≤3 then s else if thirdGuard N pre then
    ordinaryParityRosserPolicy false (thirdQ N (rosserAncestor 3 pre)) pos pre else s)

def third (pre : List ℕ) : ℝ :=
  max R.scalar (if thirdGuard N pre then
    v (primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 1+
      primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 2)
    else if secondGuard N pre then v (primeHistoryLogCoordinates N 2 (rosserAncestor 2 pre) 1)
    else R.scalar)

def fourth (pre : List ℕ) : ℝ :=
  if pre.length=4 then finiteMax d.rows4
    (fun r => producerEligible d.licensed4 r (primeHistoryLogCoordinates N 4 pre))
    (fun r => r.bufferedCandidate (d.e:ℝ) (primeHistoryLogCoordinates N 4 pre))
    (third R N pre)
  else third R N pre

def fifth (pre : List ℕ) : ℝ :=
  let inherited := fourth R d N (rosserAncestor 4 pre)
  if pre.length=5 then finiteMax d.rows5
    (fun r => P1OriginalVariableFifthContinuation.eligible d.e d.chi d.m d.omega
      d.J5 r (primeHistoryLogCoordinates N 5 pre))
    (fun r => P1OriginalVariableFifthContinuation.candidate (d.e:ℝ) r.selected
      (primeHistoryLogCoordinates N 5 pre)) inherited
  else inherited

def saved (i : P4AOriginalSavedSixthArchive.Row) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  pre.length=6 ∧ P4AOriginalSavedSixthArchive.Source i t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H3 t < third R N pre ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H5 t < third R N pre ∧
    fifth R d N (rosserAncestor 5 pre) ≤ P4AOriginalSavedSixthArchive.oldUpper i t

def eleven (c : SixthCell) (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  let parent := fifth R d N (rosserAncestor 5 pre)
  pre.length=6 ∧ Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H5 t < parent ∧
    parent ≤ Certificates.P2OriginalSixthElevenLogSemantics.oldCap c t

def after (pre : List ℕ) : ℕ → ℝ
  | 0 =>
    let t := primeHistoryLogCoordinates N 6 pre
    let s := finiteMax Finset.univ (fun i => saved R d N i pre)
      (fun i => P4AOriginalSavedSixthArchive.endpoint i t) (fifth R d N (rosserAncestor 5 pre))
    finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
      (fun c => eleven R d N c pre) (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c t) s
  | k+1 => applyLater k N (after R d N pre k) pre

def eligible (pre : List ℕ) : Action → Prop
  | .saved i => saved R d N i pre
  | .eleven c => eleven R d N c pre
  | .later c => laterEligible (P4AOriginalSixthLaterLiteral.stage c)
      (after R d N pre (P4AOriginalSixthLaterLiteral.stage c)) N c pre

def accepted (n : ℕ) (pre : List ℕ) (a : Action) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  eligible R d N pre a ∧ LowerLicense (selected a) t (rounded n (endpoint a t):ℝ) ∧
    (rounded n (endpoint a t):ℝ)+width n ≤ v (∑ j ∈ selected a,t j)

def cap5 (n : ℕ) (pre : List ℕ) : ℝ :=
  max (protect n R.scalar (fourth R d N (rosserAncestor 4 pre))) (rounded n (fifth R d N pre):ℝ)

def cap6 (n : ℕ) (pre : List ℕ) : ℝ :=
  finiteMax allActions (accepted R d N n pre)
    (fun a => (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)):ℝ))
    (cap5 R d N n (rosserAncestor 5 pre))

def five (n : ℕ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (common R d N) (frozenParityRosserPolicy false 5
    (fun h => N^(if R.lower then cap5 R d N n h else fifth R d N h)))

def six (n : ℕ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (five R d N n) (frozenParityRosserPolicy false 6
    (fun h => N^(if R.lower then cap6 R d N n h else after R d N h 8)))

def eight (delta : ℝ) (n : ℕ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (six R d N n) (fun pos pre =>
    match selectedCap delta n N pre with
    | none => six R d N n pos pre
    | some a => ordinaryParityRosserPolicy false (N^(a:ℝ)) pos pre)

def policy (delta : ℝ) (n : ℕ) (d : OriginalData) (omega N : ℝ) (pos : Bool) (pre : List ℕ) :=
  eight (current d omega N pre) d N delta n pos pre

theorem prior_ancestor (d : OriginalData) (N : ℝ) (pre : List ℕ) (k : ℕ) (hk : 3≤k) :
    prior d N (rosserAncestor k pre)=prior d N pre := by
  unfold prior P5OriginalCommonRefinedConstructor.originalSeed P1OriginalVariableFourthContinuation.seedExponent
    P4AOriginalFull87DataPolicy.active
  simp only [rosserAncestor_nested 3 k hk]

theorem current_ancestor (d : OriginalData) (omega N : ℝ) (pre : List ℕ) (k : ℕ) (hk : 3≤k) :
    current d omega N (rosserAncestor k pre)=current d omega N pre := by
  simp only [current,rosserAncestor_nested 3 k hk]

theorem common_prior (d : OriginalData) (N : ℝ) (pos : Bool) (pre : List ℕ) :
    common (prior d N pre) d N pos pre=P5OriginalCommonRefinedConstructor.common3 d N pos pre := by
  have hh : HistoricalThirdCoarse.rawLevel (d.e:ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre)=
      N^(prior d N pre).scalar := P1CoarseFirstCubeFallbackMargin.rawLevel_eq_rpow_effectiveExponent _ _ _ _ _ _
  simp only [common,base,P5OriginalCommonRefinedConstructor.common3,P5OriginalCommonRefinedConstructor.old3,
    P5OriginalCommonRefinedConstructor.fallback23,P5OriginalAboveMuThirdLowerPhysicalCoefficient.finalPolicy,
    P5OriginalAboveMuThirdLowerPhysicalCoefficient.thirdReplacement,P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondPolicy,
    P5OriginalAboveMuThirdLowerPhysicalCoefficient.secondReplacement,P5OriginalAboveMuThirdLowerPhysicalCoefficient.oldPolicy,
    HistoricalThirdCoarse.policy,thirdCappedUpperPolicy,firstExitDepthSplicePolicy,frozenParityRosserPolicy,
    ancestorFrozenPolicy,hh]

theorem third_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    third (prior d N pre) N pre=P5OriginalCommonRefinedConstructor.lambda3 d N pre := rfl

theorem fourth_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    fourth (prior d N pre) d N pre=P5OriginalCommonRefinedConstructor.exponent4 d N pre := rfl

theorem fifth_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    fifth (prior d N pre) d N pre=P5OriginalCommonRefinedConstructor.exponent5 d N pre := by
  simp only [fifth,P5OriginalCommonRefinedConstructor.exponent5,
    ← fourth_prior d N (rosserAncestor 4 pre),prior_ancestor d N pre 4 (by decide)]

theorem saved_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) (i : P4AOriginalSavedSixthArchive.Row) :
    saved (prior d N pre) d N i pre ↔ P4AOriginalFull87DataPolicy.savedEligible d N i pre := by
  simp only [saved,P4AOriginalFull87DataPolicy.savedEligible,third_prior,
    P5OriginalCommonRefinedConstructor.actualParent5,← fifth_prior d N (rosserAncestor 5 pre),
    prior_ancestor d N pre 5 (by decide)]

theorem eleven_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) (c : SixthCell) :
    eleven (prior d N pre) d N c pre ↔ P5OriginalCommonRefinedConstructor.eligibleSixth d N c pre := by
  simp only [eleven,P5OriginalCommonRefinedConstructor.eligibleSixth,
    P5OriginalCommonRefinedConstructor.actualParent5,← fifth_prior d N (rosserAncestor 5 pre),
    prior_ancestor d N pre 5 (by decide)]

theorem after_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) (k : ℕ) :
    after (prior d N pre) d N pre k=P4AOriginalFull87DataPolicy.afterLater d N pre k := by
  induction k with
  | zero =>
    simp only [after,P4AOriginalFull87DataPolicy.afterLater,P4AOriginalFull87DataPolicy.elevenExponent,
      P4AOriginalFull87DataPolicy.savedExponent,saved_prior,eleven_prior,
      P5OriginalCommonRefinedConstructor.actualParent5,← fifth_prior d N (rosserAncestor 5 pre),
      prior_ancestor d N pre 5 (by decide)]
  | succ k ih => simp only [after,P4AOriginalFull87DataPolicy.afterLater,ih]

theorem eligible_prior (d : OriginalData) (N : ℝ) (pre : List ℕ) (a : Action) :
    eligible (prior d N pre) d N pre a ↔ P4AOriginalFull87DataPolicy.ActualEligible d N pre a := by
  cases a with
  | saved i => exact saved_prior d N pre i
  | eleven c => exact eleven_prior d N pre c
  | later c => simp only [eligible,P4AOriginalFull87DataPolicy.ActualEligible,after_prior]

theorem cap5_prior (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    cap5 (prior d N pre) d N n pre=P4AOriginalFull87DataPolicy.cap5 n d N pre := by
  simp only [cap5,P4AOriginalFull87DataPolicy.cap5,P4AOriginalFull87DataPolicy.cap4,fifth_prior,
    ← fourth_prior d N (rosserAncestor 4 pre),prior_ancestor d N pre 4 (by decide),
    P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor d N 4 (by decide)] <;> rfl

theorem cap6_prior (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    cap6 (prior d N pre) d N n pre=P4AOriginalFull87DataPolicy.licensedCap n d N pre := by
  simp only [cap6,P4AOriginalFull87DataPolicy.licensedCap,accepted,P4AOriginalFull87DataPolicy.Accepted,
    eligible_prior,← cap5_prior n d N (rosserAncestor 5 pre),prior_ancestor d N pre 5 (by decide)]

theorem five_prior (n : ℕ) (d : OriginalData) (N : ℝ) (pos : Bool) (pre : List ℕ) :
    five (prior d N pre) d N n pos pre=P4AOriginalFull87DataPolicy.fifthPolicy n d N pos pre := by
  simp only [five,P4AOriginalFull87DataPolicy.fifthPolicy,firstExitDepthSplicePolicy,
    frozenParityRosserPolicy,ancestorFrozenPolicy,common_prior,P4AOriginalFull87DataPolicy.level5Exponent,
    ← cap5_prior n d N (rosserAncestor 5 pre),← fifth_prior d N (rosserAncestor 5 pre),
    prior_ancestor d N pre 5 (by decide),P4AOriginalFull87DataPolicy.active_ancestor d N 5 (by decide)] <;> rfl

theorem six_prior (n : ℕ) (d : OriginalData) (N : ℝ) (pos : Bool) (pre : List ℕ) :
    six (prior d N pre) d N n pos pre=P4AOriginalFull87DataPolicy.sixthPolicy n d N pos pre := by
  simp only [six,P4AOriginalFull87DataPolicy.sixthPolicy,firstExitDepthSplicePolicy,
    frozenParityRosserPolicy,ancestorFrozenPolicy,five_prior,P4AOriginalFull87DataPolicy.level6Exponent,
    P4AOriginalFull87DataPolicy.currentSixthExponent,← cap6_prior n d N (rosserAncestor 6 pre),
    ← after_prior d N (rosserAncestor 6 pre) 8,prior_ancestor d N pre 6 (by decide),
    P4AOriginalFull87DataPolicy.active_ancestor d N 6 (by decide)] <;> rfl

theorem original_evaluation (delta : ℝ) (n : ℕ) (d : OriginalData) (N : ℝ)
    (pos : Bool) (pre : List ℕ) :
    eight (prior d N pre) d N delta n pos pre=P4AOriginalFull87DataPolicy.policy delta n d N pos pre := by
  simp only [eight,P4AOriginalFull87DataPolicy.policy,P4AOriginalFull87DataPolicy.eighthContinuation,
    firstExitDepthSplicePolicy,six_prior]

/-- A historical source owner stays on its literal cap and retains the
old mode when the physical cutoff lies below the historical coarse
cutoff. This is a one-sided parameter restriction available after a. -/
theorem root_on_old_owner {d : OriginalData} (he : 0≤(d.e:ℝ)) {omega N : ℝ}
    (hN : 1≤N) (hwa : omega≤d.omega) {pre : List ℕ}
    (h : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N pre) :
    current d omega N pre=prior d N pre := by
  let h3 := rosserAncestor 3 pre
  let t := primeHistoryLogCoordinates N 3 h3
  obtain ⟨hactive,j,hj,ht⟩ := h
  have hs := (HistoricalThirdCoarse.mem_cells _ _ _ _).mp hj
  have hp := (P4AOriginalOrderedThirdAgreement.old_rectangle hj t).mpr (HistoricalThirdCoarse.inBox_of_cell ht)
  have hh := P4AOriginalOrderedThirdAgreement.hi_cast d.m j 0
  have hret : j ∈ retained (d.e:ℝ) d.m := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,⟨t,hp⟩,hh ▸ hs.2.2.2.2.1⟩
  have hnew : HistoricalThirdCoarse.active omega N h3 :=
    ⟨hactive.1,(Real.rpow_le_rpow_of_exponent_le hN hwa).trans hactive.2⟩
  have hold : P1ThirdFallbackSupport.supported d.e d.chi d.m d.omega N h3 := ⟨hactive,j,hj,ht⟩
  have hex : ∃ i∈retained (d.e:ℝ) d.m, t∈logPrimeMeshCell 0 (19/96) d.m i := ⟨j,hret,ht⟩
  have hval := P4AOriginalOrderedThirdAgreement.old_owner_level he hj
  simp only [current,prior,P4AOriginalOrderedThirdTable.rawExponent,hnew,if_true,
    P4AOriginalOrderedThirdTable.atPoint_on_cell hret ht,hval,
    P5OriginalCommonRefinedConstructor.originalSeed,P1OriginalVariableFourthContinuation.seedExponent,
    P1CoarseFirstCubeFallbackMargin.effectiveExponent,hold,HistoricalThirdCoarse.exponent_on_cell _ _ _ _ j hj ht,
    P4AOriginalFull87DataPolicy.active,hex,true_and,and_true]

theorem policy_on_old_owner {d : OriginalData} (he : 0≤(d.e:ℝ)) {omega N : ℝ}
    (hN : 1≤N) (hwa : omega≤d.omega) {pre : List ℕ}
    (h : P1ThirdFallbackSupport.frozenSupported d.e d.chi d.m d.omega N pre)
    (delta : ℝ) (n : ℕ) (pos : Bool) :
    policy delta n d omega N pos pre=P4AOriginalFull87DataPolicy.policy delta n d N pos pre := by
  rw [policy,root_on_old_owner he hN hwa h,original_evaluation]

end
end ImbalancedChen.P4AOriginalOrderedThirdFullPolicy
