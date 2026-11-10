import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy

/-! Original chronology evaluated on its actual fourth/fifth bank.
The three classes of sixth action share their existing source tests,
endpoints and chronological predecessor. Finite labels use the own
third activation and the rounded licensed-sixth filter. -/
namespace ImbalancedChen.P4AOriginalFull87DataPolicy
noncomputable section
open scoped Classical BigOperators
open VariableEnvelope P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalCompleteSixthChronology (laterEligible applyLater)
open P4AOriginalSixthActionBank (Action allActions endpoint selected)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap)
open P1QuantizedActionLicense (LowerLicense)

def savedEligible (d : OriginalData) (N : ℝ) (i : P4AOriginalSavedSixthArchive.Row)
    (pre : List ℕ) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  pre.length = 6 ∧ P4AOriginalSavedSixthArchive.Source i t ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H3 t < lambda3 d N pre ∧
    Certificates.P2OriginalSixthElevenLogSemantics.H5 t < lambda3 d N pre ∧
    actualParent5 d N pre ≤ P4AOriginalSavedSixthArchive.oldUpper i t

def savedExponent (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax Finset.univ (fun i => savedEligible d N i pre)
    (fun i => P4AOriginalSavedSixthArchive.endpoint i (primeHistoryLogCoordinates N 6 pre))
    (actualParent5 d N pre)

def elevenExponent (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset
    (fun c => eligibleSixth d N c pre)
    (fun c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c (primeHistoryLogCoordinates N 6 pre))
    (savedExponent d N pre)

def afterLater (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℕ → ℝ
  | 0 => elevenExponent d N pre
  | k+1 => applyLater k N (afterLater d N pre k) pre

def currentSixthExponent (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ := afterLater d N pre 8

theorem afterLater_mono (d : OriginalData) (N : ℝ) (pre : List ℕ) : Monotone (afterLater d N pre) := by
  apply monotone_nat_of_le_succ
  intro k
  exact finiteMax_seed_le _ _ _ _

theorem fifth_le_current (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    actualParent5 d N pre ≤ currentSixthExponent d N pre :=
  (show actualParent5 d N pre ≤ savedExponent d N pre from finiteMax_seed_le _ _ _ _).trans
    ((show savedExponent d N pre ≤ elevenExponent d N pre from finiteMax_seed_le _ _ _ _).trans
      (afterLater_mono d N pre (show 0 ≤ 8 by omega)))

/-- Each chronological raw candidate has a nonempty first-six mask.
This bound uses whichever of the source guards is true at this actual
bank's current value. -/
theorem current_le_of_subset_tents (d : OriginalData) (N R : ℝ) (pre : List ℕ)
    (hfifth : actualParent5 d N pre ≤ R)
    (htents : ∀ m ∈ Finset.Icc 1 63,
      v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum m (primeHistoryLogCoordinates N 6 pre)) ≤ R) :
    currentSixthExponent d N pre ≤ R := by
  have hsaved : savedExponent d N pre ≤ R := by
    apply finiteMax_le _ _ _ _ _ hfifth
    intro i _ hi
    exact htents (P4AOriginalSavedSixthArchive.selectedMask i) (P4AOriginalSavedSixthArchive.source_mask_range i _ hi.2.1)
  have heleven : elevenExponent d N pre ≤ R := by
    apply finiteMax_le _ _ _ _ _ hsaved
    intro c _ hc
    have hl : Certificates.P2OriginalSixthElevenLogSemantics.newCap c (primeHistoryLogCoordinates N 6 pre) <
        v (Certificates.P2OriginalSixthElevenLogSemantics.selectedSum c.selectedMask (primeHistoryLogCoordinates N 6 pre)) := by
      rw [v_eq_min]
      dsimp only [A,C]
      exact lt_min hc.2.1.selectedAscending (by linarith [hc.2.1.selectedDescending])
    exact hl.le.trans (htents c.selectedMask (by cases c <;> norm_num [Certificates.P2OriginalSixthElevenLogSemantics.Cell.selectedMask]))
  have hstage (k : ℕ) : afterLater d N pre k ≤ R := by
    induction k with
    | zero => exact heleven
    | succ k ih =>
      apply finiteMax_le _ _ _ _ _ ih
      intro c _ hc
      exact (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c _ hc.2.2.1).le.trans
        (htents (P4AOriginalSixthLaterLiteral.mask c) (P4AOriginalSixthLaterSemantics.original_mask_range c))
  exact hstage 8

def ActualEligible (d : OriginalData) (N : ℝ) (pre : List ℕ) : Action → Prop
  | .saved i => savedEligible d N i pre
  | .eleven c => eligibleSixth d N c pre
  | .later c => laterEligible (P4AOriginalSixthLaterLiteral.stage c)
      (afterLater d N pre (P4AOriginalSixthLaterLiteral.stage c)) N c pre

def Accepted (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) (a : Action) : Prop :=
  let t := primeHistoryLogCoordinates N 6 pre
  ActualEligible d N pre a ∧ LowerLicense (selected a) t (rounded n (endpoint a t) : ℝ) ∧
    (rounded n (endpoint a t) : ℝ) + width n ≤ VariableEnvelope.v (∑ j ∈ selected a, t j)

def cap4 (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  protect n (originalSeed d N pre) (exponent4 d N pre)

def cap5 (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  max (cap4 n d N (rosserAncestor 4 pre)) (rounded n (exponent5 d N pre) : ℝ)

def licensedCap (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  finiteMax allActions (Accepted n d N pre)
    (fun a => (rounded n (endpoint a (primeHistoryLogCoordinates N 6 pre)) : ℝ))
    (cap5 n d N (rosserAncestor 5 pre))

def active (d : OriginalData) (N : ℝ) (pre : List ℕ) : Prop :=
  primeHistoryLogCoordinates N 3 (rosserAncestor 3 pre) 0 ≤ mu ∧
    P1ThirdFallbackSupport.supported (d.e : ℝ) d.chi d.m d.omega N (rosserAncestor 3 pre)

def level4Exponent (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if active d N pre then cap4 n d N pre else exponent4 d N pre

def level5Exponent (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if active d N pre then cap5 n d N pre else exponent5 d N pre

def level6Exponent (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  if active d N pre then licensedCap n d N pre else currentSixthExponent d N pre

def fourthPolicy (n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (common3 d N)
    (frozenParityRosserPolicy false 4 (fun h => N ^ level4Exponent n d N h))

def fifthPolicy (n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 4 (common3 d N)
    (frozenParityRosserPolicy false 5 (fun h => N ^ level5Exponent n d N h))

def sixthPolicy (n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 6 (fifthPolicy n d N)
    (frozenParityRosserPolicy false 6 (fun h => N ^ level6Exponent n d N h))

def eighthContinuation (delta : ℝ) (n : ℕ) (d : OriginalData) (N : ℝ)
    (positive : Bool) (pre : List ℕ) : Bool :=
  match selectedCap delta n N pre with
  | none => sixthPolicy n d N positive pre
  | some a => ordinaryParityRosserPolicy false (N ^ (a : ℝ)) positive pre

def policy (delta : ℝ) (n : ℕ) (d : OriginalData) (N : ℝ) : Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 (sixthPolicy n d N) (eighthContinuation delta n d N)

def actualParent (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) : ℝ :=
  level6Exponent n d N (rosserAncestor 6 pre)

theorem old_afterLater (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) (k : ℕ) :
    afterLater (P4AOriginalCompleteSixthChronology.data e q om) N pre k =
      P4AOriginalCompleteSixthChronology.afterLater e q om N pre k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [afterLater,P4AOriginalCompleteSixthChronology.afterLater,ih]

theorem old_actualEligible (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) (a : Action) :
    ActualEligible (P4AOriginalCompleteSixthChronology.data e q om) N pre a ↔
      P4AOriginalSixthActionBank.ActualEligible e q om N pre a := by
  cases a with
  | saved i => rfl
  | eleven c => rfl
  | later c => simp only [ActualEligible,P4AOriginalSixthActionBank.ActualEligible,old_afterLater]

theorem old_licensedCap (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    licensedCap n (P4AOriginalCompleteSixthChronology.data e q om) N pre =
      P4AOriginalSixthLicensedFilter.licensedCap n e q om N pre := by
  unfold licensedCap P4AOriginalSixthLicensedFilter.licensedCap
  have he : Accepted n (P4AOriginalCompleteSixthChronology.data e q om) N pre =
      P4AOriginalSixthLicensedFilter.Accepted n e q om N pre := by
    funext a
    apply propext
    simp only [Accepted,P4AOriginalSixthLicensedFilter.Accepted,old_actualEligible]
  rw [he] <;> rfl

theorem old_level6 (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) :
    level6Exponent n (P4AOriginalCompleteSixthChronology.data e q om) N pre =
      P4AOriginalFull87LicensedSixthPolicy.level6Exponent n e q om N pre := by
  simp only [level6Exponent,P4AOriginalFull87LicensedSixthPolicy.level6Exponent,
    currentSixthExponent,P4AOriginalCompleteSixthChronology.currentSixthExponent,
    old_licensedCap,old_afterLater] <;> rfl

theorem old_sixthPolicy (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) :
    sixthPolicy n (P4AOriginalCompleteSixthChronology.data e q om) N =
      P4AOriginalFull87LicensedSixthPolicy.sixthPolicy n e q om N := by
  simp only [sixthPolicy,P4AOriginalFull87LicensedSixthPolicy.sixthPolicy,old_level6] <;> rfl

theorem old_policy (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) :
    policy delta n (P4AOriginalCompleteSixthChronology.data e q om) N =
      P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om N := by
  simp only [policy,P4AOriginalFull87LicensedSixthPolicy.policy,eighthContinuation,
    P4AOriginalFull87LicensedSixthPolicy.eighthContinuation,old_sixthPolicy]

theorem cap5_eq_protect (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    cap5 n d N pre = protect n (originalSeed d N pre) (exponent5 d N pre) := by
  unfold cap5 cap4
  rw [P4AOriginalFull87FiniteParentCaps.originalSeed_ancestor _ _ 4 (by decide)]
  exact protect_nested n _ _ _ (inherited4_le_exponent5 d N pre)

theorem cap5_le_licensed (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    cap5 n d N (rosserAncestor 5 pre) ≤ licensedCap n d N pre :=
  finiteMax_seed_le _ _ _ _

theorem active_ancestor (d : OriginalData) (N : ℝ) (k : ℕ) (hk : 3 ≤ k) (pre : List ℕ) :
    active d N (rosserAncestor k pre) ↔ active d N pre := by simp only [active,rosserAncestor_nested 3 k hk]

theorem fifth_even (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    fifthPolicy n d N true pre = true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 4 _ _
    (common3_even d N) (fun h => frozenParityRosserPolicy_upper_even 5 _ h) pre

theorem sixth_even (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    sixthPolicy n d N true pre = true :=
  UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 6 _ _
    (fifth_even n d N) (fun h => frozenParityRosserPolicy_upper_even 6 _ h) pre

theorem policy_even (delta : ℝ) (n : ℕ) (d : OriginalData) (N : ℝ) (pre : List ℕ) :
    policy delta n d N true pre = true := by
  apply UpperPolicyFiniteBridge.firstExitDepthSplicePolicy_even_retained 8 _ _ (sixth_even n d N) _ pre
  intro h
  unfold eighthContinuation
  cases selectedCap delta n N h
  · exact sixth_even n d N h
  · simp [ordinaryParityRosserPolicy,oddFirstExitPolicy]

end
end ImbalancedChen.P4AOriginalFull87DataPolicy
