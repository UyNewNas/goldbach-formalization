import ImbalancedChen.P1AffineTaggedDecision
import ImbalancedChen.P4AOriginalFull87SixthMarginIntegration

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A deterministic provenance tag for the SAME finite sixth cap. Every
candidate uses the ORIGINAL actual chronological tests and must attain
its RAW complete-sixth maximum. The tag is none unless the finite cap
strictly improves its finite fifth predecessor. Ties use one fixed
pre-N enumeration solely to select a witness; no sieve decision changes.
-/
namespace ImbalancedChen.P4AOriginalSixthTaggedWinner
noncomputable section
open scoped Classical BigOperators
open P1FiniteAffineDecisionProgram P1AffineTaggedDecision P1FiniteAffineQuantizerTable
open P4AOriginalFourthFifthAffinePrograms P4AOriginalCompleteSixthAffinePrograms
open P4AOriginalSixthActionBank P4AOriginalSixthWinningAction
open P4AOriginalCompleteSixthChronology P5OriginalCommonRefinedConstructor
open P5OriginalCommonRefinedPreservation P4AOriginalFull87FiniteParentCaps
open P1GuardFrozenFiniteCapAlgebra
open P4AOriginalFull87AffineGuardRealization

/-- This finite ordering is frozen once, before e,q,n,N or any tuple.
It is NOT claimed to be the archive's unspecified maximizing-row tie rule. -/
def entries : List Entry := (Finset.univ : Finset Entry).toList

theorem mem_entries (a : Entry) : a ∈ entries := by simp [entries]

def actionCode : Action → Program 6
  | .saved i => savedEndpoint i
  | .eleven c => atom (elevenNewA c)
  | .later c => atom (laterEndpointA c)

def actionTests (d : OriginalData) (b : ℚ) : Action → List (Gate 6)
  | .saved i => savedTests d b i
  | .eleven c => elevenTests d b c
  | .later c => laterTests (P4AOriginalSixthLaterLiteral.stage c)
      (afterProgram d b (P4AOriginalSixthLaterLiteral.stage c)) c

theorem actionCode_exact (a : Action) (t : Fin 6 → ℝ) :
    (actionCode a).eval t = endpoint a t := by
  cases a with
  | saved i => exact savedEndpoint_exact i t
  | eleven c => exact elevenNewA_exact c t
  | later c => exact laterEndpointA_exact c t

/-- The original raw current is expanded, never rerun on a rounded cap. -/
theorem actionTests_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ)) (a : Action) :
    Passed (primeHistoryLogCoordinates N 6 pre) (actionTests (data e q om) b a) ↔
      ActualEligible e q om N pre a := by
  have hf := fifthAtSix_at_history (data e q om) b N pre hlen hb
  cases a with
  | saved i =>
      simpa only [actionTests, ActualEligible, savedEligible, hlen, true_and,
        hb, hf, fifth] using savedTests_exact (data e q om) b i
          (primeHistoryLogCoordinates N 6 pre)
  | eleven c =>
      simpa only [actionTests, ActualEligible, eligibleSixth, hlen, true_and, hf]
        using elevenTests_exact (data e q om) b c (primeHistoryLogCoordinates N 6 pre)
  | later c =>
      have hp := afterProgram_at_history e q om N b pre hlen hb
        (P4AOriginalSixthLaterLiteral.stage c)
      simpa only [actionTests, ActualEligible, laterEligible, hlen, true_and, hp]
        using laterTests_exact (P4AOriginalSixthLaterLiteral.stage c)
          (afterProgram (data e q om) b (P4AOriginalSixthLaterLiteral.stage c)) c
          (primeHistoryLogCoordinates N 6 pre)

/-- Exact RAW attainment is checked by two nonstrict comparisons.
No uniqueness of the original maximum is required. -/
def witnessTests (d : OriginalData) (b : ℚ) (a : Entry) : List (Gate 6) :=
  actionTests d b a.val ++
    [LE (actionCode a.val) (completeProgram d b),
     LE (completeProgram d b) (actionCode a.val)]

theorem witnessTests_at_history (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ)) (a : Entry) :
    Passed (primeHistoryLogCoordinates N 6 pre) (witnessTests (data e q om) b a) ↔
      ActualEligible e q om N pre a.val ∧
      currentSixthExponent e q om N pre = endpoint a.val (primeHistoryLogCoordinates N 6 pre) := by
  rw [witnessTests, passed_append, actionTests_at_history e q om N b pre hlen hb]
  simp only [passed_cons, passed_nil, holds_LE, actionCode_exact,
    completeProgram_at_history e q om N b pre hlen hb, and_true]
  constructor
  · rintro ⟨ha,hlo,hhi⟩
    exact ⟨ha,le_antisymm hhi hlo⟩
  · rintro ⟨ha,hval⟩
    exact ⟨ha,hval.ge,hval.le⟩

def finiteFifth (n : ℕ) (d : OriginalData) (b : ℚ) : Program 6 :=
  protectedProgram n b (fifthAtSix d b)
def finiteSixth (n : ℕ) (d : OriginalData) (b : ℚ) : Program 6 :=
  protectedProgram n b (completeProgram d b)

def decision (n : ℕ) (d : OriginalData) (b : ℚ) : Trace 6 (Option Entry) :=
  .branch (LT (finiteFifth n d b) (finiteSixth n d b))
    (firstWitness (witnessTests d b) entries) (.leaf none)

def code (n : ℕ) (d : OriginalData) (b : ℚ) : Program 6 := (decision n d b).code

theorem finiteFifth_at_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) :
    (finiteFifth n (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      cap5 n e q om N (rosserAncestor 5 pre) := by
  rw [finiteFifth, protectedProgram_exact,
    fifthAtSix_at_history (data e q om) b N pre hlen hb,
    cap5_eq_protect, originalSeed_ancestor _ _ 5 (by decide), hseed]
  rfl

theorem finiteSixth_at_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) :
    (finiteSixth n (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      cap6 n e q om N pre := by
  rw [finiteSixth, protectedProgram_exact,
    completeProgram_at_history e q om N b pre hlen hb, cap6_eq_protect, hseed]

/-- Some a means strict finite improvement AND actual raw attainment by
that very a. The witness is not substituted by an unrelated mask. -/
theorem decision_some_sound (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) (a : Entry)
    (ha : (decision n (data e q om) b).eval
      (primeHistoryLogCoordinates N 6 pre) = some a) :
    cap5 n e q om N (rosserAncestor 5 pre) < cap6 n e q om N pre ∧
      ActualEligible e q om N pre a.val ∧
      currentSixthExponent e q om N pre = endpoint a.val (primeHistoryLogCoordinates N 6 pre) ∧
      cap6 n e q om N pre = (rounded n (endpoint a.val (primeHistoryLogCoordinates N 6 pre)) : ℝ) := by
  rw [decision, Trace.eval, holds_LT,
    finiteFifth_at_history n e q om N b pre hlen hb hseed,
    finiteSixth_at_history n e q om N b pre hlen hb hseed] at ha
  split_ifs at ha with hwin
  · have hw := (firstWitness_sound (witnessTests (data e q om) b) entries _ a ha).2
    obtain ⟨hel,hraw⟩ := (witnessTests_at_history e q om N b pre hlen hb a).mp hw
    have hbase : originalSeed (data e q om) N pre ≤
        cap5 n e q om N (rosserAncestor 5 pre) := by
      rw [cap5_eq_protect, originalSeed_ancestor _ _ 5 (by decide)]
      exact seed_le_protect _ _ _
    have hstrict := hbase.trans_lt hwin
    rw [cap6_eq_protect,hraw] at hstrict
    have hr : originalSeed (data e q om) N pre <
        (rounded n (endpoint a.val (primeHistoryLogCoordinates N 6 pre)) : ℝ) := by
      simpa only [protect, lt_max_iff, lt_self_iff_false, false_or] using hstrict
    refine ⟨hwin,hel,hraw,?_⟩
    rw [cap6_eq_protect,hraw,protect,max_eq_right hr.le]
  · simp [Trace.eval] at ha

/-- Strict update cannot fall through to none: the earlier actual-current
attainment theorem discharges existence of a passing original action. -/
theorem decision_some_of_strict (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ))
    (hwin : cap5 n e q om N (rosserAncestor 5 pre) < cap6 n e q om N pre) :
    ∃ a : Entry, (decision n (data e q om) b).eval
      (primeHistoryLogCoordinates N 6 pre) = some a := by
  obtain ⟨a,ha,he,hraw,_⟩ := strict_update_winner n e q om N pre hwin
  let entry : Entry := ⟨a,ha⟩
  have hw : Passed (primeHistoryLogCoordinates N 6 pre)
      (witnessTests (data e q om) b entry) :=
    (witnessTests_at_history e q om N b pre hlen hb entry).mpr ⟨he,hraw⟩
  obtain ⟨chosen,hchosen⟩ := firstWitness_exists (witnessTests (data e q om) b)
    entries (primeHistoryLogCoordinates N 6 pre) ⟨entry,mem_entries entry,hw⟩
  refine ⟨chosen,?_⟩
  rw [decision, Trace.eval, holds_LT,
    finiteFifth_at_history n e q om N b pre hlen hb hseed,
    finiteSixth_at_history n e q om N b pre hlen hb hseed, if_pos hwin]
  exact hchosen

theorem decision_none_iff (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) :
    (decision n (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) = none ↔
      ¬cap5 n e q om N (rosserAncestor 5 pre) < cap6 n e q om N pre := by
  constructor
  · intro h hn
    obtain ⟨a,ha⟩ := decision_some_of_strict n e q om N b pre hlen hb hseed hn
    rw [h] at ha
    cases ha
  · intro h
    rw [decision, Trace.eval, holds_LT,
      finiteFifth_at_history n e q om N b pre hlen hb hseed,
      finiteSixth_at_history n e q om N b pre hlen hb hseed, if_neg h]
    rfl

/-- Source alone gives the original third entry at the own-sixth ancestor.
Neither a realized history nor a support/eligibility licence is an input. -/
theorem source_seed (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hlen : pre.length = 8)
    (c : P4AOriginalFull87SourceDictionary.Cell)
    (hs : P4AOriginalFull87SourceDictionary.Source c (primeHistoryLogCoordinates N 8 pre)) :
    ∃ b ∈ thirdAlphabet (data e q om).e (data e q om).chi (data e q om).m,
      originalSeed (data e q om) N pre = (b : ℝ) ∧
      originalSeed (data e q om) N (rosserAncestor 6 pre) = (b : ℝ) ∧
      lambda3 (data e q om) N (rosserAncestor 6 pre) = (b : ℝ) := by
  obtain ⟨b,hb,hseed,_,_,_⟩ := raw_codes_at_own_ancestors e q om N pre hlen c hs
  have h3 := P4AOriginalFull87CompleteSixthBound.actual_third_eq_original
    (data e q om) N pre hlen c hs
  change lambda3 (data e q om) N (rosserAncestor 4 pre) =
    originalSeed (data e q om) N pre at h3
  rw [lambda3_ancestor _ _ 4 (by decide)] at h3
  refine ⟨b,hb,hseed,?_,?_⟩
  · rw [originalSeed_ancestor _ _ 6 (by decide),hseed]
  · rw [lambda3_ancestor _ _ 6 (by decide),h3,hseed]

/-- An appended descendant cannot change its own-sixth trace query. -/
theorem decision_on_descendants (n : ℕ) (d : OriginalData) (b : ℚ) (N : ℝ)
    (pre later : List ℕ) (hlen : 6 ≤ pre.length) :
    (decision n d b).eval (primeHistoryLogCoordinates N 6
      (rosserAncestor 6 (later ++ pre))) =
    (decision n d b).eval (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
  rw [rosserAncestor_append 6 later pre hlen]

end
end ImbalancedChen.P4AOriginalSixthTaggedWinner
