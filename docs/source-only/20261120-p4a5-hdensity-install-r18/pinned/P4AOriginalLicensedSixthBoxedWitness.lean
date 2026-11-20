import ImbalancedChen.P4AOriginalLicensedSixthAffineProgram

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

A winning witness for the FILTERED already-rounded maximum. Requiring
attainment of the OLD raw complete maximum would be wrong after rejecting
its unlicensed maximizer. One original accepted action, or genuine fifth
inheritance, is selected without altering the policy or its occurrence list.
-/
namespace ImbalancedChen.P4AOriginalLicensedSixthBoxedWitness
noncomputable section
open scoped Classical BigOperators
open Set
open P1FiniteAffineDecisionProgram P1FiniteAffineQuantizerTable P1AffineTaggedDecision
open P4AOriginalFourthFifthAffinePrograms P1OriginalVariableFourthContinuation
open P5OriginalCommonRefinedConstructor P4AOriginalCompleteSixthChronology
open P4AOriginalSixthActionBank P4AOriginalSixthLicensedFilter
open P4AOriginalFull87FiniteParentCaps P1GuardFrozenFiniteCapAlgebra
open P4AOriginalSixthTaggedWinner (entries mem_entries finiteFifth finiteFifth_at_history)
open P4AOriginalLicensedSixthAffineProgram
open P1QuantizedActionLicense (LowerLicense)
open P4AOriginalFull87HistoryCore (width)
open P1AffineCertifiedMesh P1AffineCertifiedLookup

/-- Equalities here compare ALREADY-ROUNDED accepted outputs with the NEW
maximum. No assertion about attaining the old raw maximum is made. -/
def witnessTests (n : ℕ) (d : OriginalData) (b : ℚ) (a : Entry) : List (Gate 6) :=
  tests n d b a.val ++
    [LE (candidate n a.val) (program n d b),
     LE (program n d b) (candidate n a.val)]

theorem witnessTests_exact (n : ℕ) (d : OriginalData) (b : ℚ)
    (t : Fin 6 → ℝ) (a : Entry) :
    Passed t (witnessTests n d b a) ↔
      PointAccepted n d b t a.val ∧
      (program n d b).eval t = (rounded n (endpoint a.val t) : ℝ) := by
  simp only [witnessTests, passed_append, tests_exact, passed_cons, passed_nil,
    holds_LE, candidate_exact, and_true]
  constructor
  · rintro ⟨ha,hlo,hhi⟩
    exact ⟨ha,le_antisymm hhi hlo⟩
  · rintro ⟨ha,h⟩
    exact ⟨ha,h.ge,h.le⟩

def decision (n : ℕ) (d : OriginalData) (b : ℚ) : Trace 6 (Option Entry) :=
  .branch (LT (finiteFifth n d b) (program n d b))
    (firstWitness (witnessTests n d b) entries) (.leaf none)

theorem decision_some_sound (n : ℕ) (d : OriginalData) (b : ℚ)
    (t : Fin 6 → ℝ) (a : Entry) (ha : (decision n d b).eval t = some a) :
    (finiteFifth n d b).eval t < (program n d b).eval t ∧
      PointAccepted n d b t a.val ∧
      (program n d b).eval t = (rounded n (endpoint a.val t) : ℝ) := by
  rw [decision, Trace.eval, holds_LT] at ha
  split_ifs at ha with hstrict
  · have hw := (firstWitness_sound (witnessTests n d b) entries t a ha).2
    exact ⟨hstrict,(witnessTests_exact n d b t a).mp hw⟩
  · simp only [Trace.eval] at ha
    cases ha

theorem decision_exists_of_strict (n : ℕ) (d : OriginalData) (b : ℚ)
    (t : Fin 6 → ℝ)
    (hstrict : (finiteFifth n d b).eval t < (program n d b).eval t) :
    ∃ a : Entry, (decision n d b).eval t = some a := by
  have h := finiteMax_attained allActions (PointAccepted n d b t)
    (fun a => (rounded n (endpoint a t) : ℝ)) ((finiteFifth n d b).eval t)
  rw [← program_eval] at h
  rcases h with hinherit | ⟨a,ha,haccept,hvalue⟩
  · rw [hinherit] at hstrict
    exact (lt_irrefl _ hstrict).elim
  · let entry : Entry := ⟨a,ha⟩
    have hw : Passed t (witnessTests n d b entry) :=
      (witnessTests_exact n d b t entry).mpr ⟨haccept,hvalue⟩
    obtain ⟨chosen,hchosen⟩ := firstWitness_exists (witnessTests n d b) entries t
      ⟨entry,mem_entries entry,hw⟩
    refine ⟨chosen,?_⟩
    rw [decision, Trace.eval, holds_LT, if_pos hstrict]
    exact hchosen

/-- none means equality with the REAL finite fifth seed. It cannot hide
an accepted strict update, including when the raw maximizer was rejected. -/
theorem decision_none_iff (n : ℕ) (d : OriginalData) (b : ℚ) (t : Fin 6 → ℝ) :
    (decision n d b).eval t = none ↔
      (program n d b).eval t = (finiteFifth n d b).eval t := by
  have hseed : (finiteFifth n d b).eval t ≤ (program n d b).eval t := by
    rw [program_eval]
    exact finiteMax_seed_le _ _ _ _
  constructor
  · intro hn
    have hnot : ¬(finiteFifth n d b).eval t < (program n d b).eval t := by
      intro hstrict
      obtain ⟨a,ha⟩ := decision_exists_of_strict n d b t hstrict
      rw [hn] at ha
      cases ha
    exact le_antisymm (le_of_not_gt hnot) hseed
  · intro heq
    rw [decision, Trace.eval, holds_LT, heq, if_neg (lt_irrefl _)]
    rfl

/-- Exact arithmetic specialization, with the same old third value in
both meanings. The full87 supplier below derives these seed identities. -/
theorem some_at_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) (m : ℕ) (a : Entry)
    (ha : (decision n (data e q om) b).lookup m
      (primeHistoryLogCoordinates N 6 pre) = some a) :
    Accepted n e q om N pre a.val ∧
      licensedCap n e q om N pre =
        (rounded n (endpoint a.val (primeHistoryLogCoordinates N 6 pre)) : ℝ) ∧
      LowerLicense (selected a.val) (primeHistoryLogCoordinates N 6 pre)
        (licensedCap n e q om N pre) ∧
      licensedCap n e q om N pre + width n ≤
        VariableEnvelope.v (∑ i ∈ selected a.val, primeHistoryLogCoordinates N 6 pre i) := by
  rw [Trace.lookup_exact] at ha
  obtain ⟨_,hacc,hval⟩ := decision_some_sound n (data e q om) b _ a ha
  have hactual : Accepted n e q om N pre a.val :=
    (tests_at_history n e q om N b pre hlen hb a.val).mp
      ((tests_exact n (data e q om) b _ a.val).mpr hacc)
  rw [program_at_history n e q om N b pre hlen hb hseed] at hval
  exact ⟨hactual,hval,hval.symm ▸ hactual.2.1,hval.symm ▸ hactual.2.2⟩

/-- Both the scalar and provenance share ONE own-sixth label. Every point
of the CLOSED rectangle has that value/tag; if tagged, its own full lower
licence and selected-tent debit hold everywhere, with NO safe-stratum input.
The raw test statement is algebraic until specialized to an actual history. -/
def CertifiedBox (n : ℕ) (d : OriginalData) (b : ℚ) (m : ℕ)
    (t : Fin 6 → ℝ) : Prop :=
  ∃ j ∈ approved (program n d b) m,
    j ∈ approved (decision n d b).code m ∧ t ∈ cell m j ∧
    ∃ v ∈ outputAlphabet n b, ∀ u : Fin 6 → ℝ,
      (∀ i, lo m j i ≤ u i) → (∀ i, u i ≤ hi m j i) →
        valueLookup n d b m u = (v : ℝ) ∧
        (decision n d b).eval u = (decision n d b).lookup m t ∧
        (∀ a : Entry, (decision n d b).lookup m t = some a →
          PointAccepted n d b u a.val ∧
          (v : ℝ) = (rounded n (endpoint a.val u) : ℝ) ∧
          LowerLicense (selected a.val) u (v : ℝ) ∧
          (v : ℝ) + width n ≤ VariableEnvelope.v (∑ i ∈ selected a.val, u i))

theorem certifiedBox_of_covered (n : ℕ) (d : OriginalData) (b : ℚ)
    (m : ℕ) (t : Fin 6 → ℝ)
    (hv : t ∈ covered (program n d b) m)
    (ht : t ∈ covered (decision n d b).code m) : CertifiedBox n d b m t := by
  obtain ⟨hcube,hjt⟩ := (mem_covered_iff (decision n d b).code m t).mp ht
  have hjv := ((mem_covered_iff (program n d b) m t).mp hv).2
  have hcell := gridLabel_mem m t hcube
  obtain ⟨v,hv,hvalue⟩ := value_closed_box n d b m (gridLabel m t) hjv
  have hcert := (mem_approved _ _ _).mp hjt
  have hb := mem_logPrimeMeshCell.mp hcell
  have htag := (decision n d b).tag_on_closed_box _ _ _ hcert t
    (fun i => (hb i).1) (fun i => (hb i).2.le)
  refine ⟨gridLabel m t,hjv,hjt,hcell,v,hv,?_⟩
  intro u hl hu
  have hs := hvalue u hl hu
  have htu : (decision n d b).eval u = (decision n d b).lookup m t := by
    rw [Trace.lookup_exact,htag]
    exact (decision n d b).tag_on_closed_box _ _ _ hcert u hl hu
  refine ⟨hs,htu,?_⟩
  intro a ha
  obtain ⟨_,hacc,heq⟩ := decision_some_sound n d b u a (htu.trans ha)
  have hscalar : (program n d b).eval u = (v : ℝ) := by
    simpa only [valueLookup_exact] using hs
  have hvround : (v : ℝ) = (rounded n (endpoint a.val u) : ℝ) :=
    hscalar.symm.trans heq
  exact ⟨hacc,hvround,hvround.symm ▸ hacc.2.1,hvround.symm ▸ hacc.2.2⟩

/-- Neither scalar nor tag can read a later descendant coordinate. -/
theorem own_ancestor_frozen (n : ℕ) (d : OriginalData) (b : ℚ) (m : ℕ)
    (N : ℝ) (pre later : List ℕ) (hlen : 6 ≤ pre.length) :
    valueLookup n d b m (primeHistoryLogCoordinates N 6 (rosserAncestor 6 (later ++ pre))) =
      valueLookup n d b m (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) ∧
    (decision n d b).lookup m
      (primeHistoryLogCoordinates N 6 (rosserAncestor 6 (later ++ pre))) =
      (decision n d b).lookup m (primeHistoryLogCoordinates N 6 (rosserAncestor 6 pre)) := by
  rw [rosserAncestor_append 6 later pre hlen]
  exact ⟨rfl,rfl⟩

end
end ImbalancedChen.P4AOriginalLicensedSixthBoxedWitness
