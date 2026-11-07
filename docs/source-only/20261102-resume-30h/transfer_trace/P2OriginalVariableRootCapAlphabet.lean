import ImbalancedChen.P2CanonicalPairTentWarmHistory

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original U6 root is real and varies with both external primes. A
finite receiver with this root does NOT have the G fixed-rational-seed
alphabet. Its actual stored cap is either the original root or a selected
whole-box row value. This is proved for every computed run, including
short words and inherit choices; no accepted/fresh/support premise occurs.

The current sourceCheck excludes W. We prove that fact explicitly instead
of identifying this receiver with the missing adopted full W bank.
-/
namespace ImbalancedChen.P2OriginalVariableRootCapAlphabet

noncomputable section
open scoped Classical
open P2PhysicalIncomingPrefixCells P2LowerCapPlanIntegerRetention
open P2OriginalPairSourceReceiver P2OriginalPairRootRoughProducer
open P2OriginalSelectedPairNativeData P2CanonicalPairTentWarmHistory
open P2OriginalLowerWholeBoxBranchSelect (CandidateBank SelectedBranchData SourceForm)
open P2OriginalLowerSelectedCapConstructor (Code prefixCode)

abbrev SourceIndex (mesh : ℕ) := Fin 6 × Code mesh

/-- Values are computed from the actual selector and its literal prefix
code. The default zero only enlarges the wall catalogue at failed queries.
Neither seed, N, pair primes, nor an actual parent is an input. -/
def sourceHeight (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (reserve : ℚ) (i : SourceIndex mesh) : ℝ :=
  match select R bank reserve i.1 (prefixCode i.1.val i.2) with
  | none => 0
  | some b => (rowCap R (prefixCode i.1.val i.2) reserve b : ℝ)

/-- The incoming cap being frozen is deliberately distinct from the cap
used by the source's fresh check. Thus this finite-range fact cannot hide
a parent-provenance assumption. -/
theorem checkedChoice_freeze_cases (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (reserve : ℚ) (rank : Fin 6)
    (parent incoming : ℝ) (code : Code mesh) :
    (checkedChoice R bank reserve rank parent code).freeze incoming = incoming ∨
      (checkedChoice R bank reserve rank parent code).freeze incoming =
        sourceHeight R bank reserve (rank, code) := by
  cases hs : select R bank reserve rank (prefixCode rank.val code) with
  | none =>
      exact Or.inl (by simp [checkedChoice, hs, CapChoice.freeze])
  | some b =>
      by_cases hf : freshCheck R rank (prefixCode rank.val code) reserve parent b
      · exact Or.inr (by simp [checkedChoice, hs, hf, CapChoice.freeze, sourceHeight])
      · exact Or.inl (by simp [checkedChoice, hs, hf, CapChoice.freeze])

theorem pairPlan_choice_freeze_cases (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (reserve : ℚ) (seed incoming : ℝ)
    (rank : Fin 6) (code : Code mesh) :
    ((pairPlan R bank reserve seed).choose rank code).freeze incoming = incoming ∨
      ∃ i : SourceIndex mesh,
        ((pairPlan R bank reserve seed).choose rank code).freeze incoming =
          sourceHeight R bank reserve i := by
  fin_cases rank
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · rcases checkedChoice_freeze_cases R bank reserve 3 seed incoming code with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(3, code), h⟩
  · rcases checkedChoice_freeze_cases R bank reserve 4
        (cap3 R bank reserve seed code) incoming code with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(4, code), h⟩
  · rcases checkedChoice_freeze_cases R bank reserve 5
        (cap4 R bank reserve seed code) incoming code with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(5, code), h⟩

theorem step_cap_cases (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (reserve : ℚ) (seed : ℝ) (H : Trace) (x : ℝ) :
    (step (pairPlan R bank reserve seed) R.epsilon ceiling H x).cap = H.cap ∨
      ∃ i : SourceIndex mesh,
        (step (pairPlan R bank reserve seed) R.epsilon ceiling H x).cap =
          sourceHeight R bank reserve i := by
  change (planChoice (pairPlan R bank reserve seed) R.epsilon ceiling
    (H.word ++ [x])).freeze H.cap = H.cap ∨
      ∃ i : SourceIndex mesh,
        (planChoice (pairPlan R bank reserve seed) R.epsilon ceiling
          (H.word ++ [x])).freeze H.cap = sourceHeight R bank reserve i
  unfold planChoice
  split_ifs
  · exact pairPlan_choice_freeze_cases R bank reserve seed H.cap _ _
  · exact Or.inl rfl

theorem run_cap_cases (R : PairRange) {mesh : ℕ} (bank : CandidateBank mesh)
    (reserve : ℚ) (seed : ℝ) (H : Trace) (xs : List ℝ)
    (hH : H.cap = seed ∨ ∃ i : SourceIndex mesh, H.cap = sourceHeight R bank reserve i) :
    (run (pairPlan R bank reserve seed) R.epsilon ceiling H xs).cap = seed ∨
      ∃ i : SourceIndex mesh,
        (run (pairPlan R bank reserve seed) R.epsilon ceiling H xs).cap =
          sourceHeight R bank reserve i := by
  induction xs generalizing H with
  | nil => exact hH
  | cons x xs ih =>
      apply ih (step (pairPlan R bank reserve seed) R.epsilon ceiling H x)
      rcases step_cap_cases R bank reserve seed H x with h | h
      · simpa only [h] using hH
      · exact Or.inr h

/-- All actual prefixes, not only prefixes reaching a fresh fifth row. -/
theorem original_pair_prefix_cap_cases (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (buffer : ℚ) (sixth : Bool)
    (N : ℕ) (p : ℕ × ℕ) (xs : List ℝ) (j : ℕ) :
    let seed := rootSeed sixth buffer N p
    let H := run (pairPlan R bank (2*buffer) seed) R.epsilon ceiling
      (pairRoot N p seed) (xs.take j)
    H.cap = seed ∨ ∃ i : SourceIndex mesh, H.cap = sourceHeight R bank (2*buffer) i := by
  exact run_cap_cases R bank (2*buffer) (rootSeed sixth buffer N p)
    (pairRoot N p (rootSeed sixth buffer N p)) (xs.take j) (Or.inl rfl)

/-- A failed W licence is a real source restriction, not an equality to
the original full adopted bank. -/
theorem sourceCheck_excludes_W (R : PairRange) {mesh : ℕ} (rank : Fin 6)
    (code : Code mesh) (reserve : ℚ) (b : SelectedBranchData)
    (hb : sourceCheck R rank code reserve b) (slot : Fin 5) :
    b.form ≠ SourceForm.wSlot slot := by
  intro heq
  have h := hb.1
  rw [heq] at h
  fin_cases rank <;>
    simp [P2OriginalLowerWholeBoxBranchSelect.formRankEligible] at h

theorem selected_source_excludes_W (R : PairRange) {mesh : ℕ}
    (bank : CandidateBank mesh) (reserve : ℚ) (rank : Fin 6) (code : Code mesh)
    (b : SelectedBranchData) (hb : select R bank reserve rank code = some b)
    (slot : Fin 5) : b.form ≠ SourceForm.wSlot slot :=
  sourceCheck_excludes_W R rank (prefixCode rank.val code) reserve b
    (select_some_source R bank reserve rank code b hb).2 slot

def rootConstant : Fin 5 → ℝ :=
  ![1/2, 57/64, 1/2, 57/64, VariableEnvelope.B P5U6CausalLevelGeometry.a]

def rootTSlope : Fin 5 → ℝ := ![1/2, -(3/2), 1/2, -(3/2), 0]
def rootUSlope : Fin 5 → ℝ := ![0, 0, 1/2, -(3/2), 0]

/-- t is the larger external prime and the first chronological slot. -/
def rootPlane (i : Fin 5) (u t : ℝ) : ℝ :=
  rootConstant i + rootTSlope i * t + rootUSlope i * u

/-- The actual t<mu switch is kept. Membership only enlarges its finite
alphabet; it does not replace the original piecewise root by its maximum. -/
theorem original_U6_root_plane (u t : ℝ) :
    ∃ i : Fin 5, P5U6CausalLevelGeometry.physicalLevel u t = rootPlane i u t := by
  have tent (s : ℝ) : VariableEnvelope.v s = VariableEnvelope.A s ∨
      VariableEnvelope.v s = VariableEnvelope.C s := by
    rw [VariableEnvelope.v_eq_min]
    rcases le_total (VariableEnvelope.A s) (VariableEnvelope.C s) with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (min_eq_right h)
  have maximum (a b : ℝ) : max a b = a ∨ max a b = b := by
    rcases le_total b a with h | h
    · exact Or.inl (max_eq_left h)
    · exact Or.inr (max_eq_right h)
  have hp : P5U6CausalLevelGeometry.physicalLevel u t = VariableEnvelope.v t ∨
      P5U6CausalLevelGeometry.physicalLevel u t = VariableEnvelope.v (t+u) ∨
      P5U6CausalLevelGeometry.physicalLevel u t =
        VariableEnvelope.B P5U6CausalLevelGeometry.a := by
    unfold P5U6CausalLevelGeometry.physicalLevel
    split_ifs
    · rcases maximum (VariableEnvelope.v t)
          (max (VariableEnvelope.v (t+u)) (VariableEnvelope.B P5U6CausalLevelGeometry.a))
          with h | h
      · exact Or.inl h
      · rcases maximum (VariableEnvelope.v (t+u))
            (VariableEnvelope.B P5U6CausalLevelGeometry.a) with h' | h'
        · exact Or.inr (Or.inl (h.trans h'))
        · exact Or.inr (Or.inr (h.trans h'))
    · exact Or.inl rfl
  rcases hp with h | h | h
  · rcases tent t with ht | ht
    · refine ⟨0, ?_⟩
      rw [h, ht]
      dsimp [rootPlane, rootConstant, rootTSlope, rootUSlope, VariableEnvelope.A]
      ring
    · refine ⟨1, ?_⟩
      rw [h, ht]
      dsimp [rootPlane, rootConstant, rootTSlope, rootUSlope, VariableEnvelope.C]
      ring
  · rcases tent (t+u) with ht | ht
    · refine ⟨2, ?_⟩
      rw [h, ht]
      dsimp [rootPlane, rootConstant, rootTSlope, rootUSlope, VariableEnvelope.A]
      ring
    · refine ⟨3, ?_⟩
      rw [h, ht]
      dsimp [rootPlane, rootConstant, rootTSlope, rootUSlope, VariableEnvelope.C]
      ring
  · refine ⟨4, ?_⟩
    simpa [rootPlane, rootConstant, rootTSlope, rootUSlope] using h

end
end ImbalancedChen.P2OriginalVariableRootCapAlphabet
