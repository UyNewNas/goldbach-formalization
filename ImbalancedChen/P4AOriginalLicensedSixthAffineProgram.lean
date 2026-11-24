import ImbalancedChen.P4AOriginalSixthLicensedFilter
import ImbalancedChen.P4AOriginalSixthTaggedWinner

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Compile the EXISTING licensed sixth filter, not the old unfiltered cap.
All extra lower-square and upper-debit checks are explicit finite affine
comparisons. Each candidate is rounded ONCE. The max of these candidates
and the real finite fifth seed is NOT rounded a second time.
-/
namespace ImbalancedChen.P4AOriginalLicensedSixthAffineProgram
noncomputable section
open scoped Classical BigOperators
open Set
open P1FiniteAffineDecisionProgram P1FiniteAffineQuantizerTable
open P4AOriginalFourthFifthAffinePrograms
open P1OriginalVariableFourthContinuation P1GuardFrozenFiniteCapAlgebra
open P5OriginalCommonRefinedConstructor P4AOriginalCompleteSixthChronology
open P4AOriginalSixthActionBank P4AOriginalSixthLicensedFilter
open P4AOriginalFull87FiniteParentCaps
open P4AOriginalSixthTaggedWinner
  (actionCode actionCode_exact actionTests actionTests_at_history finiteFifth finiteFifth_at_history)
open P1QuantizedActionLicense (LowerLicense)
open P4AOriginalFull87HistoryCore (width)
open P1AffineCertifiedMesh P1AffineCertifiedLookup (gridLabel gridLabel_mem)

/-- Exactly the old lower-gate dictionary, now as affine coefficients.
Selected indices repeat the half gate, not an extra complementary square. -/
def lowerAffine {k : ℕ} (I : Finset (Fin k)) : P1QuantizedActionLicense.Gate k → Affine k
  | none => K (1 / 2)
  | some (false, j) =>
      (maskAffine (Finset.univ.filter (fun i => i < j))).add ((X j).scale 2)
  | some (true, j) =>
      if j ∈ I then K (1 / 2) else
      ((maskAffine I).add
        (maskAffine (Finset.univ.filter (fun i => i < j ∧ i ∉ I)))).add ((X j).scale 2)

theorem lowerAffine_exact {k : ℕ} (I : Finset (Fin k))
    (g : P1QuantizedActionLicense.Gate k) (t : Fin k → ℝ) :
    (lowerAffine I g).eval t = P1QuantizedActionLicense.gate I t g := by
  cases g with
  | none => simp [lowerAffine, P1QuantizedActionLicense.gate]
  | some bg =>
      rcases bg with ⟨b,j⟩
      cases b with
      | false => simp [lowerAffine, P1QuantizedActionLicense.gate, prefixSquareExpr]
      | true =>
          by_cases hj : j ∈ I <;>
            simp [lowerAffine, P1QuantizedActionLicense.gate, hj, selectedSquareExpr]

def candidate (n : ℕ) (a : Action) : Program 6 := roundedProgram n (actionCode a)

theorem candidate_exact (n : ℕ) (a : Action) (t : Fin 6 → ℝ) :
    (candidate n a).eval t = (rounded n (endpoint a t) : ℝ) := by
  rw [candidate, roundedProgram_exact, actionCode_exact]

/-- Static finite tests only. The raw chronological guard is the SAME
expanded old guard; the added checks use the action's OWN rounded value. -/
def tests (n : ℕ) (d : OriginalData) (b : ℚ) (a : Action) : List (Gate 6) :=
  actionTests d b a ++
    (indexed Finset.univ (fun g : P1QuantizedActionLicense.Gate 6 =>
      LT (atom (lowerAffine (selected a) g)) (candidate n a)) ++
    [LE (candidate n a) (tentProgram (selected a) (width n))])

def PointAccepted (n : ℕ) (d : OriginalData) (b : ℚ)
    (t : Fin 6 → ℝ) (a : Action) : Prop :=
  Passed t (actionTests d b a) ∧
    LowerLicense (selected a) t (rounded n (endpoint a t) : ℝ) ∧
    (rounded n (endpoint a t) : ℝ) + width n ≤
      VariableEnvelope.v (∑ j ∈ selected a, t j)

theorem tests_exact (n : ℕ) (d : OriginalData) (b : ℚ)
    (t : Fin 6 → ℝ) (a : Action) :
    Passed t (tests n d b a) ↔ PointAccepted n d b t a := by
  have hgate (g : P1QuantizedActionLicense.Gate 6) :
      (atom (lowerAffine (selected a) g)).eval t =
        P1QuantizedActionLicense.gate (selected a) t g :=
    lowerAffine_exact (selected a) g t
  simp only [tests, passed_append, passed_indexed, Finset.mem_univ, true_implies,
    holds_LT, hgate, candidate_exact, passed_cons, passed_nil, holds_LE,
    eval_tentProgram, and_true, le_sub_iff_add_le, PointAccepted, LowerLicense]

theorem tests_at_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ)) (a : Action) :
    Passed (primeHistoryLogCoordinates N 6 pre) (tests n (data e q om) b a) ↔
      Accepted n e q om N pre a := by
  rw [tests_exact]
  unfold PointAccepted Accepted
  rw [actionTests_at_history e q om N b pre hlen hb]

/-- The finite fifth seed is inherited unchanged, even if every action
fails. No protect/rounded operation is applied to this OUTER maximum. -/
def program (n : ℕ) (d : OriginalData) (b : ℚ) : Program 6 :=
  maxRows (tests n d b) (candidate n) (finiteFifth n d b) allActions.toList

theorem program_eval (n : ℕ) (d : OriginalData) (b : ℚ) (t : Fin 6 → ℝ) :
    (program n d b).eval t =
      finiteMax allActions (PointAccepted n d b t)
        (fun a => (rounded n (endpoint a t) : ℝ)) ((finiteFifth n d b).eval t) := by
  simp only [program, eval_maxRows, Finset.toList_toFinset]
  congr 1
  · funext a
    exact propext (tests_exact n d b t a)
  · funext a
    exact candidate_exact n a t

theorem program_at_history (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ) (b : ℚ)
    (pre : List ℕ) (hlen : pre.length = 6)
    (hb : lambda3 (data e q om) N pre = (b : ℝ))
    (hseed : originalSeed (data e q om) N pre = (b : ℝ)) :
    (program n (data e q om) b).eval (primeHistoryLogCoordinates N 6 pre) =
      licensedCap n e q om N pre := by
  simp only [program, eval_maxRows, Finset.toList_toFinset,
    finiteFifth_at_history n e q om N b pre hlen hb hseed, licensedCap]
  congr 1
  · funext a
    exact propext (tests_at_history n e q om N b pre hlen hb a)
  · funext a
    exact candidate_exact n a _

/-- Selection follows result branches, not test leaves. Therefore even
an unrealizable signature cannot make a comparison affine form an output. -/
private theorem allGates_select_property {k : ℕ} (gs : List (Gate k))
    (yes no : Program k) (cmp : Affine k → Affine k → Bool × Bool)
    (P : Affine k → Prop) (hy : P (yes.select cmp)) (hn : P (no.select cmp)) :
    P ((allGates gs yes no).select cmp) := by
  induction gs with
  | nil => exact hy
  | cons g gs ih =>
      cases hg : g.strict <;>
        simp only [allGates, Gate.branch, hg, Bool.false_eq_true, if_false, if_true,
          Program.select]
      all_goals split_ifs <;> assumption

private theorem maxRows_select_property {k : ℕ} {ι : Type*}
    (gs : ι → List (Gate k)) (value : ι → Program k) (seed : Program k)
    (xs : List ι) (cmp : Affine k → Affine k → Bool × Bool)
    (P : Affine k → Prop) (hs : P (seed.select cmp))
    (hv : ∀ a ∈ xs, P ((value a).select cmp)) :
    P ((maxRows gs value seed xs).select cmp) := by
  revert hv
  induction xs with
  | nil => intro _; exact hs
  | cons a xs ih =>
      intro hv
      have hrest := ih (fun j hj => hv j (by simp [hj]))
      have hrow := hv a (by simp)
      apply allGates_select_property _ _ _ _ P
      · simp only [Program.select]
        split_ifs <;> assumption
      · exact hrest

private theorem candidate_select_constant (n : ℕ) (b : ℚ) (a : Action)
    (cmp : Affine 6 → Affine 6 → Bool × Bool) :
    ∃ v ∈ outputAlphabet n b, (candidate n a).select cmp = Affine.const (v : ℝ) := by
  apply maxRows_select_property _ _ _ _ cmp
    (fun x => ∃ v ∈ outputAlphabet n b, x = Affine.const (v : ℝ))
  · exact ⟨0, by simp [outputAlphabet], rfl⟩
  · intro j hj
    have hm : j ∈ indices n := by simpa using hj
    refine ⟨gridValue n j, ?_, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨j,hm,rfl⟩))

theorem program_select_constant (n : ℕ) (d : OriginalData) (b : ℚ)
    (cmp : Affine 6 → Affine 6 → Bool × Bool) :
    ∃ v ∈ outputAlphabet n b, (program n d b).select cmp = Affine.const (v : ℝ) := by
  apply maxRows_select_property _ _ _ _ cmp
    (fun x => ∃ v ∈ outputAlphabet n b, x = Affine.const (v : ℝ))
  · exact protected_select_constant n b _ cmp
  · intro a _
    exact candidate_select_constant n b a cmp

/-- Lookup for the already-filtered value. Applying the earlier protected
lookup to this program would ROUND TWICE and is intentionally not done. -/
def valueTable (n : ℕ) (d : OriginalData) (b : ℚ)
    (s : (program n d b).Signature) : ℝ := ((program n d b).table s).constant

theorem valueTable_on_region (n : ℕ) (d : OriginalData) (b : ℚ)
    (s : (program n d b).Signature) (t : Fin 6 → ℝ)
    (ht : t ∈ (program n d b).region s) :
    valueTable n d b s = (program n d b).eval t := by
  obtain ⟨v,_,hv⟩ := program_select_constant n d b ((program n d b).lookup s)
  have h := (program n d b).table_on_region s t ht
  simpa only [valueTable, Program.table, hv, Affine.eval_const, Affine.const] using h

def valueLookup (n : ℕ) (d : OriginalData) (b : ℚ) (m : ℕ) (t : Fin 6 → ℝ) : ℝ :=
  if t ∈ cube 6 ∧ gridLabel m t ∈ approved (program n d b) m then
    valueTable n d b ((program n d b).signature (center m (gridLabel m t)))
  else valueTable n d b ((program n d b).signature t)

theorem valueLookup_exact (n : ℕ) (d : OriginalData) (b : ℚ)
    (m : ℕ) (t : Fin 6 → ℝ) : valueLookup n d b m t = (program n d b).eval t := by
  unfold valueLookup
  split_ifs with h
  · apply valueTable_on_region
    have ht := mem_logPrimeMeshCell.mp (gridLabel_mem m t h.1)
    exact (certificate_on_approved (program n d b) m (gridLabel m t) h.2 t
      (fun i => (ht i).1) (fun i => (ht i).2.le)).1
  · exact valueTable_on_region n d b _ t rfl

theorem value_closed_box (n : ℕ) (d : OriginalData) (b : ℚ)
    (m : ℕ) (j : Label 6 m) (hj : j ∈ approved (program n d b) m) :
    ∃ v ∈ outputAlphabet n b, ∀ t : Fin 6 → ℝ,
      (∀ i, lo m j i ≤ t i) → (∀ i, t i ≤ hi m j i) →
        valueLookup n d b m t = (v : ℝ) := by
  obtain ⟨v,hv,heq⟩ := program_select_constant n d b
    ((program n d b).lookup ((program n d b).signature (center m j)))
  refine ⟨v,hv,?_⟩
  intro t hl hu
  have h := (certificate_on_approved (program n d b) m j hj t hl hu).2
  rw [valueLookup_exact]
  simpa only [Program.table, heq, Affine.eval_const] using h.symm

end
end ImbalancedChen.P4AOriginalLicensedSixthAffineProgram
