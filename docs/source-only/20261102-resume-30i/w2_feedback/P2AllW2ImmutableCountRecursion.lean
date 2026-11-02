import ImbalancedChen.P2W2PhysicalChildFeedback

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

One generation simultaneously reads the previous physical state for both
Buchstab signs, all70 W1, all36 W2, and every admitted singleton/pair child.
The old-count invariant in the local preservation lemmas is discharged by
induction from the finite Rosser polynomials in the exported theorem.
No final count enclosure or adopted analytic table is an input.
-/
namespace ImbalancedChen.P2AllW2ImmutableCountRecursion

noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2FrozenReceiverCountActions
open P2AllW1SameQRawCountInduction
open P2AllW1FrozenReceiverFiniteAction
open P2W2PhysicalChildFeedback
open P2ActualMarkedCountState (Query)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedActualBuchstabTransfer (childWindow)
open P5OriginalActionMassBound (W1Target W1Anchor originalW2At)

/-- Generalize H's proved one-generation argument so it can consume the
new joint state, rather than restarting a separate W1 recursion. -/
theorem ordinary_preserves (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (z : ℝ) (a : Query) (hdz : QueryAdmitted Q d z)
    (hold : Encloses N Q E old) :
    ordinaryCandidate false N Q old d z a≤(frozenCount N d E z:ℝ) ∧
      (frozenCount N d E z:ℝ)≤ordinaryCandidate true N Q old d z a := by
  unfold ordinaryCandidate
  dsimp only
  by_cases hg : cutoff Q d a.val≤z ∧ 0≤z ∧ z^2≤Q/(d:ℝ)
  · simp only [if_pos hg,Bool.false_eq_true,if_false,if_true]
    have ha := hold d (cutoff Q d a.val) (cutoff_query hdz.1 hdz.2.1 a.property.1)
    have hc : ∀q∈primeWindow (d*N) (cutoff Q d a.val) z,
        QueryAdmitted Q (d*q) (q:ℝ) :=
      fun q hq => ordinary_child_query hdz.1 hg.2.1 hg.2.2 hq
    have hl := sum_le_sum (fun q hq => (hold (d*q) (q:ℝ) (hc q hq)).1)
    have hu := sum_le_sum (fun q hq => (hold (d*q) (q:ℝ) (hc q hq)).2)
    have hb : (frozenCount N d E (cutoff Q d a.val):ℝ)=
        (frozenCount N d E z:ℝ)+
          ∑ q∈primeWindow (d*N) (cutoff Q d a.val) z,
            (frozenCount N (d*q) E (q:ℝ):ℝ) := by
      exact_mod_cast frozen_selected_buchstab N d E hg.1
    constructor <;> linarith
  · simpa only [if_neg hg,Bool.false_eq_true,if_false,if_true] using hold d z hdz

theorem W1_preserves (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (z : ℝ) (a : W1Action) (hdz : QueryAdmitted Q d z)
    (hold : Encloses N Q E old) :
    (frozenCount N d E z:ℝ)≤W1Candidate N Q E old d z a := by
  unfold W1Candidate
  split_ifs with hz
  · rw [hz]
    have hp := original_W1_parameters a.1 a.2
    have ha := (hold d (cutoff Q d (W1Anchor a.2))
      (cutoff_query hdz.1 hdz.2.1 (by linarith : 1≤W1Anchor a.2))).2
    have hl := sum_le_sum (fun q hq =>
      (hold (d*q) (cutoff Q d (W1Anchor a.2))
        (W1_child_queries a.1 a.2 hdz.1 hdz.2.1 hq).2).1)
    have hcut : cutoff Q d (W1Anchor a.2)≤cutoff Q d (W1Target a.1) :=
      Real.rpow_le_rpow_of_exponent_le hdz.2.1.le
        (one_div_le_one_div_of_le (by linarith : 0<W1Target a.1) hp.2.1)
    have hc : 2*(frozenCount N d E (cutoff Q d (W1Target a.1)):ℝ)≤
        2*(frozenCount N d E (cutoff Q d (W1Anchor a.2)):ℝ)-
          (∑ q∈childWindow N d Q (W1Target a.1) (W1Anchor a.2),
            (frozenCount N (d*q) E (cutoff Q d (W1Anchor a.2)):ℝ))+
          (rawTripleCount N d (d*N) E (cutoff Q d (W1Anchor a.2))
            (cutoff Q d (W1Target a.1)):ℝ) := by
      exact_mod_cast frozen_selected_three_prime_weight N d E hcut
    linarith
  · exact (hold d z hdz).2

theorem W1Round_preserves (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (bank : List Query) (hold : Encloses N Q E old) :
    Encloses N Q E (P2AllW1SameQRawCountInduction.oneRound N Q E bank old) := by
  intro d z hdz
  constructor
  · apply bestLower_le (hold d z hdz).1
    intro x hx
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
    exact (ordinary_preserves N Q E old d z a hdz hold).1
  · apply le_bestUpper (hold d z hdz).2
    intro x hx
    rcases List.mem_append.mp hx with ho | hw
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp ho
      exact (ordinary_preserves N Q E old d z a hdz hold).2
    · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
      exact W1_preserves N Q E old d z a hdz hold

def allW2 : List (Fin 36) := (Finset.univ : Finset (Fin 36)).toList

def W2Candidate (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (old : PhysicalState)
    (d : ℕ) (z : ℝ) (j : Fin 36) : ℝ :=
  if z=cutoff Q d (originalW2At j).s then W2Bound N Q E old d j
  else old.upper d z

def oneRound (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query)
    (old : PhysicalState) : PhysicalState :=
  let ordinary := P2AllW1SameQRawCountInduction.oneRound N Q E bank old
  ⟨fun d z => bestUpper (ordinary.upper d z)
      (allW2.map (W2Candidate N Q E old d z)), ordinary.lower⟩

def iterate (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query) : ℕ → PhysicalState
  | 0 => initial N Q E
  | n+1 => oneRound N Q E bank (iterate N Q E bank n)

theorem oneRound_preserves (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query)
    (old : PhysicalState) (hold : Encloses N Q E old) :
    Encloses N Q E (oneRound N Q E bank old) := by
  intro d z hdz
  have ho := W1Round_preserves N Q E old bank hold d z hdz
  refine ⟨ho.1,?_⟩
  apply le_bestUpper ho.2
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  unfold W2Candidate
  split_ifs with hz
  · rw [hz]
    exact W2Bound_upper N Q E old j hdz.1 hdz.2.1 hold
  · exact (hold d z hdz).2

/-- The invariant is proved here, not requested from a caller. All
children of all actions read exactly iterate(..., rounds), at the same Q. -/
theorem iterate_encloses (N : ℕ) (Q : ℝ) (E : ℕ → Prop) (bank : List Query)
    (rounds : ℕ) : Encloses N Q E (iterate N Q E bank rounds) := by
  induction rounds with
  | zero => exact fun _ _ h => initial_encloses N Q E h
  | succ n ih => exact oneRound_preserves N Q E bank _ ih

theorem iterate_upper_le_each_W2 (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (j : Fin 36) :
    (iterate N Q E bank (rounds+1)).upper d (cutoff Q d (originalW2At j).s) ≤
      W2Bound N Q E (iterate N Q E bank rounds) d j := by
  have hm : W2Candidate N Q E (iterate N Q E bank rounds) d
      (cutoff Q d (originalW2At j).s) j ∈
      allW2.map (W2Candidate N Q E (iterate N Q E bank rounds) d
        (cutoff Q d (originalW2At j).s)) :=
    List.mem_map.mpr ⟨j,by simp [allW2],rfl⟩
  simpa only [iterate,oneRound,W2Candidate,if_pos rfl] using
    bestUpper_le_member
      ((P2AllW1SameQRawCountInduction.oneRound N Q E bank
        (iterate N Q E bank rounds)).upper d (cutoff Q d (originalW2At j).s)) hm

theorem iterate_retains_previous (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (z : ℝ) :
    (iterate N Q E bank rounds).lower d z ≤ (iterate N Q E bank (rounds+1)).lower d z ∧
      (iterate N Q E bank (rounds+1)).upper d z ≤ (iterate N Q E bank rounds).upper d z := by
  refine ⟨fallback_le_bestLower _ _,?_⟩
  exact (bestUpper_le_fallback _ _).trans (bestUpper_le_fallback _ _)

theorem iterate_upper_le_each_W1 (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d : ℕ) (z : ℝ) (i : Fin 7) (j : Fin 10) :
    (iterate N Q E bank (rounds+1)).upper d z ≤
      W1Candidate N Q E (iterate N Q E bank rounds) d z (i,j) := by
  have hm : W1Candidate N Q E (iterate N Q E bank rounds) d z (i,j) ∈
      upperCandidates N Q E (iterate N Q E bank rounds) bank d z := by
    apply List.mem_append.mpr
    exact Or.inr (List.mem_map.mpr ⟨(i,j),original_action_mem i j,rfl⟩)
  exact (bestUpper_le_fallback _ _).trans (bestUpper_le_member _ hm)

/-- An actual admitted singleton in the next action reads the previous
joint lower state, including its earlier W2-to-Buchstab feedback. -/
theorem negativeChild_reads_previous (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d p : ℕ) (a : ℝ)
    (hq : QueryAdmitted Q (d*p) a) :
    negativeChild N Q E (iterate N Q E bank rounds) d p a =
      (iterate N Q E bank rounds).lower (d*p) a := by
  simp only [negativeChild,if_pos hq]

theorem positiveChild_reads_previous (N : ℕ) (Q : ℝ) (E : ℕ → Prop)
    (bank : List Query) (rounds d p q : ℕ) (a : ℝ) (hg : PairGate Q d p q) :
    positiveChild N Q E (iterate N Q E bank rounds) d p q a =
      (iterate N Q E bank rounds).upper (d*p*q) a + complementCount N (d*p*q) E a := by
  simp only [positiveChild,if_pos hg]

end
end ImbalancedChen.P2AllW2ImmutableCountRecursion
