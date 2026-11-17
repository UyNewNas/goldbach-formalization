import ImbalancedChen.P4AOriginalFull87RankSevenTerminalPruning
import ImbalancedChen.P4AOriginalFull87SixthBothInvoice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

This is a literal, occurrence-by-occurrence reduction of the EXISTING
fifthSixthWithoutBoth event invoice. On its actual one-sided fifth/sixth
members, replace the original stoppedTest 8 PAYLOAD by stoppedTest 7 at
the SAME selected history, mass, sign and post-query suffix.

No new event population is generated. The old event list is mapped with
a second, computed value, and the two mapped lists are proved equal.
Consequently the old signed and absolute bills are replaced, not added.
The surviving rank-five and rank-six terminal high-q values are NOT zero.
-/

namespace ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth
   actualFifthSixthExclusiveAbsInvoice)
open P4AOriginalFull87RankSevenTerminalPruning
  (actual_one_sided_stopped8_eq_stopped7)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- Re-evaluate the SAME original one-sided fifth/sixth event at cutoff 7.
The both category is retained unchanged by definition, rather than
silently declared zero. The actual source generator filters it out. -/
def shallowFifthValue (R S : Bool → List ℕ → Bool)
    (T : Bool → List ℕ → ℝ) (ev : FifthStoppedEvent ℕ) : ℝ :=
  match ev.kind with
  | .rawOnly =>
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        ev.selectedAfter ev.positiveAfter ev.massAfter ev.remainingAfter
  | .licensedOnly =>
      -stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        ev.selectedAfter ev.positiveAfter ev.massAfter ev.remainingAfter
  | .both => ev.signedValue

/-- Exact event occurrence and metadata, evaluated with its shallow
literal terminal sum. In particular sixthFromBoth still carries its
original fifth ancestor. -/
def shallowOneSidedValue (R S : Bool → List ℕ → Bool)
    (T : Bool → List ℕ → ℝ) : FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive ev => shallowFifthValue R S T ev
  | .sixthFromBoth _ ev => shallowFifthValue R S T ev

/-- The actual sixth-query event list is filtered ONLY at the former
sixth-BOTH category. The identity is at the List.map level, stronger
than equality of sums: all duplicate occurrences survive in order. -/
private theorem first_filtered_shallow_map
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (g : ℝ → ℝ) (pre : List ℕ) (mass : ℝ)
    (remaining : List ℕ)
    (hraw : ∀ p tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail)
    (hlic : ∀ p tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) true (mass * (1 : ℝ)) tail) :
    (((firstFifthEvents R S (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining).filter
        (fun ev => decide (ev.kind ≠ .both))).map
          (fun ev => g ev.signedValue)) =
    (((firstFifthEvents R S (fun _ : ℕ => (1 : ℝ))
      T pre false mass remaining).filter
        (fun ev => decide (ev.kind ≠ .both))).map
          (fun ev => g (shallowFifthValue R S T ev))) := by
  induction remaining with
  | nil => simp [firstFifthEvents]
  | cons p ps ih =>
      have hr8 := hraw p ps
      have hs8 := hlic p ps
      cases hr : R true (p :: pre) <;>
        cases hs : S true (p :: pre) <;>
        simp [firstFifthEvents, hr, hs, List.filter_append,
          List.map_append, shallowFifthValue, hr8, hs8, ih]

/-- The real fourth-prefix event producer first queries the fifth
candidate, then queries the sixth candidate ONLY in a both-admitted
fifth child. All recursive calls use the original remaining tail. -/
private theorem fourth_one_sided_shallow_map
    (R S : Bool → List ℕ → Bool) (T : Bool → List ℕ → ℝ)
    (g : ℝ → ℝ) (pre : List ℕ) (mass : ℝ)
    (remaining : List ℕ)
    (hraw5 : ∀ p tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail)
    (hlic5 : ∀ p tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail)
    (hraw6 : ∀ p q tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail)
    (hlic6 : ∀ p q tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail) :
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g ev.signedValue)) =
    ((fifthSixthWithoutBoth R S (fun _ : ℕ => (1 : ℝ))
      T pre true mass remaining).map
        (fun ev => g (shallowOneSidedValue R S T ev))) := by
  induction remaining with
  | nil => simp [fifthSixthWithoutBoth]
  | cons p ps ih =>
      have hinner := first_filtered_shallow_map R S T g
        (p :: pre) (mass * (1 : ℝ)) ps
        (fun q tail => hraw6 p q tail)
        (fun q tail => hlic6 p q tail)
      have hr8 := hraw5 p ps
      have hs8 := hlic5 p ps
      cases hr : R false (p :: pre) <;>
        cases hs : S false (p :: pre) <;>
        simp [fifthSixthWithoutBoth, hr, hs,
          List.map_append, List.map_map, Function.comp_def,
          FifthSixthStoppedEvent.signedValue, shallowOneSidedValue,
          shallowFifthValue, hr8, hs8, hinner, ih]

/-- Full actual RAW/LICENSED instantiation, not a user-supplied
smallness field. It reuses the earlier proved-candidate rank-five and
rank-six cutoff collapse independently for each policy. -/
theorem actual_fourth_prefix_shallow_map
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (F : ℕ → ℝ)
    (pre : List ℕ) (hlen : pre.length = 4)
    (mass : ℝ) (remaining : List ℕ) (g : ℝ → ℝ) :
    ((fifthSixthWithoutBoth
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
      pre true mass remaining).map (fun ev => g ev.signedValue)) =
    ((fifthSixthWithoutBoth
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
      (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
      pre true mass remaining).map (fun ev => g (shallowOneSidedValue
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        (attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F))
        ev))) := by
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ)
  let T := attachedLeafTest N cap 1 w ((N : ℝ) ^ epsilon) (highQTest X F)
  have hcutR : ∀ s pos m tail,
      ((s.length = 5 ∧ pos = false) ∨ (s.length = 6 ∧ pos = true)) →
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T s pos m tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T s pos m tail := by
    intro s pos m tail hlevel
    exact actual_one_sided_stopped8_eq_stopped7
      delta n e q om N cap w he hN epsilon heps X hX F
      R (Or.inl rfl) s pos m tail hlevel
  have hcutS : ∀ s pos m tail,
      ((s.length = 5 ∧ pos = false) ∨ (s.length = 6 ∧ pos = true)) →
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T s pos m tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T s pos m tail := by
    intro s pos m tail hlevel
    exact actual_one_sided_stopped8_eq_stopped7
      delta n e q om N cap w he hN epsilon heps X hX F
      S (Or.inr rfl) s pos m tail hlevel
  have hr5 : ∀ p tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail := by
    intro p tail
    exact hcutR (p :: pre) false (mass * (1 : ℝ)) tail
      (Or.inl ⟨by simp [hlen], rfl⟩)
  have hs5 : ∀ p tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (p :: pre) false (mass * (1 : ℝ)) tail := by
    intro p tail
    exact hcutS (p :: pre) false (mass * (1 : ℝ)) tail
      (Or.inl ⟨by simp [hlen], rfl⟩)
  have hr6 : ∀ p q tail,
      stoppedTest 8 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 R (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail := by
    intro p q tail
    exact hcutR (q :: p :: pre) true
      ((mass * (1 : ℝ)) * (1 : ℝ)) tail
      (Or.inr ⟨by simp [hlen], rfl⟩)
  have hs6 : ∀ p q tail,
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail =
      stoppedTest 7 S (fun _ : ℕ => (1 : ℝ)) T
        (q :: p :: pre) true ((mass * (1 : ℝ)) * (1 : ℝ)) tail := by
    intro p q tail
    exact hcutS (q :: p :: pre) true
      ((mass * (1 : ℝ)) * (1 : ℝ)) tail
      (Or.inr ⟨by simp [hlen], rfl⟩)
  exact fourth_one_sided_shallow_map R S T g
    pre mass remaining hr5 hs5 hr6 hs6

end
end ImbalancedChen.P4AOriginalFull87ShallowOneSidedInvoice
