import ImbalancedChen.P4AOriginalFull87SignedCarrierAP
import ImbalancedChen.ChenInitialPrimeSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A necessary exact arithmetic distinction before invoking the manuscript's
SIGNED prime-product estimate.  The reflected one-quotient shell
P = N - a*b is only ONE member of the primitive prime AP mod a*b.
The rest of that very same AP is a genuine, generally nonzero tail.
The AP at q=a*b is not silently identified with a one-shell indicator.

Here we split the actual original PLUS-Rosser signed carrier expression
into a true full-q primitive AP count and an exact omitted-shell tail.
The original fifth RAW/LICENSED tags, ordered sixth occurrences,
sharedRankFour parent and frozen survivor selector remain unchanged.
The mean(b) is arbitrary: this does not authenticate a SAME-rho PP mean,
a smooth weight or any asymptotic payment.
-/

namespace ImbalancedChen.P4AOriginalFull87OneShellAPGap
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87SignedCarrierAP
  (originalSignedPrimitiveCarrierAPDiscrepancy
   originalSignedPrimitiveCarrierAPEvent
   frozenSurvivorSignedPrimitiveCarrierAPRoom
   physical_after_lower_eq_mean_plus_signed_carrier_AP)
open P4AOriginalFull87CentreIntervalBridge (originalCarrierReflectedStep)
open P4AOriginalFull87ActualPrimitiveRosserRoom (actualPrimitiveRosserRoom)
open P4AOriginalFull87CarrierGlobalJumpInvoice (frozenSurvivorCarrierMeanRoom)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- Actual full-q primitive carrier AP; no added geometric mask. -/
def actualFullQPrimitiveAPFibre (N Q : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun P => Nat.ModEq Q P N)

/-- The genuinely remaining members of the SAME AP after removing
the one reflected shell P=N-Q. This is an actual Finset.erase, not an
independently estimated or hypothesized tail. -/
def actualFullQOutsideOneShell (N Q : ℕ) : Finset ℕ :=
  (actualFullQPrimitiveAPFibre N Q).erase (N - Q)

/-- Whenever the reflected shell is an actual primitive source prime,
it is a member of the full congruence fibre modulo Q. -/
theorem reflected_shell_in_actual_full_Q_AP
    (N Q : ℕ) (h : N - Q ∈ chenAdditivePrimeCarrier N) :
    N - Q ∈ actualFullQPrimitiveAPFibre N Q := by
  have hp : Nat.Prime (N - Q) :=
    (mem_chenAdditivePrimeCarrier.mp h).2.1
  have hQ : Q ≤ N := by
    have htwo := hp.two_le
    omega
  have hsub : N - (N - Q) = Q := by omega
  have hdiv : Q ∣ N - (N - Q) := by
    rw [hsub]
  have hmod : Nat.ModEq Q (N - Q) N :=
    (dvd_sub_iff_modEq_of_le (Nat.sub_le N Q)).mp hdiv
  exact Finset.mem_filter.mpr ⟨h, hmod⟩

/-- An exact AP count is one shell plus its erased complement.
This also handles the zero-modulus and out-of-range cases: a shell
not in the primitive source contributes zero, not an invented 1. -/
theorem actual_full_Q_AP_eq_shell_plus_outside
    (N Q : ℕ) :
    ((actualFullQPrimitiveAPFibre N Q).card : ℝ) =
      (if N - Q ∈ chenAdditivePrimeCarrier N then (1 : ℝ) else 0) +
      ((actualFullQOutsideOneShell N Q).card : ℝ) := by
  classical
  by_cases h : N - Q ∈ chenAdditivePrimeCarrier N
  · have hmem := reflected_shell_in_actual_full_Q_AP N Q h
    have hc := Finset.card_erase_add_one hmem
    have hnat :
        (actualFullQPrimitiveAPFibre N Q).card =
          1 + (actualFullQOutsideOneShell N Q).card := by
      unfold actualFullQOutsideOneShell
      omega
    have hreal :
        ((actualFullQPrimitiveAPFibre N Q).card : ℝ) =
          (1 : ℝ) +
          ((actualFullQOutsideOneShell N Q).card : ℝ) := by
      exact_mod_cast hnat
    simpa [h] using hreal
  · have hnot : N - Q ∉ actualFullQPrimitiveAPFibre N Q := by
      intro hx
      exact h (Finset.mem_filter.mp hx).1
    have htail :
        actualFullQOutsideOneShell N Q =
          actualFullQPrimitiveAPFibre N Q := by
      unfold actualFullQOutsideOneShell
      exact Finset.erase_eq_of_not_mem hnot
    simp [h, htail]

theorem actual_reflected_shell_eq_full_AP_sub_outside
    (N Q : ℕ) :
    (if N - Q ∈ chenAdditivePrimeCarrier N then (1 : ℝ) else 0) =
      ((actualFullQPrimitiveAPFibre N Q).card : ℝ) -
        ((actualFullQOutsideOneShell N Q).card : ℝ) := by
  rw [actual_full_Q_AP_eq_shell_plus_outside]
  ring

/-- The same true FULL q=a*b is used in both terms. The original
PLUS-Rosser beta is never replaced by 1 or made nonnegative. -/
def originalFullQPrimitiveAPRoom (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) : ℝ :=
  ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
    actualSmallRosserPlus N cap w L a *
      (((actualFullQPrimitiveAPFibre N (a * (p :: pre).prod)).card : ℝ) -
        mean (p :: pre).prod)

/-- Signed omitted-shell invoice. It is NOT nonnegative merely because
each underlying Finset.card is nonnegative: beta may change sign. -/
def originalFullQOutsideShellRoom (N cap : ℕ) (w L : ℝ)
    (X : ℕ) (pre : List ℕ) (p : ℕ) : ℝ :=
  ∑ a ∈ actualPrimitiveRosserRoom N cap w L X pre p,
    actualSmallRosserPlus N cap w L a *
      ((actualFullQOutsideOneShell N (a * (p :: pre).prod)).card : ℝ)

/-- Exact bridge from the original signed primitive reflected room to
true AP fibres modulo a*b. The outside-shell term CANNOT be discarded
or paid from the manuscript's PP estimate without additional work. -/
theorem original_signed_carrier_eq_full_AP_sub_outside
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) (mean : ℕ → ℝ) :
    originalSignedPrimitiveCarrierAPDiscrepancy
      N cap w L X pre p mean =
    originalFullQPrimitiveAPRoom N cap w L X pre p mean -
      originalFullQOutsideShellRoom N cap w L X pre p := by
  classical
  unfold originalSignedPrimitiveCarrierAPDiscrepancy
    originalFullQPrimitiveAPRoom originalFullQOutsideShellRoom
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  dsimp [originalCarrierReflectedStep]
  rw [actual_reflected_shell_eq_full_AP_sub_outside]
  ring

private theorem list_sum_sub {α : Type*}
    (xs : List α) (f g : α → ℝ) :
    (xs.map (fun x => f x - g x)).sum =
      (xs.map f).sum - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- Exactly the original fifth/sixth event tags and ordered p suffix. -/
def originalFullQPrimitiveAPEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          originalFullQPrimitiveAPRoom N cap w L X
            fifth.selectedAfter p mean)).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

def originalFullQOutsideShellEvent
    (N cap : ℕ) (w L : ℝ) (X : ℕ) :
    FifthSixthStoppedEvent ℕ → ℝ
  | .fifthExclusive fifth =>
      let v : ℝ := (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          originalFullQOutsideShellRoom N cap w L X
            fifth.selectedAfter p)).sum
      match fifth.kind with
      | .rawOnly => v
      | .licensedOnly => -v
      | .both => 0
  | .sixthFromBoth _ _ => 0

theorem original_signed_carrier_event_eq_full_AP_sub_outside
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (mean : ℕ → ℝ)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalSignedPrimitiveCarrierAPEvent N cap w L X mean ev =
      originalFullQPrimitiveAPEvent N cap w L X mean ev -
        originalFullQOutsideShellEvent N cap w L X ev := by
  classical
  cases ev with
  | sixthFromBoth pre fifth =>
      simp [originalSignedPrimitiveCarrierAPEvent,
        originalFullQPrimitiveAPEvent, originalFullQOutsideShellEvent]
  | fifthExclusive fifth =>
      let c : ℝ := signedTreeCoefficient true fifth.massAfter
      let F : ℕ → ℝ := fun p =>
        originalFullQPrimitiveAPRoom N cap w L X fifth.selectedAfter p mean
      let G : ℕ → ℝ := fun p =>
        originalFullQOutsideShellRoom N cap w L X fifth.selectedAfter p
      have hsum :
          (fifth.remainingAfter.map (fun p =>
            c * originalSignedPrimitiveCarrierAPDiscrepancy
              N cap w L X fifth.selectedAfter p mean)).sum =
          (fifth.remainingAfter.map (fun p => c * F p)).sum -
          (fifth.remainingAfter.map (fun p => c * G p)).sum := by
        calc
          _ = (fifth.remainingAfter.map
                (fun p => c * F p - c * G p)).sum := by
                  apply congrArg List.sum
                  apply List.map_congr_left
                  intro p hp
                  dsimp [F, G]
                  rw [original_signed_carrier_eq_full_AP_sub_outside]
                  ring
          _ = _ := list_sum_sub fifth.remainingAfter
            (fun p => c * F p) (fun p => c * G p)
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [originalSignedPrimitiveCarrierAPEvent,
            originalFullQPrimitiveAPEvent,
            originalFullQOutsideShellEvent, hk, c, F, G] using hsum
      | licensedOnly =>
          have hneg :
              -((fifth.remainingAfter.map (fun p =>
                c * originalSignedPrimitiveCarrierAPDiscrepancy
                  N cap w L X fifth.selectedAfter p mean)).sum) =
              -((fifth.remainingAfter.map (fun p => c * F p)).sum) -
              -((fifth.remainingAfter.map (fun p => c * G p)).sum) := by
            rw [hsum]
            ring
          simpa [originalSignedPrimitiveCarrierAPEvent,
            originalFullQPrimitiveAPEvent,
            originalFullQOutsideShellEvent, hk, c, F, G] using hneg
      | both =>
          simp [originalSignedPrimitiveCarrierAPEvent,
            originalFullQPrimitiveAPEvent, originalFullQOutsideShellEvent, hk]

/-- Identical sharedRankFour histories, frozen survivor filter and
ordered fifth/sixth producer as the previous signed physical equation. -/
def frozenFullQPrimitiveAPRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalFullQPrimitiveAPEvent N cap w
        ((N : ℝ) ^ epsilon) X mean)).sum)).sum

def frozenFullQOutsideShellRoom
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) : ℝ :=
  ((sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))).map (fun state =>
    (((actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
        (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
          ((N : ℝ) ^ epsilon) X)).map
      (originalFullQOutsideShellEvent N cap w
        ((N : ℝ) ^ epsilon) X)).sum)).sum

theorem frozen_signed_carrier_eq_full_AP_sub_outside
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ) :
    frozenSurvivorSignedPrimitiveCarrierAPRoom
      delta n e q om N cap w epsilon X mean =
    frozenFullQPrimitiveAPRoom delta n e q om N cap w epsilon X mean -
      frozenFullQOutsideShellRoom delta n e q om N cap w epsilon X := by
  let states := sharedRankFour e q om N cap w
    ((N : ℝ) ^ ((19 : ℝ) / 96))
  let events := fun state =>
    (actualFifthSixthWithoutBoth delta n e q om N cap w
      ((N : ℝ) ^ epsilon) X (receiverTest N) state).filter
      (keepFrozenUpperSurvivor N ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X)
  let H := originalSignedPrimitiveCarrierAPEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  let F := originalFullQPrimitiveAPEvent
    N cap w ((N : ℝ) ^ epsilon) X mean
  let G := originalFullQOutsideShellEvent
    N cap w ((N : ℝ) ^ epsilon) X
  change (states.map (fun s => ((events s).map H).sum)).sum =
    (states.map (fun s => ((events s).map F).sum)).sum -
    (states.map (fun s => ((events s).map G).sum)).sum
  calc
    _ = (states.map (fun s =>
        ((events s).map (fun ev => F ev - G ev)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro state hs
          apply congrArg List.sum
          apply List.map_congr_left
          intro ev hev
          exact original_signed_carrier_event_eq_full_AP_sub_outside
            N cap w ((N : ℝ) ^ epsilon) X mean ev
    _ = (states.map (fun s =>
        ((events s).map F).sum - ((events s).map G).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro state hs
          exact list_sum_sub (events state) F G
    _ = _ := list_sum_sub states
      (fun s => ((events s).map F).sum)
      (fun s => ((events s).map G).sum)

/-- The lower receiver remains paid exactly once. This statement
exposes the true additional full-q AP tail, not a PP-bound invoice.
No same-rho mean, smooth chart or H_N error is certified here. -/
theorem physical_after_lower_eq_mean_plus_full_AP_minus_shell_tail
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ)
    (mean : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : (1 : ℝ) < (N : ℝ))
    (heps : epsilon ≤ (1 / 500 : ℝ))
    (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    (rawStopped e q om N cap w ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (receiverTest N) -
      licensedStopped delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      actualFixedSignedFifthTail delta n e q om N cap w
        ((N : ℝ) ^ ((19 : ℝ) / 96))
        ((N : ℝ) ^ epsilon) X (lowerHalfReceiver N) =
    frozenSurvivorCarrierMeanRoom
      delta n e q om N cap w epsilon X mean +
    frozenFullQPrimitiveAPRoom
      delta n e q om N cap w epsilon X mean -
    frozenFullQOutsideShellRoom
      delta n e q om N cap w epsilon X := by
  rw [physical_after_lower_eq_mean_plus_signed_carrier_AP
    delta n e q om N cap w epsilon X mean he hN heps hX]
  rw [frozen_signed_carrier_eq_full_AP_sub_outside]
  ring

end
end ImbalancedChen.P4AOriginalFull87OneShellAPGap
