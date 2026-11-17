import ImbalancedChen.P4AOriginalFull87CentrePrimeCapacity
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
A critical qualification of the preceding signed primitive/density ledger:
full physical moduli d>N can occur inside the original strict high-q Rosser
sum, but the ACTUAL positive receiver fibre vanishes there. The three
artificially separated AP/density/modulus-prime pieces do NOT vanish
individually: their cancellation must happen BEFORE absolute values.

We prove that cancellation at every complete d>N, then carry the full
four-source identity through one fixed receiverTest-generated actual
fifth/sixth event population with *all* arithmetic terms restricted to
d<=N. No replacement event generator, missing high-q mask, changed beta,
or new analytic input is introduced. The valid external PP target still
needs a fixed theta<1 and the smooth-singleton hypotheses.
-/

namespace ImbalancedChen.P4AOriginalFull87SuperNCancellation
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest primeMass densityTest primitiveError modulusPrimeTerm)
open P4AOriginalFull87FifthSignedPrimitive
  (actualFixedSignedFifthTail actual_fixed_fifth_tail_linear
    actual_receiver_four_source)
open P4AOriginalFull87ReceiverHarmonic
  (actual_receiver_fibre_zero_of_large)
open P4AOriginalFull87CentrePrimeCapacity
  (centre_ap_le_floor_of_nonprime actualCentreCapacityBudget
    actual_fixed_fifth_centre_abs_le_capacity)
open P4AOriginalFull87CommonSixthSignedKernel
  (actual_stopped_difference_eq_common_signed_sixth_kernel)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- The admissible *finite receiver support*; not the smaller, fixed
analytic PP level N^theta. Both the equality endpoint and total d=0
are retained. -/
def atMostN (N : ℕ) (F : ℕ → ℝ) (d : ℕ) : ℝ :=
  if d ≤ N then F d else 0

/-- For discussing the exact compensating pieces above the receiver range. -/
def aboveN (N : ℕ) (F : ℕ → ℝ) (d : ℕ) : ℝ :=
  if N < d then F d else 0

/-- Actual receivers are positive and at most N, so their *complete*
modulus fibre, not merely the rough modulus, has support d<=N. -/
theorem receiver_eq_atMostN (N : ℕ) :
    receiverTest N = atMostN N (receiverTest N) := by
  funext d
  by_cases hd : d ≤ N
  · simp [atMostN, hd]
  · have hlarge : N < d := by omega
    simpa [atMostN, hd] using
      (actual_receiver_fibre_zero_of_large N d hlarge)

/-- The centre AP correction is separately zero above N only when
N is not itself prime; otherwise P=N survives even for huge d. -/
theorem centre_prime_zero_above_N (N d : ℕ)
    (hcomp : ¬ Nat.Prime N) (hd : N < d) :
    chenCentrePrimeAPCount N N d = 0 := by
  have hz : N / d = 0 := Nat.div_eq_of_lt hd
  have hle : chenCentrePrimeAPCount N N d ≤ (0 : ℝ) := by
    simpa [hz] using (centre_ap_le_floor_of_nonprime N d hcomp)
  have hnonneg : (0 : ℝ) ≤ chenCentrePrimeAPCount N N d := by
    unfold chenCentrePrimeAPCount
    positivity
  exact le_antisymm hle hnonneg

/-- The genuine large-modulus primitive discrepancy does not vanish.
It equals the negative density contribution PLUS the modulus-prime
correction. Hence applying a standalone PP bound here is unjustified. -/
theorem primitive_large_exact_cancellation (N d : ℕ)
    (hcomp : ¬ Nat.Prime N) (hd : N < d) :
    primitiveError N d =
      modulusPrimeTerm N d - primeMass N * densityTest d := by
  have hrec := actual_receiver_fibre_zero_of_large N d hd
  have hcent := centre_prime_zero_above_N N d hcomp hd
  have hfour := actual_receiver_four_source N d
  rw [hrec, hcent] at hfour
  linarith

/-- Pointwise above-N cancellation of these three terms, with
centre already shown zero separately. The full q is unchanged. -/
theorem aboveN_primitive_eq_modulus_sub_density
    (N : ℕ) (hcomp : ¬ Nat.Prime N) :
    aboveN N (primitiveError N) =
      fun d => aboveN N (modulusPrimeTerm N) d -
        primeMass N * aboveN N densityTest d := by
  funext d
  by_cases hd : N < d
  · simp only [aboveN, if_pos hd]
    exact primitive_large_exact_cancellation N d hcomp hd
  · simp [aboveN, hd]

/-- An actual signed cancellation, over the ORIGINAL fixed occurrence
population, follows from the preceding per-full-q cancellation.
This is an identity and makes no asymptotic claim. -/
theorem actual_fifth_aboveN_signed_cancellation
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (hcomp : ¬ Nat.Prime N) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (aboveN N (primitiveError N)) =
    actualFixedSignedFifthTail delta n e q om N cap w z L X
      (aboveN N (modulusPrimeTerm N)) -
    primeMass N * actualFixedSignedFifthTail
      delta n e q om N cap w z L X (aboveN N densityTest) := by
  have hfun :
      aboveN N (primitiveError N) =
        fun d => (1 : ℝ) * aboveN N (modulusPrimeTerm N) d +
          (-primeMass N) * aboveN N densityTest d := by
    funext d
    have h := congrFun
      (aboveN_primitive_eq_modulus_sub_density N hcomp) d
    dsimp at h ⊢
    linarith
  rw [hfun]
  have hlin := actual_fixed_fifth_tail_linear
    delta n e q om N cap w z L X
    (aboveN N (modulusPrimeTerm N)) (aboveN N densityTest)
    (1 : ℝ) (-primeMass N)
  simpa [sub_eq_add_neg] using hlin

/-- All four components may be restricted to d<=N BEFORE triangle
inequalities: d>N is an exact zero of the actual receiver, even though
the separately written primitiveError does not vanish. -/
theorem receiver_four_sources_atMostN (N : ℕ) :
    receiverTest N =
      fun d =>
        primeMass N * atMostN N densityTest d +
        atMostN N (primitiveError N) d -
        atMostN N (modulusPrimeTerm N) d -
        atMostN N (chenCentrePrimeAPCount N N) d := by
  funext d
  by_cases hd : d ≤ N
  · simpa [atMostN, hd] using actual_receiver_four_source N d
  · have hlarge : N < d := by omega
    simp [atMostN, hd,
      actual_receiver_fibre_zero_of_large N d hlarge]

/-- Finite same-population signed transport with complete-modulus
d<=N support. Occurrences, histories, beta, and high-q strictness are
unchanged because only the terminal arithmetic function is replaced. -/
theorem actual_fixed_fifth_bounded_four_sources
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (receiverTest N) =
      primeMass N * actualFixedSignedFifthTail
        delta n e q om N cap w z L X (atMostN N densityTest) +
      actualFixedSignedFifthTail
        delta n e q om N cap w z L X (atMostN N (primitiveError N)) -
      actualFixedSignedFifthTail
        delta n e q om N cap w z L X (atMostN N (modulusPrimeTerm N)) -
      actualFixedSignedFifthTail
        delta n e q om N cap w z L X
          (atMostN N (chenCentrePrimeAPCount N N)) := by
  let T : (ℕ → ℝ) → ℝ :=
    actualFixedSignedFifthTail delta n e q om N cap w z L X
  let D : ℕ → ℝ := atMostN N densityTest
  let E : ℕ → ℝ := atMostN N (primitiveError N)
  let M : ℕ → ℝ := atMostN N (modulusPrimeTerm N)
  let C : ℕ → ℝ := atMostN N (chenCentrePrimeAPCount N N)
  let A : ℕ → ℝ := fun d => primeMass N * D d + E d
  let B : ℕ → ℝ := fun d => A d - M d
  have ha : T A = primeMass N * T D + T E := by
    simpa [T, A] using (actual_fixed_fifth_tail_linear
      delta n e q om N cap w z L X D E (primeMass N) (1 : ℝ))
  have hb : T B = T A - T M := by
    simpa [T, B, sub_eq_add_neg] using
      (actual_fixed_fifth_tail_linear
        delta n e q om N cap w z L X A M (1 : ℝ) (-1 : ℝ))
  have hreceiver : receiverTest N = fun d => B d - C d := by
    funext d
    have h := congrFun (receiver_four_sources_atMostN N) d
    simpa [B, A, C, D, E, M] using h
  have hc : T (receiverTest N) = T B - T C := by
    rw [hreceiver]
    simpa [T, sub_eq_add_neg] using
      (actual_fixed_fifth_tail_linear
        delta n e q om N cap w z L X B C (1 : ℝ) (-1 : ℝ))
  change T (receiverTest N) =
    primeMass N * T D + T E - T M - T C
  rw [hc, hb, ha]

/-- The previous centre invoice is still the same physical one:
at d>N it was already zero (given non-prime N), so the truncation
does not create a fourth centre payment. -/
theorem centre_eq_atMostN (N : ℕ)
    (hcomp : ¬ Nat.Prime N) :
    atMostN N (chenCentrePrimeAPCount N N) =
      chenCentrePrimeAPCount N N := by
  funext d
  by_cases hd : d ≤ N
  · simp [atMostN, hd]
  · have hlarge : N < d := by omega
    have hz := centre_prime_zero_above_N N d hcomp hlarge
    simp [atMostN, hd, hz]

/-- Exact replacement of the original same-rho stopped signed delta.
This is a genuinely bounded full-q primitive discrepancy target, but
q<=N does not yet imply a fixed PP theta<1. -/
theorem actual_stopped_bounded_four_sources
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X
        (receiverTest N) -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X (receiverTest N) =
      primeMass N * actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N densityTest) +
      actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N (primitiveError N)) -
      actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N (modulusPrimeTerm N)) -
      actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N (chenCentrePrimeAPCount N N)) := by
  rw [actual_stopped_difference_eq_common_signed_sixth_kernel
    delta n e q om N cap w z he hN epsilon heps X hX
      (receiverTest N)]
  exact actual_fixed_fifth_bounded_four_sources
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X

/-- A genuine no-double-charge three-term error ledger after the
d>N cancellation, with the original centre capacity substituted once.
No arbitrary smallness of the primitive or modulus-prime totals. -/
theorem actual_stopped_bounded_density_gap_centre_budget
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ))
    (hcomp : ¬ Nat.Prime N) :
    |(rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X
        (receiverTest N) -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      primeMass N * actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N densityTest)| ≤
    |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N (primitiveError N))| +
    |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (atMostN N (modulusPrimeTerm N))| +
    actualCentreCapacityBudget
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X := by
  rw [actual_stopped_bounded_four_sources
    delta n e q om N cap w z he hN epsilon heps X hX]
  rw [centre_eq_atMostN N hcomp]
  let V := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (atMostN N densityTest)
  let A := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (atMostN N (primitiveError N))
  let B := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (atMostN N (modulusPrimeTerm N))
  let C := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (chenCentrePrimeAPCount N N)
  change |(primeMass N * V + A - B - C) - primeMass N * V| ≤
    |A| + |B| + actualCentreCapacityBudget
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
  have hcent : |C| ≤ actualCentreCapacityBudget
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X := by
    exact actual_fixed_fifth_centre_abs_le_capacity
      delta n e q om N cap w z ((N : ℝ) ^ epsilon) X hcomp
  have hcancel :
      (primeMass N * V + A - B - C) - primeMass N * V =
        A - B - C := by ring
  rw [hcancel]
  calc
    |A - B - C| ≤ |A - B| + |C| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add (A - B) (-C))
    _ ≤ (|A| + |B|) + |C| := by
      exact add_le_add_right
        (by simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add A (-B))) _
    _ ≤ |A| + |B| + actualCentreCapacityBudget
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X := by
      exact add_le_add_left hcent _

end
end ImbalancedChen.P4AOriginalFull87SuperNCancellation
