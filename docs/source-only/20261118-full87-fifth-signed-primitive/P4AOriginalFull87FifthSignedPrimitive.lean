import ImbalancedChen.P4AOriginalFull87CoprimeQuotient
import ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The real fifth-exclusive signed high-q stoppage is put into the SAME
primitive AP / exact-coprime-density / modulus-prime / centre-prime
decomposition as the actual eighth ledger. This is NOT a new policy,
a new test source, a fresh smallness field, or an asymptotic estimate.

Crucially, the fifth-event list is always generated ONCE with the actual
receiverTest N. Only its existing common signed sixth arithmetic kernel
is varied linearly. Thus no AP-model event list is silently substituted
for the original receiver-source events. The fifth gate sign, selected
history, remaining p List, full a*b PLUS beta, strict high-q boundary,
and multiplicity of every event are retained.

This gives a precise manuscript-side payment target: the three signed
primitive / modulus-prime / centre-prime terms for the very SAME stopped
delta. It does not establish any of them as o(H_N), authorize PP on
uncontrolled full q, or pay either independent reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest receiverTest_eq primeMass densityTest primitiveError
   modulusPrimeTerm exactCoprimeMean_eq_density_sub_modulus)
open P4AOriginalFull87CommonSixthSignedKernel
  (commonLargeSixthKernel commonSignedEventValue
   actual_stopped_difference_eq_common_signed_sixth_kernel)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthPlusAttachment largeFifthRosserIndices)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- The existing exact eighth arithmetic identity is also an exact
pointwise identity at each complete physical modulus in the fifth tail.
No PNT, BV or assumed uniform discrepancy enters this statement. -/
theorem actual_receiver_four_source (N d : ℕ) :
    receiverTest N d =
      primeMass N * densityTest d + primitiveError N d -
        modulusPrimeTerm N d - chenCentrePrimeAPCount N N d := by
  rw [receiverTest_eq]
  unfold primitiveError
  rw [exactCoprimeMean_eq_density_sub_modulus]
  ring

private theorem highq_test_linear
    (X d : ℕ) (F G : ℕ → ℝ) (u v : ℝ) :
    P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X
        (fun t => u * F t + v * G t) d =
      u * P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X F d +
      v * P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X G d := by
  by_cases h : X < d
  · simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, h]
  · simp [P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest, h]

/-- Linear transport across the original fifth PLUS-beta filtered support.
The small-Rosser index and complete modulus are held fixed. -/
theorem large_fifth_plus_linear
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (pre : List ℕ) (p : ℕ)
    (F G : ℕ → ℝ) (u v : ℝ) :
    largeFifthPlusAttachment N cap w L X
        (fun d => u * F d + v * G d) pre p =
      u * largeFifthPlusAttachment N cap w L X F pre p +
      v * largeFifthPlusAttachment N cap w L X G pre p := by
  unfold largeFifthPlusAttachment
  calc
    (∑ a ∈ largeFifthRosserIndices N cap w X pre,
        actualSmallRosserPlus N cap w L a *
          P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X
            (fun d => u * F d + v * G d) (a * (p :: pre).prod)) =
      ∑ a ∈ largeFifthRosserIndices N cap w X pre,
        (u * (actualSmallRosserPlus N cap w L a *
          P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X F
            (a * (p :: pre).prod)) +
         v * (actualSmallRosserPlus N cap w L a *
          P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X G
            (a * (p :: pre).prod))) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [highq_test_linear]
        ring
    _ = u * (∑ a ∈ largeFifthRosserIndices N cap w X pre,
          actualSmallRosserPlus N cap w L a *
            P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X F
              (a * (p :: pre).prod)) +
        v * (∑ a ∈ largeFifthRosserIndices N cap w X pre,
          actualSmallRosserPlus N cap w L a *
            P4AOriginalFull87PhysicalHighQOwnedInvoice.highQTest X G
              (a * (p :: pre).prod)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]

private theorem list_sum_map_linear {α : Type*}
    (xs : List α) (f g : α → ℝ) (u v : ℝ) :
    (xs.map (fun x => u * f x + v * g x)).sum =
      u * (xs.map f).sum + v * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih]
      ring

/-- The genuine post-fifth sixth p List remains ordered and retains
occurrence multiplicity. Linearity is inside one common arithmetic kernel. -/
theorem common_sixth_kernel_linear
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F G : ℕ → ℝ) (u v : ℝ)
    (fifth : P4AOriginalFull87FirstFifthStoppedEvents.FifthStoppedEvent ℕ) :
    commonLargeSixthKernel N cap w L X
        (fun d => u * F d + v * G d) fifth =
      u * commonLargeSixthKernel N cap w L X F fifth +
      v * commonLargeSixthKernel N cap w L X G fifth := by
  unfold commonLargeSixthKernel
  calc
    (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          largeFifthPlusAttachment N cap w L X
            (fun d => u * F d + v * G d) fifth.selectedAfter p)).sum =
      (fifth.remainingAfter.map (fun p =>
        u * (signedTreeCoefficient true fifth.massAfter *
          largeFifthPlusAttachment N cap w L X F fifth.selectedAfter p) +
        v * (signedTreeCoefficient true fifth.massAfter *
          largeFifthPlusAttachment N cap w L X G fifth.selectedAfter p))).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro p hp
        rw [large_fifth_plus_linear]
        ring
    _ = u * (fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            largeFifthPlusAttachment N cap w L X F fifth.selectedAfter p)).sum +
        v * (fifth.remainingAfter.map (fun p =>
          signedTreeCoefficient true fifth.massAfter *
            largeFifthPlusAttachment N cap w L X G fifth.selectedAfter p)).sum := by
        exact list_sum_map_linear _ _ _ u v

/-- RAW-only and LICENSED-only have opposite signs, not independent
absolute invoices. The absent constructor cases are syntactic zero and
are not used as an assumption about an arbitrary actual event source. -/
theorem common_signed_event_linear
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F G : ℕ → ℝ) (u v : ℝ)
    (ev : P4AOriginalFull87FifthSixthStoppedEvents.FifthSixthStoppedEvent ℕ) :
    commonSignedEventValue N cap w L X
        (fun d => u * F d + v * G d) ev =
      u * commonSignedEventValue N cap w L X F ev +
      v * commonSignedEventValue N cap w L X G ev := by
  cases ev with
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simpa [commonSignedEventValue, hk] using
            (common_sixth_kernel_linear N cap w L X F G u v fifth)
      | licensedOnly =>
          simp only [commonSignedEventValue, hk]
          rw [common_sixth_kernel_linear]
          ring
      | both => simp [commonSignedEventValue, hk]
  | sixthFromBoth fifthSelected inner =>
      simp [commonSignedEventValue]

/-- Always evaluate the fifth/sixth event generator at the original
receiverTest N, for EVERY F below. In particular its original parent,
signed history and event occurrence list cannot vary with the source
in the subsequent linearity calculation. -/
def actualFixedSignedFifthTail
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) : ℝ :=
  ((sharedRankFour e q om N cap w z).map (fun state =>
    ((actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (receiverTest N) state).map
      (commonSignedEventValue N cap w L X F)).sum)).sum

/-- The fixed ACTUAL producer is linear in its arithmetic leaf test.
This is proved on the identical nested List, not by replacing the
producer by a new density or AP-event model. -/
theorem actual_fixed_fifth_tail_linear
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (F G : ℕ → ℝ) (u v : ℝ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (fun d => u * F d + v * G d) =
      u * actualFixedSignedFifthTail delta n e q om N cap w z L X F +
      v * actualFixedSignedFifthTail delta n e q om N cap w z L X G := by
  let states := sharedRankFour e q om N cap w z
  let events := fun state =>
    actualFifthSixthWithoutBoth delta n e q om N cap w L X
      (receiverTest N) state
  change ((states.map (fun state =>
      ((events state).map (commonSignedEventValue N cap w L X
        (fun d => u * F d + v * G d))).sum)).sum) =
      u * ((states.map (fun state =>
        ((events state).map (commonSignedEventValue N cap w L X F)).sum)).sum) +
      v * ((states.map (fun state =>
        ((events state).map (commonSignedEventValue N cap w L X G)).sum)).sum)
  have hstate (state) :
      ((events state).map (commonSignedEventValue N cap w L X
        (fun d => u * F d + v * G d))).sum =
        u * ((events state).map
          (commonSignedEventValue N cap w L X F)).sum +
        v * ((events state).map
          (commonSignedEventValue N cap w L X G)).sum := by
    calc
      _ = ((events state).map (fun ev =>
          u * commonSignedEventValue N cap w L X F ev +
          v * commonSignedEventValue N cap w L X G ev)).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro ev hev
            exact common_signed_event_linear N cap w L X F G u v ev
      _ = _ := list_sum_map_linear _ _ _ u v
  calc
    _ = (states.map (fun state =>
        u * ((events state).map
          (commonSignedEventValue N cap w L X F)).sum +
        v * ((events state).map
          (commonSignedEventValue N cap w L X G)).sum)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro state hs
          exact hstate state
    _ = _ := list_sum_map_linear _ _ _ u v

/-- Exact FOUR-source decomposition of the same actual fifth-exclusive
signed stopped delta. It is deliberately NOT the earlier eighth gain:
this theorem holds on the retained fifth event population that generates
the actual sixth high-q tail, without re-running that population for G. -/
theorem actual_fixed_fifth_receiver_decomposition
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) :
    actualFixedSignedFifthTail delta n e q om N cap w z L X
        (receiverTest N) =
      primeMass N *
        actualFixedSignedFifthTail delta n e q om N cap w z L X
          densityTest +
      actualFixedSignedFifthTail delta n e q om N cap w z L X
        (primitiveError N) -
      actualFixedSignedFifthTail delta n e q om N cap w z L X
        (modulusPrimeTerm N) -
      actualFixedSignedFifthTail delta n e q om N cap w z L X
        (chenCentrePrimeAPCount N N) := by
  let T : (ℕ → ℝ) → ℝ :=
    actualFixedSignedFifthTail delta n e q om N cap w z L X
  let A : ℕ → ℝ := fun d =>
    primeMass N * densityTest d + primitiveError N d
  let B : ℕ → ℝ := fun d => A d - modulusPrimeTerm N d
  let C : ℕ → ℝ := chenCentrePrimeAPCount N N
  have ha : T A = primeMass N * T densityTest + T (primitiveError N) := by
    simpa [T, A] using
      (actual_fixed_fifth_tail_linear delta n e q om N cap w z L X
        densityTest (primitiveError N) (primeMass N) (1 : ℝ))
  have hb : T B = T A - T (modulusPrimeTerm N) := by
    simpa [T, B, sub_eq_add_neg] using
      (actual_fixed_fifth_tail_linear delta n e q om N cap w z L X
        A (modulusPrimeTerm N) (1 : ℝ) (-1 : ℝ))
  have hfun : receiverTest N = fun d => B d - C d := by
    funext d
    simpa [B, A, C] using actual_receiver_four_source N d
  have hc : T (receiverTest N) = T B - T C := by
    rw [hfun]
    simpa [T, sub_eq_add_neg] using
      (actual_fixed_fifth_tail_linear delta n e q om N cap w z L X
        B C (1 : ℝ) (-1 : ℝ))
  change T (receiverTest N) =
    primeMass N * T densityTest + T (primitiveError N) -
      T (modulusPrimeTerm N) - T C
  rw [hc, hb, ha]

/-- SOURCE_ONLY: the old physical stopped difference is identified with
this SAME fixed signed fifth source, then decomposed into the genuinely
distinct primitive AP, modulus-prime and centre-prime error components.
No two unrelated sieve bounds have been subtracted. -/
theorem actual_stopped_delta_four_sources
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
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X densityTest +
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (primitiveError N) -
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (modulusPrimeTerm N) -
      actualFixedSignedFifthTail
          delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
            (chenCentrePrimeAPCount N N) := by
  rw [actual_stopped_difference_eq_common_signed_sixth_kernel
    delta n e q om N cap w z he hN epsilon heps X hX
      (receiverTest N)]
  exact actual_fixed_fifth_receiver_decomposition
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X

/-- A local, honest error payment ledger: NO primitive/AP, modulus-prime
or centre-prime component is assumed small. Their EXACT signed terms
belong to the same fixed fifth event population; taking absolutes is
done only AFTER the complete signed decomposition. -/
private theorem abs_three_term_payment (a b c : ℝ) :
    |a - b - c| ≤ |a| + |b| + |c| := by
  calc
    |a - b - c| ≤ |a - b| + |c| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add (a - b) (-c))
    _ ≤ (|a| + |b|) + |c| := by
      exact add_le_add_right
        (by simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add a (-b))) _
    _ = _ := by ring

/-- An explicit signed, same-rho PP adapter for the retained ACTUAL
fifth tail. The right side is NOT claimed o(H_N); full-q admission,
density-to-integral identification and separate physical outside bills
remain independent manuscript obligations. -/
theorem actual_stopped_primitive_density_gap_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (epsilon : ℝ) (heps : epsilon ≤ (1 / 500 : ℝ))
    (X : ℕ) (hX : (N : ℝ) ^ (3 / 5 : ℝ) ≤ (X : ℝ)) :
    |(rawStopped e q om N cap w z ((N : ℝ) ^ epsilon) X
        (receiverTest N) -
      licensedStopped delta n e q om N cap w z
        ((N : ℝ) ^ epsilon) X (receiverTest N)) -
      primeMass N * actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X densityTest| ≤
      |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (primitiveError N)| +
      |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (modulusPrimeTerm N)| +
      |actualFixedSignedFifthTail
        delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
          (chenCentrePrimeAPCount N N)| := by
  rw [actual_stopped_delta_four_sources
    delta n e q om N cap w z he hN epsilon heps X hX]
  let U := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X densityTest
  let A := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (primitiveError N)
  let B := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (modulusPrimeTerm N)
  let C := actualFixedSignedFifthTail
    delta n e q om N cap w z ((N : ℝ) ^ epsilon) X
      (chenCentrePrimeAPCount N N)
  change |(primeMass N * U + A - B - C) -
    primeMass N * U| ≤ |A| + |B| + |C|
  have hcancel :
      (primeMass N * U + A - B - C) - primeMass N * U =
        A - B - C := by ring
  rw [hcancel]
  exact abs_three_term_payment A B C


end
end ImbalancedChen.P4AOriginalFull87FifthSignedPrimitive
