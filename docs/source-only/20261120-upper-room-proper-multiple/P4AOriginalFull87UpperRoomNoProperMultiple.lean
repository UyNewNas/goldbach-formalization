import ImbalancedChen.P4AOriginalFull87ProperReceiverTail
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous one-shell/full-AP "proper divisor" tail was correct on an
UNRESTRICTED modulus, but not yet evaluated on the ACTUAL upper quotient
room. This file applies its original two-sided strict half-boundary.

For every admitted original PLUS-Rosser integer quotient a, the complete
physical modulus Q = a * (p :: pre).prod satisfies 2*Q > N. Every actual
prime receiver r=N-P lies in [0,N]. A strict proper multiple of Q would
satisfy 2*Q <= r <= N, an impossibility. The entire non-shell AP tail
therefore vanishes ON THIS ORIGINAL UPPER ROOM without cancellation,
smoothness, or an analytic estimate.

No new masks, surrogate coefficients or altered fifth/sixth occurrences.
Do not extend this conclusion to lower-half corrections or arbitrary q.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperRoomNoProperMultiple
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87FullUpperQuotientRoom (fullUpperQuotientRoom)
open P4AOriginalFull87ActualPrimitiveRosserRoom
  (actualPrimitiveRosserRoom actual_primitive_room_subset_full)
open P4AOriginalFull87OneShellAPGap
  (actualFullQPrimitiveAPFibre actualFullQOutsideOneShell
   actual_full_Q_AP_eq_shell_plus_outside originalFullQOutsideShellRoom
   frozenFullQPrimitiveAPRoom)
open P4AOriginalFull87ProperReceiverTail
  (actualFullQProperReceiverFibre proper_receiver_fibre_data
   outside_shell_card_eq_proper_receiver
   originalProperReceiverDivisorKernel originalProperReceiverDivisorConvolution
   originalProperReceiverConvolutionEvent frozenProperReceiverConvolution
   original_outside_shell_eq_receiver_convolution
   physical_after_lower_eq_mean_plus_full_AP_minus_proper_divisors)
open P4AOriginalFull87CarrierGlobalJumpInvoice (frozenSurvivorCarrierMeanRoom)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87FrozenSurvivorInvoice (keepFrozenUpperSurvivor)
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)
open P4AOriginalFull87FifthSignedPrimitive (actualFixedSignedFifthTail)
open P4AOriginalFull87StoppedUpperHalfPrimeDirect (lowerHalfReceiver)

/-- An admitted ORIGINAL upper room quotient has Q > N/2. In particular
Q=0 is impossible, including any zero-factor degenerate history. -/
theorem actual_upper_room_modulus_exceeds_half
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    N < 2 * (a * (p :: pre).prod) := by
  let b : ℕ := (p :: pre).prod
  have hf : a ∈ fullUpperQuotientRoom N X L pre p :=
    (actual_primitive_room_subset_full N cap w L X pre p) ha
  change a ∈ Finset.Ico
    ((N / (2 * b) + 1).max (X / b + 1))
    ((Nat.ceil L).min (N / b + 1)) at hf
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hf
  have hfloor : N / (2 * b) + 1 ≤ a :=
    le_trans (le_max_left _ _) hlo
  have hb : 0 < b := by
    by_contra hn
    have hz : b = 0 := Nat.eq_zero_of_not_pos hn
    have hupper : a < N / b + 1 :=
      lt_of_lt_of_le hhi (min_le_right _ _)
    simp [hz] at hfloor hupper
    omega
  have hquot : N / (2 * b) < a := by omega
  have hmul : N < a * (2 * b) :=
    (Nat.div_lt_iff_lt_mul (by omega : 0 < 2 * b)).mp hquot
  calc
    N < a * (2 * b) := hmul
    _ = 2 * (a * (p :: pre).prod) := by dsimp [b]; ring

/-- Strictly proper positive multiples require at least TWO copies,
not one. This is an integer-arithmetic fact; no measure argument. -/
private theorem no_proper_multiple_above_half
    {N Q r : ℕ} (hhalf : N < 2 * Q)
    (hrange : r ≤ N) (hdvd : Q ∣ r) (hproper : Q < r) : False := by
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    by_contra hnot
    have hcase : k = 0 ∨ k = 1 := by omega
    rcases hcase with hz | ho
    · subst k
      simp at hk
      omega
    · subst k
      simp at hk
      omega
  have htwice : 2 * Q ≤ r := by
    calc
      2 * Q = Q * 2 := by omega
      _ ≤ Q * k := Nat.mul_le_mul_left Q hk2
      _ = r := hk.symm
  omega

/-- No REAL receiver r=N-P can be a strict proper multiple of any
complete q from the original upper quotient room. -/
theorem actual_upper_room_no_proper_receiver
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a r : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    r ∉ actualFullQProperReceiverFibre N (a * (p :: pre).prod) := by
  intro hr
  obtain ⟨hdvd, hproper, hrange⟩ := proper_receiver_fibre_data hr
  exact no_proper_multiple_above_half
    (actual_upper_room_modulus_exceeds_half N cap w L X pre p a ha)
    hrange hdvd hproper

/-- The non-shell AP fibre has ZERO cardinality on the actual upper
room. This does not assert the same for arbitrary Q <= N/2. -/
theorem actual_upper_room_outside_shell_card_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    ((actualFullQOutsideOneShell N (a * (p :: pre).prod)).card : ℝ) = 0 := by
  have he : actualFullQProperReceiverFibre N
      (a * (p :: pre).prod) = ∅ := by
    ext r
    constructor
    · intro hr
      exact False.elim
        (actual_upper_room_no_proper_receiver N cap w L X pre p a r ha hr)
    · simp
  rw [outside_shell_card_eq_proper_receiver, he]
  simp

/-- Thus the TRUE complete-q AP count is exactly the single reflected
shell on the ACTUAL upper domain, not on unrestricted moduli. -/
theorem actual_upper_room_full_AP_eq_reflected_shell
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p a : ℕ)
    (ha : a ∈ actualPrimitiveRosserRoom N cap w L X pre p) :
    ((actualFullQPrimitiveAPFibre N (a * (p :: pre).prod)).card : ℝ) =
      if N - a * (p :: pre).prod ∈ chenAdditivePrimeCarrier N
      then 1 else 0 := by
  rw [actual_full_Q_AP_eq_shell_plus_outside]
  rw [actual_upper_room_outside_shell_card_zero N cap w L X pre p a ha]
  simp

/-- Actual receiver proper-divisor kernel vanishes POINTWISE for every
original receiver. This retains the original PLUS-beta signs. -/
theorem original_upper_proper_divisor_kernel_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p r : ℕ)
    (hr : r ∈ chenPrimeReceiverSource N) :
    originalProperReceiverDivisorKernel N cap w L X pre p r = 0 := by
  unfold originalProperReceiverDivisorKernel
  apply Finset.sum_eq_zero
  intro a ha
  have hnot : ¬(a * (p :: pre).prod ∣ r ∧
      a * (p :: pre).prod < r) := by
    intro hp
    exact no_proper_multiple_above_half
      (actual_upper_room_modulus_exceeds_half N cap w L X pre p a ha)
      (chenPrimeReceiverSource_data hr).2.1 hp.1 hp.2
  simp [hnot]

/-- The complete signed proper-divisor convolution is exactly zero
on the actual upper room; it does NOT require signed cancellation. -/
theorem original_upper_proper_divisor_convolution_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    originalProperReceiverDivisorConvolution N cap w L X pre p = 0 := by
  unfold originalProperReceiverDivisorConvolution
  apply Finset.sum_eq_zero
  intro r hr
  exact original_upper_proper_divisor_kernel_zero N cap w L X pre p r hr

theorem original_upper_outside_shell_room_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    originalFullQOutsideShellRoom N cap w L X pre p = 0 := by
  rw [original_outside_shell_eq_receiver_convolution]
  exact original_upper_proper_divisor_convolution_zero N cap w L X pre p

/-- Every signed original RAW-only/LICENSED-only event has zero outside
shell tail. The original BOTH and sixthFromBoth semantics stay zero. -/
theorem original_upper_proper_divisor_event_zero
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (ev : FifthSixthStoppedEvent ℕ) :
    originalProperReceiverConvolutionEvent N cap w L X ev = 0 := by
  cases ev with
  | sixthFromBoth pre fifth =>
      rfl
  | fifthExclusive fifth =>
      cases hk : fifth.kind with
      | rawOnly =>
          simp [originalProperReceiverConvolutionEvent, hk,
            original_upper_proper_divisor_convolution_zero]
      | licensedOnly =>
          simp [originalProperReceiverConvolutionEvent, hk,
            original_upper_proper_divisor_convolution_zero]
      | both =>
          simp [originalProperReceiverConvolutionEvent, hk]

/-- No occurrence is discarded. Each existing frozen state and actual
fifth/sixth event is evaluated on its original source, where the
proper-divisor correction vanishes. -/
theorem frozen_upper_proper_divisor_convolution_zero
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w epsilon : ℝ) (X : ℕ) :
    frozenProperReceiverConvolution
      delta n e q om N cap w epsilon X = 0 := by
  unfold frozenProperReceiverConvolution
  simp [original_upper_proper_divisor_event_zero]

/-- The REAL stopped physical ledger, with the lower receiver paid
exactly once, has NO non-shell AP tail on the original upper room.
This is finite arithmetic only; matching the manuscript's physical
rho_N(q), smooth W_N and H_N payment remain open. -/
theorem physical_after_lower_eq_mean_plus_true_full_AP
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
      delta n e q om N cap w epsilon X mean := by
  rw [physical_after_lower_eq_mean_plus_full_AP_minus_proper_divisors
    delta n e q om N cap w epsilon X mean he hN heps hX]
  rw [frozen_upper_proper_divisor_convolution_zero]
  ring

end
end ImbalancedChen.P4AOriginalFull87UpperRoomNoProperMultiple
