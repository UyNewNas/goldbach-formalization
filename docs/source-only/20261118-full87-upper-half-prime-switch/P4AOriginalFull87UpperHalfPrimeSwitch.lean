import ImbalancedChen.P4AOriginalFull87SuperNCancellation
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A non-asymptotic SWITCH of the genuinely large full-modulus region.
When N < 2*d, the real target-deleted receiver fibre is either empty
or the singleton {d}. This converts a high-half modulus sum with the
ORIGINAL signed coefficient into a sum over the ORIGINAL prime source,
without an unsigned replacement, new policy, or external PP invocation.

The last theorem splits the original RAW-minus-LICENSED physical high-q
difference into this prime-switched high-half and the untouched lower
half. In particular it does not claim the high-half is o(H_N).
The full integer modulus and both strict boundaries X<d and N<2*d
are preserved; equality belongs to the lower-half complement.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperHalfPrimeSwitch
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87EighthPrimeMeanLedger
  (receiverTest physical_linear)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalLicensedSixthSignedLedger (physical)

/-- A positive actual receiver divisible by a modulus larger than N/2
must equal that COMPLETE modulus. No prime distribution result is used. -/
private theorem half_receiver_dvd_eq
    (N d n : ℕ)
    (hhalf : N < 2 * d)
    (hn : n ∈ chenPrimeReceiverSource N)
    (hdiv : d ∣ n) : n = d := by
  obtain ⟨hnpos, hnle, _⟩ := chenPrimeReceiverSource_data hn
  have hmul : n / d * d = n := Nat.div_mul_cancel hdiv
  have hquotpos : 0 < n / d := by
    by_contra hnot
    have hz : n / d = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz] at hmul
    simp at hmul
    omega
  have hquotlt : n / d < 2 := by
    by_contra hnot
    have hge : 2 ≤ n / d := by omega
    have htwod : 2 * d ≤ n := by
      calc
        2 * d ≤ (n / d) * d := Nat.mul_le_mul_right d hge
        _ = n := hmul
    omega
  have hquot : n / d = 1 := by omega
  calc
    n = n / d * d := hmul.symm
    _ = d := by simp [hquot]

/-- The ORIGINAL receiver fibre, with no reselected prime set, is an
exact singleton or empty for d>N/2. This is stronger than floor(N/d)<=1. -/
theorem receiver_upper_half_fibre_singleton (N d : ℕ)
    (hhalf : N < 2 * d) :
    (chenPrimeReceiverSource N).filter (fun n => d ∣ n) =
      if d ∈ chenPrimeReceiverSource N then {d} else ∅ := by
  classical
  let R := chenPrimeReceiverSource N
  change R.filter (fun n => d ∣ n) = if d ∈ R then {d} else ∅
  by_cases hmem : d ∈ R
  · have hf : R.filter (fun n => d ∣ n) = {d} := by
      ext n
      constructor
      · intro hn
        have heq : n = d := half_receiver_dvd_eq N d n hhalf
          (Finset.mem_filter.mp hn).1 (Finset.mem_filter.mp hn).2
        exact Finset.mem_singleton.mpr heq
      · intro hn
        have heq : n = d := Finset.mem_singleton.mp hn
        subst n
        exact Finset.mem_filter.mpr ⟨hmem, dvd_rfl⟩
    simp [hmem, hf]
  · have hf : R.filter (fun n => d ∣ n) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro n hn
      obtain ⟨hsrc, hdiv⟩ := Finset.mem_filter.mp hn
      have heq : n = d := half_receiver_dvd_eq N d n hhalf hsrc hdiv
      exact hmem (heq ▸ hsrc)
    simp [hmem, hf]

/-- Exact indicator, not merely a count bound. In particular d=0 and
the deleted zero-receiver are never inserted into this formula. -/
theorem receiver_upper_half_indicator (N d : ℕ)
    (hhalf : N < 2 * d) :
    receiverTest N d =
      if d ∈ chenPrimeReceiverSource N then 1 else 0 := by
  classical
  unfold receiverTest
  rw [receiver_upper_half_fibre_singleton N d hhalf]
  split_ifs <;> simp

/-- Switching the ORIGINAL modulus-indexed signed weight to its
corresponding original prime P, with d=N-P. The input S may contain
unrelated or repeated-prime-factor moduli, and is not silently replaced
by a new sieve-policy source. An arbitrary real weight retains signs. -/
theorem receiver_upper_half_modulus_prime_switch
    (N : ℕ) (S : Finset ℕ) (weight : ℕ → ℝ) :
    (∑ d ∈ S, if N < 2 * d then weight d * receiverTest N d else 0) =
      ∑ P ∈ chenAdditivePrimeCarrier N,
        if N - P ∈ S ∧ N < 2 * (N - P)
        then weight (N - P) else 0 := by
  classical
  let R := chenPrimeReceiverSource N
  have hpoint (d : ℕ) :
      (if N < 2 * d then weight d * receiverTest N d else 0) =
      (if d ∈ R ∧ N < 2 * d then weight d else 0) := by
    by_cases hh : N < 2 * d
    · simp [hh, R, receiver_upper_half_indicator N d hh]
    · simp [hh]
  calc
    (∑ d ∈ S, if N < 2 * d then weight d * receiverTest N d else 0)
        = ∑ d ∈ S, if d ∈ R ∧ N < 2 * d then weight d else 0 := by
          apply Finset.sum_congr rfl
          intro d _
          exact hpoint d
    _ = ∑ d ∈ S.filter (fun d => d ∈ R ∧ N < 2 * d), weight d := by
          rw [Finset.sum_filter]
    _ = ∑ d ∈ R.filter (fun d => d ∈ S ∧ N < 2 * d), weight d := by
          congr 1
          ext d
          simp only [Finset.mem_filter]
          tauto
    _ = ∑ d ∈ R,
          if d ∈ S ∧ N < 2 * d then weight d else 0 := by
          rw [Finset.sum_filter]
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
          if N - P ∈ S ∧ N < 2 * (N - P)
          then weight (N - P) else 0 := by
          simpa only [R] using
            (sum_chenPrimeReceiverSource N
              (fun d => if d ∈ S ∧ N < 2 * d then weight d else 0))

/-- Half-open separation at the integer boundary 2*d=N. It is a
geometric partition of THE SAME high-q receiver, not an error estimate. -/
def upperHalfHighQ (N X d : ℕ) : ℝ :=
  if N < 2 * d then highQTest X (receiverTest N) d else 0

def lowerHalfHighQ (N X d : ℕ) : ℝ :=
  if 2 * d ≤ N then highQTest X (receiverTest N) d else 0

theorem highq_receiver_halves (N X d : ℕ) :
    highQTest X (receiverTest N) d =
      upperHalfHighQ N X d + lowerHalfHighQ N X d := by
  by_cases hh : N < 2 * d
  · have hn : ¬ 2 * d ≤ N := Nat.not_le.mpr hh
    simp [upperHalfHighQ, lowerHalfHighQ, hh, hn]
  · have hl : 2 * d ≤ N := by omega
    simp [upperHalfHighQ, lowerHalfHighQ, hh, hl]

/-- Full-q, strict high-q variant. The original small Rosser beta and
rough coefficient are carried by weight; no new sign or multiplicity
constraints are imposed. -/
theorem receiver_upper_half_highq_switch
    (N X : ℕ) (S : Finset ℕ) (weight : ℕ → ℝ) :
    (∑ d ∈ S, weight d * upperHalfHighQ N X d) =
      ∑ P ∈ chenAdditivePrimeCarrier N,
        if N - P ∈ S ∧ N < 2 * (N - P) then
          (if X < N - P then weight (N - P) else 0)
        else 0 := by
  have hsum :
      (∑ d ∈ S, weight d * upperHalfHighQ N X d) =
      ∑ d ∈ S, if N < 2 * d then
        (if X < d then weight d else 0) * receiverTest N d
        else 0 := by
    apply Finset.sum_congr rfl
    intro d _
    by_cases hh : N < 2 * d
    · by_cases hx : X < d
      · simp [upperHalfHighQ, highQTest, hh, hx]
      · simp [upperHalfHighQ, highQTest, hh, hx]
    · simp [upperHalfHighQ, hh]
  exact hsum.trans
    (receiver_upper_half_modulus_prime_switch N S
      (fun d => if X < d then weight d else 0))

/-- Actual P1.4 physical rho, not an arbitrary replacement coefficient.
The complete rough modulus set and the signed small-beta attachment
remain those of P. High-half receiver terms return to original primes. -/
theorem actual_physical_upper_half_highq_prime_switch
    (P : Bool → List ℕ → Bool)
    (N cap X : ℕ) (w z L : ℝ) :
    physical P N cap w z L (upperHalfHighQ N X) =
      ∑ Q ∈ chenAdditivePrimeCarrier N,
        if N - Q ∈ actualSmallRoughModuli (P false) N cap w z ∧
            N < 2 * (N - Q) then
          (if X < N - Q then
            actualSmallRoughRho (P false) N cap w z L (N - Q)
          else 0)
        else 0 := by
  unfold physical
  exact receiver_upper_half_highq_switch N X
    (actualSmallRoughModuli (P false) N cap w z)
    (actualSmallRoughRho (P false) N cap w z L)

/-- Exact signed physical decomposition; the lower half is untouched,
not discarded or treated by PP. The same frozen policy is used on both
halves so this introduces no synthetic signed saving. -/
theorem actual_physical_highq_halves
    (P : Bool → List ℕ → Bool)
    (N cap X : ℕ) (w z L : ℝ) :
    physical P N cap w z L (highQTest X (receiverTest N)) =
      physical P N cap w z L (upperHalfHighQ N X) +
      physical P N cap w z L (lowerHalfHighQ N X) := by
  have hf :
      highQTest X (receiverTest N) =
        fun d => (1 : ℝ) * upperHalfHighQ N X d +
          (1 : ℝ) * lowerHalfHighQ N X d := by
    funext d
    simpa only [one_mul] using highq_receiver_halves N X d
  rw [hf]
  simpa only [one_mul] using
    (physical_linear P N cap w z L
      (upperHalfHighQ N X) (lowerHalfHighQ N X) (1 : ℝ) (1 : ℝ))

/-- Both ORIGINAL upper policies, without recomputing either source.
This makes the high-half prime-switch and the lower-half remaining
analytic liability available to the actual RAW-minus-LICENSED rho. -/
theorem actual_raw_licensed_highq_halves
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w z L : ℝ) :
    physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (highQTest X (receiverTest N)) -
      physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        N cap w z L (highQTest X (receiverTest N)) =
      (physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (upperHalfHighQ N X) -
       physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        N cap w z L (upperHalfHighQ N X)) +
      (physical
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        N cap w z L (lowerHalfHighQ N X) -
       physical
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        N cap w z L (lowerHalfHighQ N X)) := by
  rw [actual_physical_highq_halves, actual_physical_highq_halves]
  ring

end
end ImbalancedChen.P4AOriginalFull87UpperHalfPrimeSwitch
