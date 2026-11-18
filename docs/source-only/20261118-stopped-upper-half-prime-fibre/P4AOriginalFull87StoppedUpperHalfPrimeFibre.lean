import ImbalancedChen.P4AOriginalFull87StoppedUpperHalfPrimeDirect
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A reindexing of the ACTUAL stopped upper-half original-prime invoice.
The prior proof expressed each complete a*(p::pre).prod receiver test as
the indicator of the genuine additive prime P = N - a*(p::pre).prod.

Here we reverse the finite summation: each prime P is charged its
UNIQUE Rosser index a = (N-P)/(p::pre).prod, if that quotient is really
in the ORIGINAL fifth-power-filtered PLUS-Rosser support and its
multiplication equals N-P. This is not a new AP theorem or density
input, nor a claim that the resulting signed prime invoice is small.

Both strict boundaries X < N-P and 2*P < N are preserved. Each actual
post-fifth sixth occurrence and the original mass/sign remain intact.
No external number-theoretic input or proof escape is introduced.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedUpperHalfPrimeFibre
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedUpperHalfPrimeDirect
  (upperHalfReceiver large_fifth_upper_half_prime_invoice)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthRosserIndices largeFifthPlusAttachment)
open P4AOriginalFull87CommonSixthSignedKernel (commonLargeSixthKernel)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)

/-- Additive-prime tagging is a finite Fubini identity. Every original
Rosser index is counted once, at P=N-a*b, only when the genuine
additive-prime carrier contains that P. -/
private theorem finite_prime_tag_exchange
    (S C : Finset ℕ) (f : ℕ → ℕ) (gate : ℕ → Prop)
    [DecidablePred gate] (beta : ℕ → ℝ) :
    (∑ a ∈ S, if gate a ∧ f a ∈ C then beta a else 0) =
      ∑ P ∈ C, ∑ a ∈ S,
        if gate a ∧ f a = P then beta a else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hg : gate a
  · simp [hg, Finset.sum_ite_eq']
  · simp [hg]

/-- General positive target q: the fixed product b leaves at most one
original Rosser index, q/b. Multiplicative equality is checked exactly;
divisor rounding alone is not enough. -/
private theorem positive_product_unique_quotient
    (S : Finset ℕ) (beta : ℕ → ℝ)
    (b q : ℕ) (hq : 0 < q) :
    (∑ a ∈ S, if a * b = q then beta a else 0) =
      if q / b ∈ S ∧ (q / b) * b = q then beta (q / b) else 0 := by
  classical
  by_cases hb : b = 0
  · simp [hb, Nat.ne_of_gt hq]
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb
  have hiff (a : ℕ) :
      (a * b = q) ↔
        (a = q / b ∧ (q / b) * b = q) := by
    constructor
    · intro heq
      have hdiv : q / b = a := by
        rw [← heq]
        exact Nat.mul_div_cancel a hbpos
      exact ⟨hdiv.symm, by simpa [hdiv] using heq⟩
    · rintro ⟨rfl, heq⟩
      exact heq
  have hsum :
      (∑ a ∈ S, if a * b = q then beta a else 0) =
        ∑ a ∈ S,
          if a = q / b ∧ (q / b) * b = q then beta a else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hiff a]
  rw [hsum]
  by_cases hmul : (q / b) * b = q
  · simp [hmul, Finset.sum_ite_eq']
  · simp [hmul]

/-- The fibre at a genuine original additive prime P has a single
potential Rosser index. The strict high-q boundary and strict
upper-half boundary are tested at the FULL modulus N-P. -/
private theorem original_prime_fibre_single_quotient
    (N X b P : ℕ) (S : Finset ℕ) (beta : ℕ → ℝ)
    (hP : P ∈ chenAdditivePrimeCarrier N) :
    (∑ a ∈ S,
      if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
          N - a * b = P then beta a else 0) =
      if X < N - P ∧ N < 2 * (N - P) ∧
          (N - P) / b ∈ S ∧
          ((N - P) / b) * b = N - P
      then beta ((N - P) / b) else 0 := by
  classical
  have hPN : P < N := (mem_chenAdditivePrimeCarrier.mp hP).1
  have hq : 0 < N - P := by omega
  have hiff (a : ℕ) :
      ((X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
          N - a * b = P) ↔
        ((X < N - P ∧ N < 2 * (N - P)) ∧
          a * b = N - P) := by
    constructor
    · rintro ⟨⟨hx, hh, hle⟩, heq⟩
      have hab : a * b = N - P := by omega
      exact ⟨⟨by omega, by omega⟩, hab⟩
    · rintro ⟨⟨hx, hh⟩, hab⟩
      exact ⟨⟨by omega, by omega, by omega⟩, by omega⟩
  calc
    (∑ a ∈ S,
      if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
          N - a * b = P then beta a else 0) =
        ∑ a ∈ S,
          if (X < N - P ∧ N < 2 * (N - P)) ∧
              a * b = N - P then beta a else 0 := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hiff a]
    _ = if X < N - P ∧ N < 2 * (N - P) then
          (∑ a ∈ S, if a * b = N - P then beta a else 0)
        else 0 := by
          by_cases hg : X < N - P ∧ N < 2 * (N - P)
          <;> simp [hg]
    _ = _ := by
      rw [positive_product_unique_quotient S beta b (N - P) hq]
      by_cases hx : X < N - P
      <;> by_cases hh : N < 2 * (N - P)
      <;> simp [hx, hh]

/-- Exact reindexing of the old upper-half signed finite PLUS-beta
sum by ORIGINAL additive primes P, with no lost sixth occurrences.
The condition 2*P<N is equivalent to N<2*(N-P) because P<N.
Neither the old Rosser support nor its beta coefficient is replaced. -/
theorem original_upper_half_prime_rosser_reindex
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ) :
    largeFifthPlusAttachment N cap w L X
        (upperHalfReceiver N) pre p =
      ∑ P ∈ chenAdditivePrimeCarrier N,
        if 2 * P < N ∧ X < N - P ∧
            (N - P) / (p :: pre).prod ∈
              largeFifthRosserIndices N cap w X pre ∧
            ((N - P) / (p :: pre).prod) *
              (p :: pre).prod = N - P
        then actualSmallRosserPlus N cap w L
          ((N - P) / (p :: pre).prod) else 0 := by
  classical
  let b : ℕ := (p :: pre).prod
  let S : Finset ℕ := largeFifthRosserIndices N cap w X pre
  let beta : ℕ → ℝ := actualSmallRosserPlus N cap w L
  have htag :
      (∑ a ∈ S,
        if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
            (N - a * b) ∈ chenAdditivePrimeCarrier N
        then beta a else 0) =
        ∑ P ∈ chenAdditivePrimeCarrier N,
          ∑ a ∈ S,
            if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
                N - a * b = P
            then beta a else 0 := by
    exact finite_prime_tag_exchange S (chenAdditivePrimeCarrier N)
      (fun a => N - a * b)
      (fun a => X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) beta
  rw [large_fifth_upper_half_prime_invoice]
  change
    (∑ a ∈ S,
      if X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N ∧
          (N - a * b).Prime ∧ Nat.Coprime (N - a * b) N
      then beta a else 0) = _
  have hpoint (a : ℕ) :
      (if X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N ∧
          (N - a * b).Prime ∧ Nat.Coprime (N - a * b) N
       then beta a else 0) =
      (if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
           N - a * b ∈ chenAdditivePrimeCarrier N
       then beta a else 0) := by
    simp [mem_chenAdditivePrimeCarrier_iff_le, Nat.sub_le, and_assoc]
  calc
    (∑ a ∈ S,
      if X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N ∧
          (N - a * b).Prime ∧ Nat.Coprime (N - a * b) N
      then beta a else 0) =
        ∑ a ∈ S,
          if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
              N - a * b ∈ chenAdditivePrimeCarrier N
          then beta a else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hpoint a
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
          ∑ a ∈ S,
            if (X < a * b ∧ N < 2 * (a * b) ∧ a * b ≤ N) ∧
                N - a * b = P
            then beta a else 0 := htag
    _ = ∑ P ∈ chenAdditivePrimeCarrier N,
          if X < N - P ∧ N < 2 * (N - P) ∧
              (N - P) / b ∈ S ∧ ((N - P) / b) * b = N - P
          then beta ((N - P) / b) else 0 := by
            apply Finset.sum_congr rfl
            intro P hP
            exact original_prime_fibre_single_quotient
              N X b P S beta hP
    _ = _ := by
      apply Finset.sum_congr rfl
      intro P hP
      have hPN : P < N := (mem_chenAdditivePrimeCarrier.mp hP).1
      have hhalf : (N < 2 * (N - P)) ↔ (2 * P < N) := by omega
      change
        (if X < N - P ∧ N < 2 * (N - P) ∧
            (N - P) / b ∈ S ∧ ((N - P) / b) * b = N - P
         then beta ((N - P) / b) else 0) = _
      by_cases hx : X < N - P
      <;> by_cases hh : 2 * P < N
      <;> simp [hx, hh, hhalf, and_left_comm, and_comm, and_assoc, b, S, beta]

/-- Reindexing at the SAME actual fifth event and ordered sixth suffix.
This still has the original signed tree mass, all repeated occurrences
and the exact old PLUS-beta quotient, rather than fixed physical rho. -/
theorem common_sixth_upper_half_prime_reindex
    (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (fifth : FifthStoppedEvent ℕ) :
    commonLargeSixthKernel N cap w L X
        (upperHalfReceiver N) fifth =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (∑ P ∈ chenAdditivePrimeCarrier N,
            if 2 * P < N ∧ X < N - P ∧
                (N - P) / (p :: fifth.selectedAfter).prod ∈
                  largeFifthRosserIndices N cap w X fifth.selectedAfter ∧
                ((N - P) / (p :: fifth.selectedAfter).prod) *
                  (p :: fifth.selectedAfter).prod = N - P
            then actualSmallRosserPlus N cap w L
              ((N - P) / (p :: fifth.selectedAfter).prod)
            else 0))).sum := by
  unfold commonLargeSixthKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [original_upper_half_prime_rosser_reindex]

end
end ImbalancedChen.P4AOriginalFull87StoppedUpperHalfPrimeFibre
