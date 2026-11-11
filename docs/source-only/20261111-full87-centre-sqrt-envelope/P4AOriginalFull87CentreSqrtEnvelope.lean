import ImbalancedChen.P4AOriginalFull87CentreCoprimeDivisors
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The original87 signed physical centre-prime invoice receives a genuinely
sublinear elementary envelope, not another absolute discrepancy interface.

Two elementary combinatorial arguments are given as Lean candidate bodies:
(1) count divisors by the small member of each factor pair; and
(2) count distinct target-prime divisors by the logarithm of the product
of the actual prime-factor list.

Hence the ACTUAL previous centreCoprimeDivisorBudget is at most
  4 * (Nat.sqrt N + 2) * Nat.log 2 N
for nonzero N. This is O(sqrt(N) log N) arithmetically, before any PP,
Mertens, PNT, or reserve inference. A formal comparison with the frozen
analytic H_N is NOT contained here.

No axiom, sorry, admit, native_decide, unsafe, new PP coefficient,
or extra paid error term.
-/

namespace ImbalancedChen.P4AOriginalFull87CentreSqrtEnvelope
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87EighthPrimeMeanLedger (gain primeMass densityTest receiverTest)
open P4AOriginalFull87SignedSharpReceiver (sharpPrimeError)
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87CentrePrimeFibres (centreDivisorPrimes)
open P4AOriginalFull87CentreCoprimeDivisors
  (centreCoprimeDivisorBudget original_full87_receiver_sharp_coprime_invoice)

/-- Elementary divisor-pair bound. Both d and m/d are *genuine*
positive divisors when m != 0. Divisors larger than sqrt(m)+1 are
injected, by their complement, into the same small interval. -/
private theorem card_divisors_le_two_sqrt_add (m : ℕ) :
    m.divisors.card ≤ 2 * (Nat.sqrt m + 2) := by
  classical
  by_cases hm : m = 0
  · simp [hm]
  let b := Nat.sqrt m + 1
  let small : Finset ℕ := Finset.Icc 1 b
  have hlt : m < b * b := by
    simpa [b, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt m
  have hsmallcard : small.card ≤ b + 1 := by
    have hs : small ⊆ Finset.range (b + 1) := by
      intro a ha
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_Icc.mp ha).2)
    simpa using (Finset.card_le_card hs)
  have hcover :
      m.divisors ⊆ small ∪ small.image (fun a => m / a) := by
    intro d hd
    have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    by_cases hdsmall : d ≤ b
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_Icc.mpr ⟨hdpos, hdsmall⟩))
    · let a : ℕ := m / d
      have hmul : a * d = m := Nat.div_mul_cancel hdvd
      have hapos : 0 < a := by
        by_contra h
        have ha0 : a = 0 := by omega
        have hm0 : m = 0 := by simpa [ha0] using hmul.symm
        exact hm hm0
      have hasmall : a ≤ b := by
        by_contra h
        have ha : b + 1 ≤ a := by omega
        have hdb : b + 1 ≤ d := by omega
        have hprod : (b + 1) * (b + 1) ≤ a * d :=
          Nat.mul_le_mul ha hdb
        nlinarith [hprod, hmul, hlt]
      have hquot : m / a = d := by
        rw [← hmul]
        exact Nat.mul_div_cancel_left d hapos
      exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_image.mpr
          ⟨a, Finset.mem_Icc.mpr ⟨hapos, hasmall⟩, hquot⟩))
  calc
    m.divisors.card ≤
        (small ∪ small.image (fun a => m / a)).card :=
      Finset.card_le_card hcover
    _ ≤ small.card + (small.image (fun a => m / a)).card :=
      Finset.card_union_le _ _
    _ ≤ small.card + small.card :=
      add_le_add_left Finset.card_image_le _
    _ ≤ (b + 1) + (b + 1) := add_le_add hsmallcard hsmallcard
    _ = 2 * (Nat.sqrt m + 2) := by dsimp [b]; omega

/-- The product of a list of actual factors >=2 dominates 2^length. -/
private theorem two_pow_length_le_prod (xs : List ℕ)
    (hxs : ∀ a ∈ xs, 2 ≤ a) : 2 ^ xs.length ≤ xs.prod := by
  induction xs with
  | nil => norm_num
  | cons a rest ih =>
      have ha : 2 ≤ a := hxs a (by simp)
      have hr : ∀ x ∈ rest, 2 ≤ x := by
        intro x hx
        exact hxs x (by simp [hx])
      have hle : 2 * 2 ^ rest.length ≤ a * rest.prod :=
        Nat.mul_le_mul ha (ih hr)
      simpa only [List.length_cons, List.prod_cons, pow_succ, mul_comm] using hle

/-- The literal centre-divisor prime list cannot be larger than the
number of prime factors (with multiplicity) of N, which is at most log_2 N. -/
private theorem centre_prime_card_le_log_two (N : ℕ) (hN : N ≠ 0) :
    (centreDivisorPrimes N).card ≤ Nat.log 2 N := by
  classical
  have hsubset :
      centreDivisorPrimes N ⊆ N.primeFactorsList.toFinset := by
    intro P hP
    have hh := Finset.mem_filter.mp hP
    have hp : Nat.Prime P := (mem_chenPrimePrefix.mp hh.1).2
    simpa only [List.mem_toFinset] using
      ((Nat.mem_primeFactorsList hN).mpr ⟨hp, hh.2⟩)
  have hcount : (centreDivisorPrimes N).card ≤
      N.primeFactorsList.length := by
    exact (Finset.card_le_card hsubset).trans
      (List.toFinset_card_le N.primeFactorsList)
  have hpow : 2 ^ N.primeFactorsList.length ≤ N := by
    calc
      _ ≤ N.primeFactorsList.prod := two_pow_length_le_prod _
        (by intro p hp; exact (Nat.prime_of_mem_primeFactorsList hp).two_le)
      _ = N := Nat.prod_primeFactorsList hN
  exact hcount.trans (Nat.le_log_of_pow_le (by norm_num) hpow)

/-- First substantial uniform bound, still counting the SAME original
centre-divisor primes and the SAME complete-modulus coprime divisor bill. -/
theorem original87_centre_coprime_budget_le_sqrt_count (N : ℕ) :
    centreCoprimeDivisorBudget N ≤
      4 * (((Nat.sqrt N + 2 : ℕ) : ℝ)) *
        (((centreDivisorPrimes N).card : ℕ) : ℝ) := by
  have hterm (P : ℕ) :
      (((((N - P).divisors.filter (fun d => Nat.Coprime d N)).card : ℕ) : ℝ) ≤
        2 * (((Nat.sqrt N + 2 : ℕ) : ℝ)) := by
    have hf : ((N - P).divisors.filter
        (fun d => Nat.Coprime d N)).card ≤ (N - P).divisors.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hs : Nat.sqrt (N - P) ≤ Nat.sqrt N :=
      Nat.sqrt_le_sqrt (Nat.sub_le N P)
    have hn : ((N - P).divisors.filter
        (fun d => Nat.Coprime d N)).card ≤ 2 * (Nat.sqrt N + 2) := by
      calc
        _ ≤ (N - P).divisors.card := hf
        _ ≤ 2 * (Nat.sqrt (N - P) + 2) :=
          card_divisors_le_two_sqrt_add _
        _ ≤ 2 * (Nat.sqrt N + 2) := by omega
    exact_mod_cast hn
  unfold centreCoprimeDivisorBudget
  calc
    2 * ∑ P ∈ centreDivisorPrimes N,
      (((((N - P).divisors.filter (fun d => Nat.Coprime d N)).card : ℕ) : ℝ)
        ≤ 2 * ∑ P ∈ centreDivisorPrimes N,
          (2 * (((Nat.sqrt N + 2 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun P _ => hterm P))
        (by norm_num)
    _ = 4 * (((Nat.sqrt N + 2 : ℕ) : ℝ)) *
        (((centreDivisorPrimes N).card : ℕ) : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Explicit O(sqrt N log N) arithmetic envelope for the actual centre bill.
This is an internal finite inequality, NOT a substitute for the H_N
normalization or for either signed PP hypothesis. -/
def centreSqrtLogBudget (N : ℕ) : ℝ :=
  4 * (((Nat.sqrt N + 2 : ℕ) : ℝ)) * ((Nat.log 2 N : ℕ) : ℝ)

theorem original87_centre_coprime_budget_le_sqrt_log
    (N : ℕ) (hN : N ≠ 0) :
    centreCoprimeDivisorBudget N ≤ centreSqrtLogBudget N := by
  calc
    centreCoprimeDivisorBudget N ≤
        4 * (((Nat.sqrt N + 2 : ℕ) : ℝ)) *
          (((centreDivisorPrimes N).card : ℕ) : ℝ) :=
      original87_centre_coprime_budget_le_sqrt_count N
    _ ≤ centreSqrtLogBudget N := by
      unfold centreSqrtLogBudget
      exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast centre_prime_card_le_log_two N hN)
        (by positivity)

/-- This envelope enters the SAME actual sixth-minus-eighth receiver
identity, with independent original signed sharp-PP premises and WITHOUT
reintroducing the already cancelled modulus-prime bill. -/
theorem original87_receiver_sharp_sqrt_log_invoice
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (boundSixth boundEighth : ℝ)
    (hN : ¬Nat.Prime N) (hN0 : N ≠ 0)
    (hSixth :
      |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ boundSixth)
    (hEighth :
      |physical (policy (width r) n e q om (N : ℝ)) N cap w z L
        (sharpPrimeError N)| ≤ boundEighth) :
    |gain (width r) n e q om N cap w z L (receiverTest N) -
      primeMass N * gain (width r) n e q om N cap w z L densityTest| ≤
      boundSixth + boundEighth + centreSqrtLogBudget N := by
  have hprior := original_full87_receiver_sharp_coprime_invoice
    r n e q om N cap w z L boundSixth boundEighth hN hSixth hEighth
  have hcentre := original87_centre_coprime_budget_le_sqrt_log N hN0
  linarith

end
end ImbalancedChen.P4AOriginalFull87CentreSqrtEnvelope
