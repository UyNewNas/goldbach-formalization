import ImbalancedChen.P4AOriginalFull87StoppedUpperHalfPrimeFibre
import ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The preceding original upper-half P-fibre still summed over the
centre-deleted additive-prime carrier. On the *actual* small-Rosser
support, a is coprime to N; all actual fifth-selected rough primes
and every genuine sixth occurrence are also coprime to N.

Thus q = a * (p :: pre).prod is coprime to N. For q = N - P, the
centre-deletion condition Coprime P N is automatic. We may enlarge
the P-index carrier to the literal unmasked prime prefix, without
adding or removing a nonzero term. The quotient-support and exact
multiplication tests are NOT removed; in particular this theorem
does not confer PP admissibility on an arithmetic-filtered sum.

The actual fifth producer, ordered sixth list, signed mass, strict
2*P<N and X<N-P gates, and occurrence multiplicities are unchanged.
No asymptotic bound or external analytic theorem is used.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87StoppedUpperHalfPrimeDirect (upperHalfReceiver)
open P4AOriginalFull87StoppedUpperHalfPrimeFibre
  (original_upper_half_prime_rosser_reindex)
open P4AOriginalFull87PlusBetaPowerFilter
  (largeFifthRosserIndices largeFifthPlusAttachment)
open P4AOriginalFull87CommonSixthSignedKernel (commonLargeSixthKernel)
open P4AOriginalFull87FirstFifthStoppedEvents (FifthStoppedEvent)
open P4AOriginalFull87FifthSixthStoppedEvents (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice (actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization (sharedRankFour)
open P4AOriginalFull87OrderedSixthSuffix
  (actual_event_joined_history_original_rough)

/-- List product is coprime to N when every literal occurrence is.
No toFinset conversion or occurrence deduplication is used. -/
private theorem coprime_list_product
    (N : ℕ) (xs : List ℕ)
    (hc : ∀ r ∈ xs, Nat.Coprime r N) :
    Nat.Coprime xs.prod N := by
  induction xs with
  | nil =>
      simpa using (Nat.coprime_one_left N)
  | cons r rest ih =>
      have hr : Nat.Coprime r N := hc r (by simp)
      have hrest : ∀ t ∈ rest, Nat.Coprime t N := by
        intro t ht
        exact hc t (by simp [ht])
      simpa only [List.prod_cons] using hr.mul_left (ih hrest)

/-- Source-level rough membership suffices for the complete fifth/sixth
product to be coprime to N. It uses the actual lower w and upper z
as separate parameters; no rho0 endpoint substitution occurs. -/
private theorem original_rough_six_product_coprime
    (N cap : ℕ) (w z : ℝ) (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    Nat.Coprime (p :: pre).prod N := by
  apply coprime_list_product N (p :: pre)
  intro r hr
  have hmem : r ∈ roughPrimeUniverse N cap w z := hrough r hr
  exact (mem_roughPrimeUniverse_prime hmem).coprime_iff_not_dvd.mpr
    (mem_roughPrimeUniverse_not_dvd hmem)

/-- A FULL original Rosser-rough modulus, with no discarded a or sixth
occurrence, is coprime to the Goldbach centre. -/
theorem original_full_modulus_coprime_target
    (N cap : ℕ) (w z : ℝ) (pre : List ℕ) (p a : ℕ)
    (ha : a ∈ largeFifthRosserIndices N cap w 0 pre)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    Nat.Coprime (a * (p :: pre).prod) N := by
  have hSupport : a ∈ actualSmallRosserSupport N cap w :=
    (Finset.mem_filter.mp ha).1
  exact (actualSmallRosserSupport_coprime_target N cap w hSupport).mul_left
    (original_rough_six_product_coprime N cap w z pre p hrough)

/-- For any original fifth Rosser support (with the genuine X filter)
and rough sixth history, the complementary P is automatically
coprime to N whenever the checked quotient reproduces N-P. -/
private theorem original_quotient_fibre_coprime_prime
    (N cap : ℕ) (w z : ℝ) (X P : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hPN : P ≤ N)
    (ha : (N - P) / (p :: pre).prod ∈
      largeFifthRosserIndices N cap w X pre)
    (hmul : ((N - P) / (p :: pre).prod) *
      (p :: pre).prod = N - P)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    Nat.Coprime P N := by
  have hSupport :
      (N - P) / (p :: pre).prod ∈ actualSmallRosserSupport N cap w :=
    (Finset.mem_filter.mp ha).1
  have hfull : Nat.Coprime
      (((N - P) / (p :: pre).prod) * (p :: pre).prod) N :=
    (actualSmallRosserSupport_coprime_target N cap w hSupport).mul_left
      (original_rough_six_product_coprime N cap w z pre p hrough)
  have hq : Nat.Coprime (N - P) N := by
    simpa only [hmul] using hfull
  exact (Nat.coprime_self_sub_left hPN).mp hq

/-- An actual P fibre can be summed over the ORIGINAL unmasked
prime prefix, because the Rosser/rough support already eliminates
centre divisors. The original quotient test stays literal. -/
theorem original_upper_half_unmasked_prime_prefix
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (pre : List ℕ) (p : ℕ)
    (hrough : ∀ r ∈ p :: pre, r ∈ roughPrimeUniverse N cap w z) :
    largeFifthPlusAttachment N cap w L X
        (upperHalfReceiver N) pre p =
      ∑ P ∈ chenPrimePrefix N,
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
  rw [original_upper_half_prime_rosser_reindex]
  rw [chenAdditivePrimeCarrier_eq_prefix_filter]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro P hP
  have hPN : P ≤ N := (mem_chenPrimePrefix.mp hP).1
  have hprime : Nat.Prime P := (mem_chenPrimePrefix.mp hP).2
  by_cases hgate :
      2 * P < N ∧ X < N - P ∧ (N - P) / b ∈ S ∧
        ((N - P) / b) * b = N - P
  · have hcop : Nat.Coprime P N :=
      original_quotient_fibre_coprime_prime N cap w z X P pre p
        hPN hgate.2.2.1 hgate.2.2.2 hrough
    have hnot : ¬ P ∣ N := hprime.coprime_iff_not_dvd.mp hcop
    simp [b, S, beta, hgate, hnot]
  · simp [b, S, beta, hgate]

/-- Same true receiver-generated fifthExclusive producer and same
ordered sixth occurrence list. The event source is NOT regenerated
from the unmasked prime prefix. -/
theorem actual_common_sixth_unmasked_prime_prefix
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth delta n e q om N cap w L X
        (P4AOriginalFull87EighthPrimeMeanLedger.receiverTest N) state) :
    commonLargeSixthKernel N cap w L X
        (upperHalfReceiver N) fifth =
      (fifth.remainingAfter.map (fun p =>
        signedTreeCoefficient true fifth.massAfter *
          (∑ P ∈ chenPrimePrefix N,
            if 2 * P < N ∧ X < N - P ∧
                (N - P) / (p :: fifth.selectedAfter).prod ∈
                  largeFifthRosserIndices N cap w X fifth.selectedAfter ∧
                ((N - P) / (p :: fifth.selectedAfter).prod) *
                  (p :: fifth.selectedAfter).prod = N - P
            then actualSmallRosserPlus N cap w L
              ((N - P) / (p :: fifth.selectedAfter).prod)
            else 0))).sum := by
  have hjoined :
      fifth.selectedAfter.reverse ++ fifth.remainingAfter <+
        roughPrimeUniverse N cap w z := by
    simpa [P4AOriginalFull87OrderedSixthSuffix.eventSelected,
      P4AOriginalFull87ActualSixthSuffix.eventSixthSuffix] using
      (actual_event_joined_history_original_rough
        delta n e q om N cap w z L X
        (P4AOriginalFull87EighthPrimeMeanLedger.receiverTest N)
        state hstate (.fifthExclusive fifth) hfifth)
  unfold commonLargeSixthKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  have hrough : ∀ r ∈ p :: fifth.selectedAfter,
      r ∈ roughPrimeUniverse N cap w z := by
    intro r hr
    rcases List.mem_cons.mp hr with heq | hpre
    · subst r
      exact hjoined.subset (List.mem_append.mpr (Or.inr hp))
    · have hrev : r ∈ fifth.selectedAfter.reverse := by
        simpa using hpre
      exact hjoined.subset (List.mem_append.mpr (Or.inl hrev))
  rw [original_upper_half_unmasked_prime_prefix
    N cap w z L X fifth.selectedAfter p hrough]

end
end ImbalancedChen.P4AOriginalFull87StoppedUpperHalfCoprimeUnmask
