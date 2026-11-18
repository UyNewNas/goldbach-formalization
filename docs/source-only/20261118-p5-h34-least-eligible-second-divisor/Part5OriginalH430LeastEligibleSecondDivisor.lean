import ImbalancedChen.Part5OriginalH430ActualRetainedPrefixFibres

/-!
P5.6 / h34: the canonical rank-two arithmetic prefix is the LEAST
genuinely admitted prime divisor of the original tagged quotient q.

The previous retained-prefix packet used Nat.find only to obtain one
admitted divisor. Here we retain its minimality: any smaller prime
divisor of q cannot pass the ACTUAL second Rosser policy at this
tag/p-specific physical Q. This is an arithmetic first-eligible-divisor
sieve, not a Buchstab historical owner or a selected-count payment.

No claim is made that every smaller prime divisor is absent: it may
exist but fail the actual Rosser predicate. Neither q nor its chosen
second factor is identified with a new feedback-history mark.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430LeastEligibleSecondDivisor

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TaggedReceiverFibres
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430ActualRetainedPrefixFibres

/-- Exact original arithmetic and policy predicate used by Nat.find.
It includes actual prime-divisibility of the original q and the
original root-specific second ordinary Rosser test. -/
def eligibleSecond (N cap precision : ℕ) (tau z0 : ℝ)
    (lower : Bool) (z : TaggedReceiver) (ell : ℕ) : Prop :=
  ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
    retainedOriginalSecond N cap precision tau z0 lower z ell

/-- The canonical prefix has no STRICTLY SMALLER admissible second
prime divisor; this is stronger than mere existence of some divisor. -/
theorem least_key_witness_and_minimality
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    ∃ ell : ℕ,
      actualSecondPrefixKey N cap precision tau z0 lower z =
        some (arithmeticBand z, arithmeticPrime z, ell) ∧
      eligibleSecond N cap precision tau z0 lower z ell ∧
      ∀ m : ℕ, m < ell →
        ¬ eligibleSecond N cap precision tau z0 lower z m := by
  classical
  have hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z :=
    ((mem_stage_retained_original N cap precision tau z0 lower z).mp hz).2.2
  refine ⟨Nat.find hret, ?_, ?_, ?_⟩
  · simp [actualSecondPrefixKey, hret]
  · exact Nat.find_spec hret
  · intro m hm
    exact Nat.find_min hret hm

/-- An actual chosen second factor is at most ANY genuinely accepted
prime divisor of the SAME q under the SAME tag/p-specific Rosser test.
No arbitrary signed historical weight is used. -/
theorem chosen_second_le_any_eligible
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (chosen m : ℕ)
    (hkey : actualSecondPrefixKey N cap precision tau z0 lower z =
      some (arithmeticBand z, arithmeticPrime z, chosen))
    (hm : eligibleSecond N cap precision tau z0 lower z m) :
    chosen ≤ m := by
  classical
  have hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z :=
    ((mem_stage_retained_original N cap precision tau z0 lower z).mp hz).2.2
  have hchosen : Nat.find hret = chosen := by
    simpa [actualSecondPrefixKey, hret] using hkey
  simpa [hchosen] using (Nat.find_min' hret hm)

/-- Exact first-eligible-prime characterization: no fabricated owner
premise, and the backward direction uses the true least-witness lemma. -/
theorem canonical_key_iff_first_eligible_divisor
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (ell : ℕ) :
    actualSecondPrefixKey N cap precision tau z0 lower z =
      some (arithmeticBand z, arithmeticPrime z, ell) ↔
    eligibleSecond N cap precision tau z0 lower z ell ∧
      ∀ m : ℕ, m < ell →
        ¬ eligibleSecond N cap precision tau z0 lower z m := by
  classical
  have hret : hasRetainedOriginalSecond
      N cap precision tau z0 lower z :=
    ((mem_stage_retained_original N cap precision tau z0 lower z).mp hz).2.2
  have hkey :
      (actualSecondPrefixKey N cap precision tau z0 lower z =
        some (arithmeticBand z, arithmeticPrime z, ell)) ↔
      Nat.find hret = ell := by
    simp [actualSecondPrefixKey, hret]
  rw [hkey]
  constructor
  · intro heq
    subst ell
    exact ⟨Nat.find_spec hret, fun m hm => Nat.find_min hret hm⟩
  · intro ⟨hell, hmin⟩
    exact (Nat.find_eq_iff hret).2 ⟨hell, hmin⟩

/-- A literal retained (tag,p,q) is in its own canonical (tag,p,ell)
fibre precisely when ell passes the TRUE prime/Rosser tests and no
smaller actual accepted prime divides q. This is a q-sensitive sieve
description, not a bijection with the historical selected owner. -/
theorem mem_canonical_fibre_iff_first_eligible
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) :
    z ∈ actualRetainedPrefixFibre N cap precision tau z0 lower
        (some (arithmeticBand z, arithmeticPrime z, ell)) ↔
      z ∈ stageRetainedOriginal N cap precision tau z0 lower ∧
      eligibleSecond N cap precision tau z0 lower z ell ∧
      ∀ m : ℕ, m < ell →
        ¬ eligibleSecond N cap precision tau z0 lower z m := by
  classical
  simp only [actualRetainedPrefixFibre, Finset.mem_filter]
  constructor
  · rintro ⟨hz, hkey⟩
    exact ⟨hz, (canonical_key_iff_first_eligible_divisor
      N cap precision tau z0 lower z hz ell).mp hkey⟩
  · rintro ⟨hz, hfirst⟩
    exact ⟨hz, (canonical_key_iff_first_eligible_divisor
      N cap precision tau z0 lower z hz ell).mpr hfirst⟩

/-- The chosen prime simultaneously satisfies the original q-divisor
restriction, the ORIGINAL lower sieve window and the strict root-prime
ordering. Minimality refers ONLY to eligible second Rosser factors. -/
theorem least_key_original_window
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    ∃ ell : ℕ,
      actualSecondPrefixKey N cap precision tau z0 lower z =
        some (arithmeticBand z, arithmeticPrime z, ell) ∧
      ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
      (N : ℝ) ^ Part5OriginalUpsilon5CausalDictionary.a ≤ (ell : ℝ) ∧
      (ell : ℝ) < (arithmeticPrime z : ℝ) ∧
      ∀ m : ℕ, m < ell →
        ¬ eligibleSecond N cap precision tau z0 lower z m := by
  obtain ⟨ell, hkey, hel, hmin⟩ :=
    least_key_witness_and_minimality
      N cap precision tau z0 lower z hz
  have horig : z ∈ originalTagged N :=
    ((mem_stage_retained_original N cap precision tau z0 lower z).mp hz).1
  have hwin := retained_original_second_window_and_policy
    N cap precision tau z0 lower horig hel.1 hel.2.1 hel.2.2
  exact ⟨ell, hkey, hel.1, hel.2.1, hwin.1, hwin.2.1, hmin⟩

end
end ImbalancedChen.Part5OriginalH430LeastEligibleSecondDivisor
