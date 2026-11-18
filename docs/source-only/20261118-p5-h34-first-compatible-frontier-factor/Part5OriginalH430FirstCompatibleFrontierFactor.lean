import ImbalancedChen.Part5OriginalH430LeastEligibleSecondDivisor
import ImbalancedChen.Part5OriginalH430RankTwoFrontierConverse

/-!
P5.6 / h34: match the canonical original U3/U4 q-divisor to the
LITERAL rank-two ordinary Rosser frontier at the SAME physical Q.

The first-eligible arithmetic divisor is the least q-divisor among
those which have a real frontier state with ordered prefix [ell,p].
Every smaller genuine prime divisor of q is therefore absent from
that physical frontier (even though it can divide q). The actual
frontier sign and mass are preserved.

This is a precise FRONTIER compatibility theorem, NOT a theorem
identifying the first-excluded history owner, a q-to-history
injection, root norm7/2 capacity, or a count/Theta payment.
SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430FirstCompatibleFrontierFactor

noncomputable section
open scoped Classical BigOperators
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430PhysicalSelectedRootQFibres
open Part5OriginalH430ActualSecondRosserRetention
open Part5OriginalH430ActualRankTwoFrontierSupport
open Part5OriginalH430RankTwoFrontierConverse
open Part5OriginalH430ActualRetainedPrefixFibres
open Part5OriginalH430LeastEligibleSecondDivisor

/-- A genuine prime divisor of the ORIGINAL quotient q whose
ordered rank-two prefix [ell,p] actually occurs in the recursive
ordinary-Rosser frontier at this tag/p-specific Q. A frontier
state alone does NOT imply ell divides q, so the conjunction is
essential. -/
def frontierEligibleSecond
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) : Prop :=
  ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
    ∃ d : FirstExitDepthState ℕ,
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z]

/-- The arithmetic Rosser-retention test, with q divisibility
retained, is equivalent to the REAL rank-two frontier witness.
This reuses the previously derived forward and reverse recursion
theorems, rather than assuming a historical matching licence. -/
theorem frontier_eligible_iff_actual_second
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver) (ell : ℕ) :
    frontierEligibleSecond N cap precision tau z0 lower z ell ↔
      eligibleSecond N cap precision tau z0 lower z ell := by
  constructor
  · rintro ⟨hp, hdiv, d, hd, hprefix⟩
    exact ⟨hp, hdiv,
      (retained_original_second_iff_actual_rank_two
        N cap precision tau z0 lower z ell).2 ⟨d, hd, hprefix⟩⟩
  · rintro ⟨hp, hdiv, hret⟩
    obtain ⟨d, hd, hprefix⟩ :=
      (retained_original_second_iff_actual_rank_two
        N cap precision tau z0 lower z ell).1 hret
    exact ⟨hp, hdiv, d, hd, hprefix⟩

/-- The canonical arithmetic (tag,p,ell) key is exactly the
LEAST prime divisor of this particular q possessing a TRUE
rank-two historical frontier state. The minimum is among
q-compatible frontier factors, not every historical prime and
not the first forbidden (first-exit) factor. -/
theorem canonical_key_iff_first_compatible_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (ell : ℕ) :
    actualSecondPrefixKey N cap precision tau z0 lower z =
        some (arithmeticBand z, arithmeticPrime z, ell) ↔
      frontierEligibleSecond N cap precision tau z0 lower z ell ∧
      ∀ m : ℕ, m < ell →
        ¬ frontierEligibleSecond N cap precision tau z0 lower z m := by
  simpa only [frontier_eligible_iff_actual_second] using
    (canonical_key_iff_first_eligible_divisor
      N cap precision tau z0 lower z hz ell)

/-- Real earlier PRIME factors of the literal quotient. They
are not discarded from the original receiver or divided out
as if the q itself were a prime. -/
def smallerOriginalPrimeFactors (z : TaggedReceiver) (ell : ℕ) :
    Finset ℕ := by
  classical
  exact (Finset.range ell).filter
    (fun m => m.Prime ∧ m ∣ arithmeticQuotientPrime z)

/-- Every genuine smaller q prime factor is denied by the
actual second Rosser policy, not by an invented absence-of-
divisors premise. This is the exact first-compatible mismatch
lane that would have to be reconciled with a first-exit owner. -/
theorem smaller_q_factor_not_retained
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (ell : ℕ)
    (hkey : actualSecondPrefixKey N cap precision tau z0 lower z =
      some (arithmeticBand z, arithmeticPrime z, ell))
    {m : ℕ} (hm : m ∈ smallerOriginalPrimeFactors z ell) :
    ¬ retainedOriginalSecond N cap precision tau z0 lower z m := by
  have hfirst :=
    (canonical_key_iff_first_eligible_divisor
      N cap precision tau z0 lower z hz ell).mp hkey
  have hsmall : m < ell :=
    Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  have hprime : m.Prime ∧ m ∣ arithmeticQuotientPrime z :=
    (Finset.mem_filter.mp hm).2
  intro hret
  exact (hfirst.2 m hsmall) ⟨hprime.1, hprime.2, hret⟩

/-- Thus no smaller TRUE q-prime factor can occur as the
actual [m,p] second-rank frontier prefix at this physical Q.
This is stronger than a statement about Nat.find alone, but
does not exclude other (non-q-dividing) history prefixes. -/
theorem smaller_q_factor_not_in_actual_frontier
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (ell : ℕ)
    (hkey : actualSecondPrefixKey N cap precision tau z0 lower z =
      some (arithmeticBand z, arithmeticPrime z, ell))
    {m : ℕ} (hm : m ∈ smallerOriginalPrimeFactors z ell) :
    ¬ ∃ d : FirstExitDepthState ℕ,
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [m, arithmeticPrime z] := by
  rintro ⟨d, hd, hprefix⟩
  exact (smaller_q_factor_not_retained
    N cap precision tau z0 lower z hz ell hkey hm)
      ((retained_original_second_iff_actual_rank_two
        N cap precision tau z0 lower z m).2 ⟨d, hd, hprefix⟩)

/-- Exact canonical compatible frontier witness with original
prime-divisibility, TRUE alternating rank-two sign and mass,
and absence of all earlier q-dividing FRONTIER factors. -/
theorem canonical_key_actual_frontier_and_earlier_blockers
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower) :
    ∃ ell : ℕ, ∃ d : FirstExitDepthState ℕ,
      actualSecondPrefixKey N cap precision tau z0 lower z =
        some (arithmeticBand z, arithmeticPrime z, ell) ∧
      ell.Prime ∧ ell ∣ arithmeticQuotientPrime z ∧
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z] ∧
      d.positive = true ∧
      d.mass = historicalFirstRootMass (arithmeticPrime z) *
        (1 / ((ell : ℝ) - 1)) ∧
      ∀ m : ℕ, m < ell →
        m.Prime → m ∣ arithmeticQuotientPrime z →
        ¬ ∃ e : FirstExitDepthState ℕ,
          e ∈ firstExitDepthFrontier 2
            (ordinaryRosserRetainedPolicy lower
              (originalPhysicalQ N precision tau z))
            (fun r : ℕ => 1 / ((r : ℝ) - 1))
            [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
          e.selectedPrefix = [m, arithmeticPrime z] := by
  obtain ⟨ell, hkey, hel, hmin⟩ :=
    least_key_witness_and_minimality
      N cap precision tau z0 lower z hz
  obtain ⟨d, hd, hprefix, hsign, hmass⟩ :=
    retained_original_second_in_actual_rank_two_frontier
      N cap precision tau z0 lower z ell hel.2.2
  refine ⟨ell, d, hkey, hel.1, hel.2.1, hd,
    hprefix, hsign, hmass, ?_⟩
  intro m hm hp hdiv
  rintro ⟨e, he, heprefix⟩
  exact (hmin m hm) ⟨hp, hdiv,
    (retained_original_second_iff_actual_rank_two
      N cap precision tau z0 lower z m).2 ⟨e, he, heprefix⟩⟩

/-- Even for the canonical q-compatible factor, there is at
most one frontier STATE VALUE with this ordered prefix and Q.
This does not imply unique LIST POSITIONS or at most one q
receipt per tag/p/ell, hence no count-capacity payment. -/
theorem canonical_key_unique_actual_frontier_state
    (N cap precision : ℕ) (tau z0 : ℝ) (lower : Bool)
    (z : TaggedReceiver)
    (hz : z ∈ stageRetainedOriginal N cap precision tau z0 lower)
    (ell : ℕ)
    (hkey : actualSecondPrefixKey N cap precision tau z0 lower z =
      some (arithmeticBand z, arithmeticPrime z, ell)) :
    ∃! d : FirstExitDepthState ℕ,
      d ∈ firstExitDepthFrontier 2
        (ordinaryRosserRetainedPolicy lower
          (originalPhysicalQ N precision tau z))
        (fun r : ℕ => 1 / ((r : ℝ) - 1))
        [] true 1 (roughPrimeUniverse N cap 0 z0) ∧
      d.selectedPrefix = [ell, arithmeticPrime z] := by
  have hel :=
    ((canonical_key_iff_first_eligible_divisor
      N cap precision tau z0 lower z hz ell).mp hkey).1
  exact retained_original_second_unique_frontier_state
    N cap precision tau z0 lower z ell hel.2.2

end
end ImbalancedChen.Part5OriginalH430FirstCompatibleFrontierFactor
