import ImbalancedChen.RoughPrimeUniverse
import ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Endpoint-direction audit for the previous literal w = N^(19/96)
sixth-receiver-zero specialization.

The ACTUAL rough universe is [w,z), not [z, infinity).
The frozen rho0=19/96 is the UPPER sieve endpoint in the manuscript,
but the generic source also retains a separate LOWER presieve cutoff w.
Nothing in the prior receiver-zero proof identifies the actual w
with N^rho0. This packet demonstrates why substituting the upper z
for the lower w is mathematically invalid.

The finite example uses the genuine target-deleted chen receiver.
It is NOT a witness that the original fifth-exclusive producer or
PLUS-Rosser filter admits a particular event, and it does NOT
invalidate the earlier conditional theorem at literal w=N^rho0.
-/

namespace ImbalancedChen.P4AOriginalFull87UpperEndpointDirectionAudit

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87EighthPrimeMeanLedger (receiverTest)

private def sixWord : List ℕ := [3, 5, 7, 11, 13, 17]

/-- Six genuinely distinct rough primes, all above lower w=3 and
strictly below upper z=26, with the actual N-coprime requirement.
No model prime list is used in place of roughPrimeUniverse. -/
theorem six_word_mem_original_rough_universe :
    ∀ p ∈ sixWord,
      p ∈ roughPrimeUniverse (2 ^ 24) 100 (3 : ℝ) (26 : ℝ) := by
  intro p hp
  simp [sixWord] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num [mem_roughPrimeUniverse]

/-- Enlarging the actual upper endpoint retains this same six-word;
the lower cutoff is unchanged. -/
theorem six_word_mem_of_upper_at_least_26
    (z : ℝ) (hz : (26 : ℝ) ≤ z) :
    ∀ p ∈ sixWord,
      p ∈ roughPrimeUniverse (2 ^ 24) 100 (3 : ℝ) z := by
  intro p hp
  have h := six_word_mem_original_rough_universe p hp
  obtain ⟨hcap, hprime, hnot, hlow, hupp⟩ :=
    mem_roughPrimeUniverse.mp h
  exact mem_roughPrimeUniverse.mpr
    ⟨hcap, hprime, hnot, hlow, lt_of_lt_of_le hupp hz⟩

/-- The genuine six-prime product remains BELOW the even target.
Thus z as an upper cutoff does not imply the lower estimate
N < w^6 needed by the prior stopped-receiver-zero theorem. -/
theorem six_word_product_below_target :
    sixWord.prod = 255255 ∧ sixWord.prod < 2 ^ 24 := by
  constructor <;> norm_num [sixWord]

/-- The original target-deleted prime source REALLY has a receiver
divisible by this six-prime full modulus: P=16521961 is prime,
N=16777216 and N-P=255255. No hypothetical prime source is inserted. -/
theorem six_word_actual_receiver_positive :
    (0 : ℝ) < receiverTest (2 ^ 24) sixWord.prod := by
  have hprime : Nat.Prime 16521961 := by norm_num
  have hP : 16521961 ∈ chenAdditivePrimeCarrier (2 ^ 24) := by
    rw [chenAdditivePrimeCarrier_eq_prefix_filter]
    simp only [Finset.mem_filter, mem_chenPrimePrefix]
    exact ⟨⟨by norm_num, hprime⟩, by norm_num⟩
  have hreceiver : 255255 ∈ chenPrimeReceiverSource (2 ^ 24) := by
    unfold chenPrimeReceiverSource
    apply Finset.mem_image.mpr
    refine ⟨16521961, hP, ?_⟩
    norm_num
  have hfiltered : 255255 ∈
      (chenPrimeReceiverSource (2 ^ 24)).filter
        (fun n => 255255 ∣ n) := by
    exact Finset.mem_filter.mpr ⟨hreceiver, dvd_refl _⟩
  have hcard : 0 <
      ((chenPrimeReceiverSource (2 ^ 24)).filter
        (fun n => 255255 ∣ n)).card := by
    exact Finset.card_pos.mpr ⟨255255, hfiltered⟩
  rw [six_word_product_below_target.1]
  unfold receiverTest
  exact_mod_cast hcard

/-- A concrete finite obstruction to upgrading an upper-z statement
into the previous lower-w zero theorem: the very same actual rough
universe contains a six-prime word under z≥26, its product is ≤N,
and the original prime receiver test at that product is positive.
This does NOT assert membership in the original stopped event list. -/
theorem actual_upper_endpoint_not_a_six_lower_cutoff
    (z : ℝ) (hz : (26 : ℝ) ≤ z) :
    (∀ p ∈ sixWord,
        p ∈ roughPrimeUniverse (2 ^ 24) 100 (3 : ℝ) z) ∧
      sixWord.prod < 2 ^ 24 ∧
      (0 : ℝ) < receiverTest (2 ^ 24) sixWord.prod := by
  exact ⟨six_word_mem_of_upper_at_least_26 z hz,
    six_word_product_below_target.2,
    six_word_actual_receiver_positive⟩

end
end ImbalancedChen.P4AOriginalFull87UpperEndpointDirectionAudit
