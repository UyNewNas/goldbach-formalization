import ImbalancedChen.P4ACoveringCapInvariance

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual small-prime target transport. A marked prefix coprime to the actual
small product does not change which primes are deleted on replacing N by
B*N. The SAME real level and cutoff are retained; equality concerns both
complete coefficient functions, including zero and off-support values.
-/

namespace ImbalancedChen.P5Z.OriginalCommonBetaTargetTransport

noncomputable section
open P4ACoveringCapInvariance

/-- A prefix containing no new allowed small prime leaves the actual
prime carrier unchanged. Primes already dividing N require no restriction. -/
theorem actual_small_prime_carrier_target_mul {N B cap : ℕ} {w : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N cap w)) :
    actualSmallPrimeFinset (B * N) cap w = actualSmallPrimeFinset N cap w := by
  ext p
  constructor
  · intro hp
    obtain ⟨hpCap, hpPrime, hpBN, hpw⟩ := mem_actualSmallPrimeFinset.mp hp
    exact mem_actualSmallPrimeFinset.mpr ⟨hpCap, hpPrime,
      fun hpN => hpBN (dvd_mul_of_dvd_right hpN B), hpw⟩
  · intro hp
    have h := mem_actualSmallPrimeFinset.mp hp
    have hpM : p ∣ actualSmallPrimeProduct N cap w := by
      have hpf : p ∈ (actualSmallPrimeProduct N cap w).primeFactors := by
        rw [actualSmallPrimeProduct_primeFactors]
        exact hp
      exact (Nat.mem_primeFactors.mp hpf).2.1
    have hpB : ¬ p ∣ B := h.2.1.coprime_iff_not_dvd.mp (hB.symm.of_dvd_left hpM)
    refine mem_actualSmallPrimeFinset.mpr ⟨h.1, h.2.1, ?_, h.2.2.2⟩
    intro hpBN
    exact (h.2.1.dvd_mul.mp hpBN).elim hpB h.2.2.1

/-- Exact equality of the actual finite products, without a density premise. -/
theorem actual_small_product_target_mul {N B cap : ℕ} {w : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N cap w)) :
    actualSmallPrimeProduct (B * N) cap w = actualSmallPrimeProduct N cap w := by
  unfold actualSmallPrimeProduct
  rw [actual_small_prime_carrier_target_mul hB]

/-- Both original signs transport as functions at ONE unchanged level L. -/
theorem actual_small_pair_target_mul {N B cap : ℕ} {w : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N cap w)) (L : ℝ) :
    actualSmallRosserPlus (B * N) cap w L = actualSmallRosserPlus N cap w L ∧
      actualSmallRosserMinus (B * N) cap w L = actualSmallRosserMinus N cap w L := by
  have hprod := actual_small_product_target_mul hB
  constructor
  · unfold actualSmallRosserPlus
    rw [hprod]
  · unfold actualSmallRosserMinus
    rw [hprod]

/-- A canonical common beta pair survives both changes of target and
covering row enumeration. Its physical level L is NEVER rescaled by B. -/
theorem actual_small_pair_target_mul_cover {N B commonCap rowCap : ℕ} {w : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N commonCap w))
    (hcommon : w ≤ (commonCap : ℝ)) (hrow : w ≤ (rowCap : ℝ)) (L : ℝ) :
    actualSmallRosserPlus (B * N) rowCap w L = actualSmallRosserPlus N commonCap w L ∧
      actualSmallRosserMinus (B * N) rowCap w L = actualSmallRosserMinus N commonCap w L := by
  have hpair := actual_small_pair_target_mul hB L
  exact ⟨(actualSmallRosserPlus_eq_of_cover L hrow hcommon).trans hpair.1,
    (actualSmallRosserMinus_eq_of_cover L hrow hcommon).trans hpair.2⟩

/-- The existing sign-sensitive choice is preserved for every real rough
coefficient c. This is equality of the SAME chosen functions, not merely
an absolute bound or a substituted choice of beta sign. -/
theorem actual_signed_small_target_mul_cover {N B commonCap rowCap : ℕ} {w : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N commonCap w))
    (hcommon : w ≤ (commonCap : ℝ)) (hrow : w ≤ (rowCap : ℝ)) (L c : ℝ) :
    (if 0 ≤ c then actualSmallRosserPlus (B * N) rowCap w L
      else actualSmallRosserMinus (B * N) rowCap w L) =
    (if 0 ≤ c then actualSmallRosserPlus N commonCap w L
      else actualSmallRosserMinus N commonCap w L) := by
  have hpair := actual_small_pair_target_mul_cover hB hcommon hrow L
  rw [hpair.1, hpair.2]

end
end ImbalancedChen.P5Z.OriginalCommonBetaTargetTransport
