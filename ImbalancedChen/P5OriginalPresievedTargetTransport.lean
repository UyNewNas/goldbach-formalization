import ImbalancedChen.P5OriginalCommonBetaTargetTransport

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Target transport for the ENTIRE genuine presieved coefficient. The same
ordered rough universe, retainOdd policy, strict prime cutoff z, small
cutoff w, and real beta level L occur on both sides. Nothing is recomputed
at marked target B*N. This is not an equality with the old native sigma.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedTargetTransport

noncomputable section
open OriginalCommonBetaTargetTransport
open P4ACoveringCapInvariance

/-- The smaller actual prime product divides the larger one literally. -/
theorem small_product_dvd_of_cutoff_le {N cap : ℕ} {w z : ℝ} (hwz : w ≤ z) :
    actualSmallPrimeProduct N cap w ∣ actualSmallPrimeProduct N cap z := by
  unfold actualSmallPrimeProduct
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have h := mem_actualSmallPrimeFinset.mp hp
  exact mem_actualSmallPrimeFinset.mpr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.trans_le hwz⟩

/-- The rough interval is the actual prime carrier below z, filtered at w. -/
theorem rough_prime_carrier_eq_small_filter (N cap : ℕ) (w z : ℝ) :
    roughPrimeFinset N cap w z =
      (actualSmallPrimeFinset N cap z).filter (fun p => w ≤ (p : ℝ)) := by
  ext p
  simp only [mem_roughPrimeFinset, Finset.mem_filter, mem_actualSmallPrimeFinset]
  tauto

/-- Marking deletes no rough prime; the decreasing LIST is unchanged,
not just an unordered carrier or a collection of cardinalities. -/
theorem rough_universe_target_mul {N B cap : ℕ} {w z : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N cap z)) :
    roughPrimeUniverse (B * N) cap w z = roughPrimeUniverse N cap w z := by
  unfold roughPrimeUniverse
  rw [rough_prime_carrier_eq_small_filter,
    actual_small_prime_carrier_target_mul hB,
    ← rough_prime_carrier_eq_small_filter]

/-- A fixed causal policy therefore has the same retained carrier and
same coefficient function under the marked target. -/
theorem fixed_rough_pair_target_mul (retainOdd : List ℕ → Bool)
    {N B cap : ℕ} {w z : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N cap z)) :
    fixedRoughSupport retainOdd (B * N) cap w z = fixedRoughSupport retainOdd N cap w z ∧
      fixedRoughCoefficient retainOdd (B * N) cap w z = fixedRoughCoefficient retainOdd N cap w z := by
  constructor
  · unfold fixedRoughSupport
    rw [rough_universe_target_mul hB]
  · funext d
    unfold fixedRoughCoefficient
    rw [rough_universe_target_mul hB]

/-- Actual displayed physical modulus support is unchanged as well. -/
theorem presieved_moduli_target_mul (retainOdd : List ℕ → Bool)
    {N B cap : ℕ} {w z : ℝ} (hwz : w ≤ z)
    (hB : B.Coprime (actualSmallPrimeProduct N cap z)) :
    actualSmallRoughModuli retainOdd (B * N) cap w z =
      actualSmallRoughModuli retainOdd N cap w z := by
  have hsmall := hB.of_dvd_right (small_product_dvd_of_cutoff_le hwz)
  unfold actualSmallRoughModuli actualSmallRosserSupport
  rw [actual_small_product_target_mul hsmall, (fixed_rough_pair_target_mul retainOdd hB).1]

/-- The complete sign-sensitive small/rough coefficient is EXACTLY the
same function. This includes all inactive factors, zero, and all test
arguments. Policy, z, w and L are frozen physical data. -/
theorem presieved_rho_target_mul (retainOdd : List ℕ → Bool)
    {N B cap : ℕ} {w z : ℝ} (L : ℝ) (hwz : w ≤ z)
    (hB : B.Coprime (actualSmallPrimeProduct N cap z)) :
    actualSmallRoughRho retainOdd (B * N) cap w z L =
      actualSmallRoughRho retainOdd N cap w z L := by
  have hsmall := hB.of_dvd_right (small_product_dvd_of_cutoff_le hwz)
  have hpair := actual_small_pair_target_mul hsmall L
  have hrough := fixed_rough_pair_target_mul retainOdd hB
  unfold actualSmallRoughRho actualSmallRosserSupport
  rw [actual_small_product_target_mul hsmall, hrough.1, hrough.2, hpair.2, hpair.1]

/-- Arbitrary covering row enumerations give the same ordered universe. -/
theorem rough_universe_target_mul_cover {N B commonCap rowCap : ℕ} {w z : ℝ}
    (hB : B.Coprime (actualSmallPrimeProduct N commonCap z))
    (hcommon : z ≤ (commonCap : ℝ)) (hrow : z ≤ (rowCap : ℝ)) :
    roughPrimeUniverse (B * N) rowCap w z = roughPrimeUniverse N commonCap w z :=
  (roughPrimeUniverse_eq_of_cover hrow hcommon).trans (rough_universe_target_mul hB)

/-- Full engineering target match with all real cutoffs, physical levels
and the causal policy fixed, and arbitrary covering enumerations. -/
theorem presieved_target_mul_cover (retainOdd : List ℕ → Bool)
    {N B commonCap rowCap : ℕ} {w z : ℝ} (L : ℝ) (hwz : w ≤ z)
    (hB : B.Coprime (actualSmallPrimeProduct N commonCap z))
    (hcommon : z ≤ (commonCap : ℝ)) (hrow : z ≤ (rowCap : ℝ)) :
    actualSmallRoughModuli retainOdd (B * N) rowCap w z =
      actualSmallRoughModuli retainOdd N commonCap w z ∧
    actualSmallRoughRho retainOdd (B * N) rowCap w z L =
      actualSmallRoughRho retainOdd N commonCap w z L := by
  exact ⟨(actualSmallRoughModuli_eq_of_cover retainOdd hwz hrow hcommon).trans
      (presieved_moduli_target_mul retainOdd hwz hB),
    (actualSmallRoughRho_eq_of_cover retainOdd L hwz hrow hcommon).trans
      (presieved_rho_target_mul retainOdd L hwz hB)⟩

end
end ImbalancedChen.P5Z.OriginalPresievedTargetTransport
