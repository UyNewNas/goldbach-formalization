import ImbalancedChen.P4AOriginalFull87LiveSharpFactors
import ImbalancedChen.P4AOriginalFull87SignedSharpReceiver
import ImbalancedChen.FixedRoughCoefficients
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The ORIGINAL two live sixth/eighth coefficients are confined to a single
literal finite rough-prime universe. The displayed carrier is NOT assumed
to be live: first obtain the actual nonzero physical factor a*b using the
existing Rosser support theorem, then prove b divides the squarefree product
of the genuine roughPrimeUniverse. No artificially clipped PP coefficient,
changed parent, new sieve mask or invented rough level is introduced.

This is an exact, generally weak, finite support envelope. In particular
the product of all rough primes is NOT automatically N^theta (theta<1).
The frozen manuscript's physically admissible exponent and smooth PP
licence are still unsupplied; this file does not pay them.
-/

namespace ImbalancedChen.P4AOriginalFull87LiveRoughUniverse

noncomputable section
open scoped Classical BigOperators

open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87SignedSharpReceiver
  (full87PhysicalSupport full87PhysicalRhoChange sharpPrimeError
   full87_owned_signed_sharp_callsite)
open P4AOriginalFull87LiveSharpFactors
  (original_full87_rho_change_ne_zero_old_or_new)

/-- The exact finite prime alphabet of BOTH original policies, not a
newly enlarged PP cover or an assumed power-of-N modulus bound. -/
def actualRoughUniverseProduct (N cap : ℕ) (w z : ℝ) : ℕ :=
  (roughPrimeUniverse N cap w z).toFinset.prod id

private theorem actualRoughUniverseProduct_pos
    (N cap : ℕ) (w z : ℝ) :
    0 < actualRoughUniverseProduct N cap w z := by
  classical
  unfold actualRoughUniverseProduct
  apply Finset.prod_pos
  intro p hp
  exact (mem_roughPrimeUniverse_prime (List.mem_toFinset.mp hp)).pos

/-- Every ACTUAL retained rough modulus divides the one physical squarefree
alphabet product. The proof uses the existing first-exit factor support;
membership in a hypothetical enlarged rough cover would not suffice. -/
theorem actual_fixed_rough_dvd_universe_product
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) (b : ℕ)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    b ∣ actualRoughUniverseProduct N cap w z := by
  classical
  have hsub : b.primeFactors ⊆ (roughPrimeUniverse N cap w z).toFinset := by
    intro p hp
    exact List.mem_toFinset.mpr
      (fixedRoughSupport_primeFactors_mem retainOdd N cap w z hb hp)
  have hsquare := fixedRoughSupport_squarefree retainOdd N cap w z hb
  calc
    b = ∏ p ∈ b.primeFactors, p :=
      (Nat.prod_primeFactors_of_squarefree hsquare).symm
    _ ∣ actualRoughUniverseProduct N cap w z := by
      unfold actualRoughUniverseProduct
      exact prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) hsub

/-- The active small-factor inequality is STRICT. The rough-factor bound
is obtained from the actual retained support, not imposed as an input. -/
private theorem actual_live_physical_lt_universe
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (d : ℕ)
    (hd : actualSmallRoughRho retainOdd N cap w z L d ≠ 0) :
    (d : ℝ) <
      L * (actualRoughUniverseProduct N cap w z : ℝ) := by
  obtain ⟨a, _ha, b, hb, hdprod, haL, _hcoeff⟩ :=
    actualSmallRoughRho_ne_zero_factors retainOdd N cap w z L hd
  have hdiv : b ∣ actualRoughUniverseProduct N cap w z :=
    actual_fixed_rough_dvd_universe_product retainOdd N cap w z b hb
  have hUpos : 0 < actualRoughUniverseProduct N cap w z :=
    actualRoughUniverseProduct_pos N cap w z
  have hbU : (b : ℝ) ≤ (actualRoughUniverseProduct N cap w z : ℝ) := by
    exact_mod_cast (Nat.le_of_dvd hUpos hdiv)
  have hUposReal :
      (0 : ℝ) < (actualRoughUniverseProduct N cap w z : ℝ) := by
    exact_mod_cast hUpos
  rw [hdprod, Nat.cast_mul]
  calc
    (a : ℝ) * b ≤
        (a : ℝ) * (actualRoughUniverseProduct N cap w z : ℝ) :=
          mul_le_mul_of_nonneg_left hbU (Nat.cast_nonneg a)
    _ < L * (actualRoughUniverseProduct N cap w z : ℝ) :=
          mul_lt_mul_of_pos_right haL hUposReal

/-- Strict ACTUAL complete-modulus support bound for the original signed
sixth-minus-eighth physical coefficient. No sign, occurrence or beta
is discarded: nonzero means at least one side is genuinely live. -/
theorem original87_live_rho_change_lt_universe
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ)
    (hd : full87PhysicalRhoChange r n e q om N cap w z L d ≠ 0) :
    (d : ℝ) <
      L * (actualRoughUniverseProduct N cap w z : ℝ) := by
  rcases original_full87_rho_change_ne_zero_old_or_new
      r n e q om N cap w z L d hd with h6 | h8
  · exact actual_live_physical_lt_universe
      ((P4AOriginalFull87LicensedSixthPolicy.sixthPolicy
        n e q om (N : ℝ)) false) N cap w z L d h6
  · exact actual_live_physical_lt_universe
      ((P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ)) false) N cap w z L d h8

/-- If the exact complete modulus is above the physical finite envelope,
the ORIGINAL signed rho difference is zero, including on displayed but
zero-weight carrier entries. -/
theorem original87_rho_change_zero_above_universe
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (d : ℕ)
    (hd : L * (actualRoughUniverseProduct N cap w z : ℝ) ≤ (d : ℝ)) :
    full87PhysicalRhoChange r n e q om N cap w z L d = 0 := by
  by_contra h
  exact (not_lt_of_ge hd)
    (original87_live_rho_change_lt_universe r n e q om N cap w z L d h)

/-- Exact SAME-rho sharp-prime invoice, restricted to genuinely possible
complete moduli. No leaf-level absolute discrepancy sum replaces the
original full-q signed coefficient; the cutoff is applied only AFTER
combining matching physical moduli and their occurrence multiplicities. -/
theorem original87_owned_sharp_eq_universe_cut
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    (∑ c : P4AOriginalFull87SourceDictionary.Cell,
      P4AOriginalFull87OwnedEighthSource.ownedSource
        (width r) n e q om N cap w z L (sharpPrimeError N) c) =
      ∑ d ∈ (full87PhysicalSupport r n e q om N cap w z).filter
          (fun d => (d : ℝ) <
            L * (actualRoughUniverseProduct N cap w z : ℝ)),
        full87PhysicalRhoChange r n e q om N cap w z L d *
          sharpPrimeError N d := by
  classical
  rw [full87_owned_signed_sharp_callsite]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hcut : (d : ℝ) <
      L * (actualRoughUniverseProduct N cap w z : ℝ)
  · simp [hcut]
  · have hzero := original87_rho_change_zero_above_universe
        r n e q om N cap w z L d (le_of_not_gt hcut)
    simp [hcut, hzero]

end
end ImbalancedChen.P4AOriginalFull87LiveRoughUniverse
