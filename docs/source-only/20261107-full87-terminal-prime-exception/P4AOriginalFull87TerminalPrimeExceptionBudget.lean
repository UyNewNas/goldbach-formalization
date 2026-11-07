import ImbalancedChen.P4AOriginalFull87EighthPrimeMeanLedger
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4 actual ORIGINAL full-modulus terminal: reduce the two elementary
prime-exception invoices to an explicit, N-independent modulus-prime
window and one actual centre-divisor cardinality. The signed full-beta
physical weights, both sixth/eighth policies and every occurrence are
unchanged. The primitive discrepancy is NOT absorbed or asserted small.

The modulus-zero case is handled using the totalized totient/division,
not by silently assuming all physical moduli positive. This packet is
a finite coefficient bound, NOT a same-rho asymptotic estimate or a
compiler/density reserve debit.
-/

namespace ImbalancedChen.P4AOriginalFull87TerminalPrimeExceptionBudget
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87EighthPrimeMeanLedger

/-- Every prime divisor of positive d lies in this finite, explicit
modulus-only universe; the bound does not depend on the centre N. -/
def primeDivisorWindow (d : ℕ) : Finset ℕ :=
  (Finset.range (d + 1)).filter (fun p => Nat.Prime p ∧ p ∣ d)

/-- A finite exact upper invoice for the modulus-prime term at full d.
At d=0 both sides of its comparison below are zero, by totalized
totient division. -/
def modulusPrimeCap (d : ℕ) : ℝ :=
  ((primeDivisorWindow d).card : ℝ) / (Nat.totient d : ℝ)

theorem modulusPrimeCap_nonneg (d : ℕ) : 0 ≤ modulusPrimeCap d := by
  unfold modulusPrimeCap
  positivity

/-- The actual inclusive prime prefix is a SUBSET of the distinct
positive prime divisors of the entire physical modulus d.  The proof
does not identify d with its rough part, nor assume d squarefree. -/
theorem actual_modulus_prime_count_le_window
    (N d : ℕ) (hd : 0 < d) :
    chenPrimeDivisorCount N d ≤ (primeDivisorWindow d).card := by
  classical
  have hs :
      (chenPrimePrefix N).filter (fun p => p ∣ d) ⊆
        primeDivisorWindow d := by
    intro p hp
    obtain ⟨hprefix, hdiv⟩ := Finset.mem_filter.mp hp
    have hprime : Nat.Prime p := (mem_chenPrimePrefix.mp hprefix).2
    have hpd : p ≤ d := Nat.le_of_dvd hd hdiv
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpd), ⟨hprime, hdiv⟩⟩
  unfold chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hs

/-- The physical modulus-prime term is bounded by the prime-divisor
count of d divided by the genuine full-modulus totient, including
the zero/one boundaries.  This is not a PNT/Mertens assertion. -/
theorem modulusPrimeTerm_le_cap (N d : ℕ) :
    modulusPrimeTerm N d ≤ modulusPrimeCap d := by
  by_cases hd : d = 0
  · subst d
    simp [modulusPrimeTerm, modulusPrimeCap]
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hc := actual_modulus_prime_count_le_window N d hdpos
    have hmul := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ (Nat.totient d : ℝ)⁻¹ by positivity)
    simpa only [modulusPrimeTerm, modulusPrimeCap, div_eq_mul_inv] using hmul

/-- Each exceptional centre prime is literally a prime divisor of N.
This inequality retains the centre correction; it does NOT erase it
on geometric or coprimality grounds. -/
theorem centrePrimeAPCount_le_centreDivisors (N d : ℕ) :
    chenCentrePrimeAPCount N N d ≤ chenPrimeDivisorCount N N := by
  classical
  have hs :
      (chenPrimePrefix N).filter (fun p => Nat.ModEq d p N ∧ p ∣ N) ⊆
        (chenPrimePrefix N).filter (fun p => p ∣ N) := by
    intro p hp
    obtain ⟨hprefix, ⟨_hcong, hdiv⟩⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hprefix, hdiv⟩
  unfold chenCentrePrimeAPCount chenPrimeDivisorCount
  exact_mod_cast Finset.card_le_card hs

/-- Absolute coefficient sums are monotone under pointwise ABSOLUTE
control on the original entire physical modulus population. -/
private theorem absolutePhysical_mono
    (P : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (G H : ℕ → ℝ)
    (h : ∀ d ∈ actualSmallRoughModuli (P false) N cap w z,
      |G d| ≤ |H d|) :
    absolutePhysical P N cap w z L G ≤
      absolutePhysical P N cap w z L H := by
  unfold absolutePhysical
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (h d hd)
    (abs_nonneg (actualSmallRoughRho (P false) N cap w z L d))

/-- The modulus exception is a concrete full-rho weighted moment of
prime divisors of the actual full modulus. In particular no separate
signed beta family has been manufactured for the error term. -/
theorem absolutePhysical_modulus_le
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) :
    absolutePhysical P N cap w z L (modulusPrimeTerm N) ≤
      absolutePhysical P N cap w z L modulusPrimeCap := by
  apply absolutePhysical_mono
  intro d _hd
  have h := modulusPrimeTerm_le_cap N d
  rw [abs_of_nonneg (modulusPrimeTerm_nonneg N d),
    abs_of_nonneg (modulusPrimeCap_nonneg d)]
  exact h

/-- The centre exception is controlled by the ACTUAL finite number of
centre prime divisors times the SAME physical absolute coefficient mass.
The centre primes may be nonzero in genuine arithmetic progressions. -/
theorem absolutePhysical_centre_le
    (P : Bool → List ℕ → Bool) (N cap : ℕ)
    (w z L : ℝ) :
    absolutePhysical P N cap w z L (chenCentrePrimeAPCount N N) ≤
      chenPrimeDivisorCount N N *
        absolutePhysical P N cap w z L (fun _ => 1) := by
  unfold absolutePhysical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _hd
  have hb : |chenCentrePrimeAPCount N N d| ≤
      chenPrimeDivisorCount N N := by
    rw [abs_of_nonneg (centrePrimeTerm_nonneg N d)]
    exact centrePrimeAPCount_le_centreDivisors N d
  calc
    |actualSmallRoughRho (P false) N cap w z L d| *
        |chenCentrePrimeAPCount N N d| ≤
      |actualSmallRoughRho (P false) N cap w z L d| *
        chenPrimeDivisorCount N N :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = chenPrimeDivisorCount N N *
          (|actualSmallRoughRho (P false) N cap w z L d| * |(1 : ℝ)|) := by
            simp [mul_comm]

/-- Both original policies use precisely the same full-modulus beta and
source terminal; these are TWO absolute comparison supports, not
two independently charged reserves. -/
theorem absoluteGainBudget_modulus_le
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    absoluteGainBudget delta n e q om N cap w z L (modulusPrimeTerm N) ≤
      absoluteGainBudget delta n e q om N cap w z L modulusPrimeCap := by
  unfold absoluteGainBudget
  exact add_le_add
    (absolutePhysical_modulus_le
      (sixthPolicy n e q om (N : ℝ)) N cap w z L)
    (absolutePhysical_modulus_le
      (policy delta n e q om (N : ℝ)) N cap w z L)

theorem absoluteGainBudget_centre_le
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    absoluteGainBudget delta n e q om N cap w z L
        (chenCentrePrimeAPCount N N) ≤
      chenPrimeDivisorCount N N *
        absoluteGainBudget delta n e q om N cap w z L (fun _ => 1) := by
  unfold absoluteGainBudget
  calc
    absolutePhysical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (chenCentrePrimeAPCount N N) +
      absolutePhysical (policy delta n e q om (N : ℝ)) N cap w z L
        (chenCentrePrimeAPCount N N) ≤
      chenPrimeDivisorCount N N *
        absolutePhysical (sixthPolicy n e q om (N : ℝ)) N cap w z L
          (fun _ => 1) +
      chenPrimeDivisorCount N N *
        absolutePhysical (policy delta n e q om (N : ℝ)) N cap w z L
          (fun _ => 1) := by
            exact add_le_add
              (absolutePhysical_centre_le _ N cap w z L)
              (absolutePhysical_centre_le _ N cap w z L)
    _ = _ := by ring

/-- Stronger, actual-source arithmetic error statement: the two
elementary prime exceptions now have explicit full-beta moments. ONLY
the genuine primitive AP discrepancy remains as an unevaluated error
function. No o(H_N), archive gain, or reserve charge is asserted. -/
theorem receiver_density_error_explicit_prime_exception_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) :
    |gain delta n e q om N cap w z L (receiverTest N) -
        primeMass N * gain delta n e q om N cap w z L densityTest| ≤
      absoluteGainBudget delta n e q om N cap w z L (primitiveError N) +
      absoluteGainBudget delta n e q om N cap w z L modulusPrimeCap +
      chenPrimeDivisorCount N N *
        absoluteGainBudget delta n e q om N cap w z L (fun _ => 1) := by
  have hbase := receiver_density_error_bound delta n e q om N cap w z L
  have hmod := absoluteGainBudget_modulus_le delta n e q om N cap w z L
  have hcen := absoluteGainBudget_centre_le delta n e q om N cap w z L
  linarith

end
end ImbalancedChen.P4AOriginalFull87TerminalPrimeExceptionBudget
