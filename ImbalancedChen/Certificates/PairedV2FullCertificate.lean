import ImbalancedChen.Certificates.PairedV2StripCertificates
import ImbalancedChen.Certificates.PairedV2NaturalSums

/-!
The full adopted-mask integral uses the actual row checker and the exact
natural-number endpoint sums.  The table, row selector, logarithm enclosures
and coefficient are inherited unchanged.  This assembly still requires
the split strip-check modules to pass their independent verification gates.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Exhaustive checks of the original certificate on every adopted row. -/
theorem all_certificates_checked : ∀ r : Row,
    (makeCertificate r (approximation r)).check = true := by
  rintro ⟨i, j⟩
  exact strip_certificates_checked i j

/-- Casting the proved natural numerator sum at the original common scale. -/
theorem lower_sum :
    (∑ r : Row, (makeCertificate r (approximation r)).lower : ℚ) =
      55858378943374979 / 100000000000000000000 := by
  simp only [makeCertificate]
  rw [← Finset.sum_div, ← Nat.cast_sum, NaturalSums.lower_numerator_sum]
  norm_num

/-- Casting the proved natural numerator sum at the original common scale. -/
theorem upper_sum :
    (∑ r : Row, (makeCertificate r (approximation r)).upper : ℚ) =
      55858409959907296 / 100000000000000000000 := by
  simp only [makeCertificate]
  rw [← Finset.sum_div, ← Nat.cast_sum, NaturalSums.upper_numerator_sum]
  norm_num

/-- Directed bounds on the sum of the actual fourfold integrals, each
already carrying the original `K / 80` coefficient exactly once. -/
theorem integral_bounds :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤ integral ∧
      integral ≤ (55858409959907296 / 100000000000000000000 : ℝ) := by
  have hb := full_integral_bounds_of_checked approximation all_certificates_checked
  rw [lower_sum, upper_sum] at hb
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hb
  exact hb

/-- The frozen manuscript's rounded-down adopted extra-gross coefficient. -/
theorem adopted_extra_gross_lower : (558583 / 1000000000 : ℝ) ≤ integral := by
  exact le_trans (by norm_num) integral_bounds.1

end ImbalancedChen.Certificates.PairedV2.FullMask
