import ImbalancedChen.P2AdoptedRowsActualEnclosure
import ImbalancedChen.Certificates.P2SemanticGainSetIntegral

/-!
# P2.7: the full same-mask-v2 paired contribution

This entry point composes the existing complete row certificate, actual-grid
reindexing, support Fubini identities and actual Buchstab-gain comparison.
The strict bound is the 1106 manuscript's `current-extra-gross` statement.
It follows from the original exact lower endpoint; no new numerical witness
or integral lower-bound hypothesis is introduced.

The arithmetic injection into the retained parent belongs to its existing
counting obligations. The constant-gain certificate's upper endpoint is not
asserted to be an upper bound for the larger actual Buchstab gain.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedCertificateCompletion

noncomputable section

open scoped BigOperators

/-- The exact certified endpoint strictly exceeds the rounded manuscript value. -/
theorem endpoint_strict_margin :
    (558583 / 1000000000 : ℝ) <
      55858378943374979 / 100000000000000000000 := by
  norm_num

/-- All 17,572 original constant-gain integrals satisfy the strict manuscript bound. -/
theorem integral_strict_lower : (558583 / 1000000000 : ℝ) < integral :=
  lt_of_lt_of_le endpoint_strict_margin integral_bounds.1

/-- The same strict bound indexed by the actual adopted mesh coordinates. -/
theorem actual_grid_strict_lower :
    (558583 / 1000000000 : ℝ) <
      ∑ p ∈ P2AdoptedRows.grid, P2AdoptedRows.gridIntegral p := by
  rw [P2AdoptedRows.sum_gridIntegral]
  exact integral_strict_lower

/-- Product-volume integration over the actual support union gives the same bound. -/
theorem support_union_strict_lower :
    (558583 / 1000000000 : ℝ) < P2AdoptedUnion.unionIntegral := by
  rw [P2PairedSupportFubini.unionIntegral_eq_integral]
  exact integral_strict_lower

/-- The genuine pinned Buchstab extra gain dominates the certified constant gain. -/
theorem actual_buchstab_gain_strict_lower :
    (558583 / 1000000000 : ℝ) < P2SemanticGainSetIntegral.unionSemanticIntegral :=
  lt_of_lt_of_le support_union_strict_lower
    P2SemanticGainSetIntegral.unionSemanticIntegral_ge_constant

/-- The genuine Buchstab integral exceeds its half-baseline by the manuscript amount. -/
theorem actual_buchstab_difference_strict_lower :
    (558583 / 1000000000 : ℝ) <
      P2SemanticGainSetIntegral.unionBuchstabIntegral -
        P2SemanticGainSetIntegral.unionHalfBaselineIntegral := by
  rw [P2SemanticGainSetIntegral.unionBuchstabIntegral_sub_halfBaseline]
  exact actual_buchstab_gain_strict_lower

/-- The full P2.7 analytic certificate, with complete mesh size and exact endpoints. -/
theorem complete_analytic_certificate :
    P2AdoptedRows.grid.card = 17572 ∧
    (55858378943374979 / 100000000000000000000 : ℝ) ≤ integral ∧
    integral ≤ (55858409959907296 / 100000000000000000000 : ℝ) ∧
    (558583 / 1000000000 : ℝ) < integral ∧
    (558583 / 1000000000 : ℝ) < P2SemanticGainSetIntegral.unionSemanticIntegral :=
  ⟨P2AdoptedRows.grid_card, integral_bounds.1, integral_bounds.2,
    integral_strict_lower, actual_buchstab_gain_strict_lower⟩

end

end ImbalancedChen.Certificates.PairedV2.FullMask.P2PairedCertificateCompletion
