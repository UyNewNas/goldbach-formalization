import ImbalancedChen.P4AActualSixthFrozenEighthAdmission
import ImbalancedChen.P4AOriginalFull87LicensedSixthPolicy
import ImbalancedChen.P4AOriginalFull87WholeSixthCeiling
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The genuine rank-eight frontier of the ORIGINAL new sixth/eighth policy
has a strict physical rough-PREFIX product bound. The frontier is literally
the same as the new sixth frontier; its selected sixth ancestor is used by
the existing seventh-step admission proof. We then apply the separate
all-history 299/500 ceiling, including inherited fifth and third-inactive
sixth histories. We do not turn a scalar cap into a leaf-product inequality:
the strict product step comes from the existing real rank-eight admission.

This only bounds the selected rough PREFIX at rank eight, not the full
first-exit terminal rough product after subsequent selections. The
small-factor scaling lemma is stated separately with its explicit fixed
parameter cost. No PP input or reserve is paid here.
-/

namespace ImbalancedChen.P4AOriginalFull87RankEightPrefixLevel
noncomputable section
open scoped Classical

/-- Exactly the original new-sixth/eighth policy, not an auxiliary
coverage policy. The selected prefix is the true retained rank-eight
frontier produced by firstExitDepthFrontier, with original multiplicity
and genuine prime universe. No assumption of a realized source row. -/
theorem actual_rankEight_prefix_product_lt_fixed_power
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    (s.selectedPrefix.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  have hSix : s ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.sixthPolicy
        n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only
      [P4AOriginalFull87LicensedSixthPolicy.frontier_eq_new_sixth] using hs
  have hActual : s ∈ firstExitDepthFrontier 8
      (P4AActualSixthFrozenEighthAdmission.sixthPolicy
        (P4AOriginalFull87FiniteParentPolicy.fifthPolicy
          n e q om (N : ℝ))
        (fun history => (N : ℝ) ^
          P4AOriginalFull87LicensedSixthPolicy.level6Exponent
            n e q om (N : ℝ) history))
      weight [] true 1 (roughPrimeUniverse N cap w z) := by
    simpa only [P4AActualSixthFrozenEighthAdmission.sixthPolicy,
      P4AOriginalFull87LicensedSixthPolicy.sixthPolicy] using hSix
  have hAdmissible :=
    P4AActualSixthFrozenEighthAdmission.actual_rank_eight_admissible
      (P4AOriginalFull87FiniteParentPolicy.fifthPolicy
        n e q om (N : ℝ))
      (fun history => (N : ℝ) ^
        P4AOriginalFull87LicensedSixthPolicy.level6Exponent
          n e q om (N : ℝ) history)
      N cap w z weight s hActual
  have hSixLevel :=
    P4AOriginalFull87WholeSixthCeiling.level6_power_le_initial_ceiling
      n e q om (N : ℝ) he hN.le
      (rosserAncestor 6 s.selectedPrefix)
  exact hAdmissible.1.trans_le hSixLevel

/-- The exact additional parameter cost of attaching an actual
small Rosser factor to the rank-eight PREFIX (not a terminal leaf).
The scale hypothesis depends on fixed N,L,theta only, never on s or
on a proof-carrying source field. A genuine final q-bound requires the
separate continuation/terminal argument and a fixed-before-N buffer. -/
theorem actual_rankEight_attached_prefix_lt_of_fixed_scale
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (a : ℕ) (L theta : ℝ)
    (ha : (a : ℝ) < L)
    (hscale : L * (N : ℝ) ^ (299 / 500 : ℝ) ≤
      (N : ℝ) ^ theta) :
    ((a * s.selectedPrefix.prod : ℕ) : ℝ) <
      (N : ℝ) ^ theta := by
  have hprefix := actual_rankEight_prefix_product_lt_fixed_power
    delta n e q om N cap w z weight he hN s hs
  have hLpos : (0 : ℝ) < L :=
    lt_of_le_of_lt (Nat.cast_nonneg a) ha
  calc
    ((a * s.selectedPrefix.prod : ℕ) : ℝ) =
        (a : ℝ) * (s.selectedPrefix.prod : ℝ) := by push_cast; ring
    _ ≤ L * (s.selectedPrefix.prod : ℝ) :=
        mul_le_mul_of_nonneg_right ha.le (Nat.cast_nonneg _)
    _ < L * (N : ℝ) ^ (299 / 500 : ℝ) :=
        mul_lt_mul_of_pos_left hprefix hLpos
    _ ≤ (N : ℝ) ^ theta := hscale

end
end ImbalancedChen.P4AOriginalFull87RankEightPrefixLevel
