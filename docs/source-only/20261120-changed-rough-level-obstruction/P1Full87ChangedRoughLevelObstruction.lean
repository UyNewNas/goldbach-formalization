import ImbalancedChen.P1Full87ChangedRoughFiveFactors
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A new quantitative consequence of the ACTUAL changed-rough carrier:
when the literal lower rough-prime cutoff w is at least one, each changed
RAW/LICENSED rough modulus b satisfies w^5 <= b. This combines the prior
genuine common-tree first-disagreement factor count with the original
fixedRoughSupport squarefreeness and physical rough-prime threshold.

The consequence is a *conditional level obstruction*: for any B < w^5
the original rough symmetric difference has no modulus b <= B.
Crucially this is not an assertion that the full small/rough physical rho
has level B, nor an authentication of manuscript PP, and the actual
parameter w must be matched before invoking a manuscript power cutoff.
No new support mask, analytic input, or target-shaped hypothesis is used.
-/

namespace ImbalancedChen.P1Full87ChangedRoughLevelObstruction

noncomputable section
open Classical
open scoped BigOperators

/-- The original squarefree rough support has product at least w^5
whenever it contains five distinct prime factors. No rounding of the
strict/inclusive rough cutoff is performed. -/
private theorem fixed_rough_five_factor_power_bound
    (retainOdd : List ℕ → Bool) (N cap b : ℕ) (w z : ℝ)
    (hw : 1 ≤ w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z)
    (hfive : 5 ≤ b.primeFactors.card) :
    w ^ 5 ≤ (b : ℝ) := by
  classical
  have hsq : Squarefree b :=
    fixedRoughSupport_squarefree retainOdd N cap w z hb
  have hrough : RoughPrimeSupportedAt w b :=
    fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb
  have hprod :
      (∏ p ∈ b.primeFactors, (p : ℝ)) = (b : ℝ) := by
    exact_mod_cast (Nat.prod_primeFactors_of_squarefree hsq)
  have hnonneg : 0 ≤ w := le_trans zero_le_one hw
  calc
    w ^ 5 ≤ w ^ b.primeFactors.card := pow_le_pow_right₀ hw hfive
    _ = ∏ p ∈ b.primeFactors, w := by simp
    _ ≤ ∏ p ∈ b.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact hnonneg
      · intro p hp
        exact hrough.2 p hp
    _ = (b : ℝ) := hprod

/-- The actual RAW/LICENSED changed rough carrier is above the FIFTH
power of the same literal rough-prime lower endpoint. Neither one-sided
support is replaced or enlarged; it is the original common-tree change. -/
theorem actual_full87_changed_rough_wpow_five_le
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap b : ℕ) (w z : ℝ) (hw : 1 ≤ w) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    b ∈
      (fixedRoughSupport (S false) N cap w z \
       fixedRoughSupport (R false) N cap w z) ∪
      (fixedRoughSupport (R false) N cap w z \
       fixedRoughSupport (S false) N cap w z) →
    w ^ 5 ≤ (b : ℝ) := by
  dsimp only
  intro hb
  have hfive :=
    P1Full87ChangedRoughFiveFactors.actual_full87_changed_rough_ge_five_primeFactors
      delta n e q om N cap b w z hb
  rcases Finset.mem_union.mp hb with hS | hR
  · exact fixed_rough_five_factor_power_bound
      (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ) false)
      N cap b w z hw (Finset.mem_sdiff.mp hS).1 hfive
  · exact fixed_rough_five_factor_power_bound
      (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ) false)
      N cap b w z hw (Finset.mem_sdiff.mp hR).1 hfive

/-- Explicit failure of a low rough-modulus candidate when a proposed
level B is strictly below the fifth-power lower rough cutoff. The exact
strict inequality is retained; equality is NOT silently excluded. -/
theorem actual_full87_changed_rough_above_level
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap b B : ℕ) (w z : ℝ) (hw : 1 ≤ w)
    (hlevel : (B : ℝ) < w ^ 5) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    b ∈
      (fixedRoughSupport (S false) N cap w z \
       fixedRoughSupport (R false) N cap w z) ∪
      (fixedRoughSupport (R false) N cap w z \
       fixedRoughSupport (S false) N cap w z) →
    B < b := by
  dsimp only
  intro hb
  have hbound := actual_full87_changed_rough_wpow_five_le
    delta n e q om N cap b w z hw hb
  exact_mod_cast (lt_of_lt_of_le hlevel hbound)

/-- There is NO low rough-modulus source in either direction of the
actual changed support, provided the numeric level inequality is proved
for the SAME w. This is only a rough-carrier obstruction, not an
unjustified full-q smooth PP conclusion. -/
theorem actual_full87_changed_rough_low_carrier_empty
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap B : ℕ) (w z : ℝ) (hw : 1 ≤ w)
    (hlevel : (B : ℝ) < w ^ 5) :
    let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
    let S := P4AOriginalFull87LicensedSixthPolicy.policy
      delta n e q om (N : ℝ)
    (((fixedRoughSupport (S false) N cap w z \
        fixedRoughSupport (R false) N cap w z) ∪
       (fixedRoughSupport (R false) N cap w z \
        fixedRoughSupport (S false) N cap w z)).filter
         (fun b => b ≤ B)) = ∅ := by
  dsimp only
  ext b
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  rintro ⟨hchanged, hle⟩
  have hgt := actual_full87_changed_rough_above_level
    delta n e q om N cap b B w z hw hlevel hchanged
  exact (Nat.not_le_of_gt hgt) hle

end
end ImbalancedChen.P1Full87ChangedRoughLevelObstruction
