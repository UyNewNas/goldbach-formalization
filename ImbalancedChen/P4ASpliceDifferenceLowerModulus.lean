import ImbalancedChen.P4ASpliceDifferenceLocalization
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
SOURCEONLY / UNCOMPILED. Actual rough retained supports are squarefree,
and each of their prime factors is at least w. Their product is the
literal retained modulus. Through-k policy agreement therefore places
each changed modulus at least at w^(k+1), for w≥1. For the original compact
third update this is w^3. The literal compiler mass can be restricted to
that lower modulus range by an exact equality, without a mass bound.
-/

namespace ImbalancedChen.P4ASpliceDifferenceLowerModulus

noncomputable section
open scoped BigOperators symmDiff
open P4ARetainedSupportDifferenceMass P4ASpliceDifferenceLocalization

/-- Squarefreeness identifies the actual retained modulus with the product
of its distinct prime factors. Every factor carries the actual rough lower
bound, so no hypothetical modulus envelope is used. -/
theorem retained_pow_primeFactors_card_le
    (retainOdd : List ℕ → Bool) (N cap : ℕ) {w : ℝ} (hw : 0 ≤ w) (z : ℝ)
    {d : ℕ} (hd : d ∈ fixedRoughSupport retainOdd N cap w z) :
    w ^ d.primeFactors.card ≤ (d : ℝ) := by
  classical
  have hsf := fixedRoughSupport_squarefree retainOdd N cap w z hd
  have hrough := fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd
  calc
    w ^ d.primeFactors.card = ∏ _p ∈ d.primeFactors, w := (Finset.prod_const w).symm
    _ ≤ ∏ p ∈ d.primeFactors, (p : ℝ) := by
      apply Finset.prod_le_prod
      · intro p _hp
        exact hw
      · intro p hp
        exact hrough.2 p hp
    _ = ((∏ p ∈ d.primeFactors, p : ℕ) : ℝ) := by rw [Nat.cast_prod]
    _ = (d : ℝ) := by rw [Nat.prod_primeFactors_of_squarefree hsf]

/-- Common early policy decisions force each changed retained modulus
above the rough lower cutoff raised to its first possible changed rank. -/
theorem changed_modulus_ge_pow_succ (k : ℕ)
    (retainOdd₁ retainOdd₂ : List ℕ → Bool)
    (hagree : ∀ history, history.length ≤ k → retainOdd₁ history = retainOdd₂ history)
    (N cap : ℕ) {w : ℝ} (hw : 1 ≤ w) (z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport retainOdd₁ N cap w z ∆
      fixedRoughSupport retainOdd₂ N cap w z) :
    w ^ (k + 1) ≤ (d : ℝ) := by
  have hcard : k + 1 ≤ d.primeFactors.card :=
    Nat.succ_le_of_lt (changed_support_has_more_primeFactors k retainOdd₁ retainOdd₂
      hagree N cap w z hd)
  have hpow : w ^ d.primeFactors.card ≤ (d : ℝ) := by
    rcases Finset.mem_symmDiff.mp hd with ⟨hd₁, _⟩ | ⟨hd₂, _⟩
    · exact retained_pow_primeFactors_card_le retainOdd₁ N cap (zero_le_one.trans hw) z hd₁
    · exact retained_pow_primeFactors_card_le retainOdd₂ N cap (zero_le_one.trans hw) z hd₂
  exact (pow_le_pow_right₀ hw hcard).trans hpow

/-- The original third upper update and its initial policy have no changed
modulus below w^3. Their shared first stop and all early tests are preserved. -/
theorem actualThird_changed_modulus_ge_cube
    (e h : ℝ) (m N cap : ℕ) {w : ℝ} (hw : 1 ≤ w) (z : ℝ) {d : ℕ}
    (hd : d ∈ fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
      fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z) :
    w ^ 3 ≤ (d : ℝ) := by
  exact changed_modulus_ge_pow_succ 2 _ _
    (fun history hlen => actualExtendedThirdCompactUpperPolicy_through_two
      e h m N false history hlen) N cap hw z hd

/-- Literal absolute compiler coefficient error vanishes below the cube
cutoff, including moduli outside both supports. -/
theorem actualThird_abs_coefficient_sub_eq_zero_below_cube
    (e h : ℝ) (m N cap : ℕ) {w : ℝ} (hw : 1 ≤ w) (z : ℝ)
    (d : ℕ) (hd : (d : ℝ) < w ^ 3) :
    |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
      fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d| = 0 := by
  have hnot : d ∉ fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
      fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z := by
    intro hmem
    exact (not_lt_of_ge (actualThird_changed_modulus_ge_cube e h m N cap hw z hmem)) hd
  rw [abs_coefficient_sub_eq_symmDiff_indicator, if_neg hnot]

/-- Exact restriction on any finite common carrier. In particular one can
take the actual union without an enlargement charge. No error mass is
estimated: the omitted coefficient errors are identically zero. -/
theorem actualThird_compilerMass_restrict_ge_cube
    (e h : ℝ) (m N cap : ℕ) {w : ℝ} (hw : 1 ≤ w) (z : ℝ)
    (rough : Finset ℕ) :
    reciprocalTotientDensity rough
      (fun d => |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
        fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d|) =
      reciprocalTotientDensity (rough.filter (fun d => w ^ 3 ≤ (d : ℝ)))
        (fun d => |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
          fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d|) := by
  classical
  unfold reciprocalTotientDensity
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hdnot
  have hsmall : (d : ℝ) < w ^ 3 := by
    apply lt_of_not_ge
    intro hlarge
    exact hdnot (Finset.mem_filter.mpr ⟨hd, hlarge⟩)
  rw [actualThird_abs_coefficient_sub_eq_zero_below_cube e h m N cap hw z d hsmall, zero_div]

/-- Common-union form of the exact original third compiler restriction. -/
theorem actualThird_union_compilerMass_restrict_ge_cube
    (e h : ℝ) (m N cap : ℕ) {w : ℝ} (hw : 1 ≤ w) (z : ℝ) :
    let rough := fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∪
      fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z
    reciprocalTotientDensity rough
      (fun d => |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
        fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d|) =
      reciprocalTotientDensity (rough.filter (fun d => w ^ 3 ≤ (d : ℝ)))
        (fun d => |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
          fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d|) := by
  exact actualThird_compilerMass_restrict_ge_cube e h m N cap hw z _

/-- The previously exact symmetric-difference unit charge also has this
proved lower-modulus restriction. Both its sign removal and its cutoff
are supplied by the actual policies. -/
theorem actualThird_union_compilerMass_eq_changed_ge_cube_unitMass
    (e h : ℝ) (m N cap : ℕ) {w : ℝ} (hw : 1 ≤ w) (z : ℝ) :
    reciprocalTotientDensity
      (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∪
        fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z)
      (fun d => |fixedRoughCoefficient (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z d -
        fixedRoughCoefficient (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z d|) =
      reciprocalTotientDensity
        ((fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
          fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z).filter
            (fun d => w ^ 3 ≤ (d : ℝ))) (fun _ => 1) := by
  classical
  have hfilter :
      (fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
        fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z).filter
          (fun d => w ^ 3 ≤ (d : ℝ)) =
      fixedRoughSupport (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z ∆
        fixedRoughSupport (actualExtendedThirdCompactInitialPolicy e m N false) N cap w z := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact actualThird_changed_modulus_ge_cube e h m N cap hw z hd
  rw [hfilter, compilerMass_union_eq_symmDiff_unitMass]

end
end ImbalancedChen.P4ASpliceDifferenceLowerModulus
