import ImbalancedChen.P3ActualU8RoughDeltaNorm
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
A strict-level bound for the L1 mass of the LITERAL small Rosser
minus/plus weights, and its consequence for the actual labelled U8
compiled-minus-raw signed PP. This does not control the rough compiler
difference or prove an arbitrary-log PP bound.

The active condition is (d : Real) < L, not <= L. Both signed weights
are bounded by one, and an inactive small slot contributes exactly zero.
There is no multiplication by the number of physical moduli.
-/

namespace ImbalancedChen.P3ActualU8SmallNormLevel

noncomputable section
open scoped BigOperators

/-- When the actual small Rosser slot is at or above its strict level,
BOTH literal weights are zero. This uses the provider's active-support
lemmas rather than assuming support truncation as an axiom. -/
theorem actual_small_beta_zero_of_level
    (N cap d : ℕ) (w L : ℝ) (hlevel : L ≤ (d : ℝ)) :
    actualSmallRosserMinus N cap w L d = 0 ∧
      actualSmallRosserPlus N cap w L d = 0 := by
  constructor
  · by_contra hn
    exact (not_lt_of_ge hlevel)
      (actualSmallRosserMinus_active hn).2.1
  · by_contra hn
    exact (not_lt_of_ge hlevel)
      (actualSmallRosserPlus_active hn).2.1

/-- The literal small Rosser sign-sensitive L1 factor is bounded by
the number of NATURAL indices strictly below the actual level L.
In particular it is at most ceil(L), uniformly in the enumeration cap,
target N, prime cutoff w and all rough retention policies. No asymptotic
smallness or subpolynomial bound follows from this inequality. -/
theorem actual_small_beta_norm_le_ceil
    (N cap : ℕ) (w L : ℝ) :
    (∑ a ∈ actualSmallRosserSupport N cap w,
      max |actualSmallRosserMinus N cap w L a|
        |actualSmallRosserPlus N cap w L a|) ≤
      (Nat.ceil L : ℝ) := by
  classical
  let S := actualSmallRosserSupport N cap w
  let A := S.filter (fun a => (a : ℝ) < L)
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have hAR : A ⊆ Finset.range (Nat.ceil L) := by
    intro a ha
    have hlt : (a : ℝ) < L := (Finset.mem_filter.mp ha).2
    exact Finset.mem_range.mpr (Nat.lt_ceil.mpr hlt)
  have hcard : A.card ≤ Nat.ceil L := by
    calc
      A.card ≤ (Finset.range (Nat.ceil L)).card :=
        Finset.card_le_card hAR
      _ = Nat.ceil L := by simp
  have hzero : ∀ a ∈ S, a ∉ A →
      max |actualSmallRosserMinus N cap w L a|
        |actualSmallRosserPlus N cap w L a| = 0 := by
    intro a ha haNot
    have hnot : ¬ (a : ℝ) < L := by
      intro haL
      exact haNot (Finset.mem_filter.mpr ⟨ha, haL⟩)
    obtain ⟨hm, hp⟩ := actual_small_beta_zero_of_level N cap a w L
      (le_of_not_gt hnot)
    simp [hm, hp]
  change (∑ a ∈ S,
      max |actualSmallRosserMinus N cap w L a|
        |actualSmallRosserPlus N cap w L a|) ≤ _
  calc
    _ = ∑ a ∈ A,
        max |actualSmallRosserMinus N cap w L a|
          |actualSmallRosserPlus N cap w L a| := by
        exact (Finset.sum_subset hAS hzero).symm
    _ ≤ ∑ _a ∈ A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact max_le
          (actualSmallRosserMinus_abs_le_one N cap w L a)
          (actualSmallRosserPlus_abs_le_one N cap w L a)
    _ = (A.card : ℝ) := by simp
    _ ≤ (Nat.ceil L : ℝ) := by exact_mod_cast hcard

/-- Apply the proved strict small-level mass to the actual original U8
rank-three PP coefficient perturbation. The complete physical moduli,
exact primitive mean, signed rho, and original U8 labels (including the
p2=q terminal repetition) remain unchanged.

The remaining RHS is the TRUE rough integer-compiler difference; it is
NOT assumed small. The natural ceil(L) loss may itself be polynomial
in N and is not an arbitrary-log discrepancy payment. -/
theorem actual_u8_PP_delta_le_ceil_level_rough
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (rough : Finset ℕ)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (compiled : ℕ → ℤ) :
    let small := actualSmallRosserSupport N cap w
    let Q := smallRoughModuli small rough
    let rhoComp := smallRoughRho small rough
      (fun b => (compiled b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let rhoRaw := smallRoughRho small rough
      (fixedRoughCoefficient retainOdd N cap w z)
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    |Part3.primeProductSignedError 3 N N Q rhoComp
        (P5U8SharpKSource.physicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rhoRaw
        (P5U8SharpKSource.physicalWeight N)| ≤
    ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
      ((Nat.ceil L : ℝ) *
        (∑ b ∈ rough, |(compiled b : ℝ) -
          fixedRoughCoefficient retainOdd N cap w z b|)) := by
  dsimp
  have hprev := P3ActualU8RoughDeltaNorm.actual_u8_compiled_PP_delta_le_rough_delta
    retainOdd N cap w z L rough hrough compiled
  dsimp at hprev
  calc
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((∑ a ∈ actualSmallRosserSupport N cap w,
          max |actualSmallRosserMinus N cap w L a|
            |actualSmallRosserPlus N cap w L a|) *
          (∑ b ∈ rough, |(compiled b : ℝ) -
            fixedRoughCoefficient retainOdd N cap w z b|)) := hprev
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((Nat.ceil L : ℝ) *
          (∑ b ∈ rough, |(compiled b : ℝ) -
            fixedRoughCoefficient retainOdd N cap w z b|)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right
          (actual_small_beta_norm_le_ceil N cap w L)
          (Finset.sum_nonneg (fun b hb => abs_nonneg _))
      · positivity

end
end ImbalancedChen.P3ActualU8SmallNormLevel
