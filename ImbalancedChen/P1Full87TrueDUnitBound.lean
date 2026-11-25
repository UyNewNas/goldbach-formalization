import ImbalancedChen.P1Full87TrueDPolicyDelta
import ImbalancedChen.SignSensitiveAttachment
import Mathlib.Tactic

/-!
P1.4 SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A genuine pointwise strengthening of the previous bound
|rho_LICENSED - rho_RAW| <= 2.  For one fixed rough modulus b,
each causal first-exit policy contributes the SAME Mobius(b)
or zero. Both policies use the SAME small Rosser coefficients.
Consequently the sign-sensitive attachment difference has
absolute value <= 1 at each unique small/rough physical modulus.

The new bound is independent of whether a branch is tagged,
changed, BOTH, inherited, or filtered. It does not grant the
manuscript's whole signed-PP admissible coefficient class:
causal factorization, common smoothing, and uniformity remain
separate checks. It also does not assert a positive majorant for
the difference or any asymptotic H_N error budget.
-/

namespace ImbalancedChen.P1Full87TrueDUnitBound

noncomputable section
open Classical
open scoped BigOperators
open P1Full87TrueDPolicyDelta (trueDDeltaRho)

/-- Every actual rough coefficient is literally the same Mobius value,
masked by its own retained support. There is no policy-dependent sign
at a fixed rough modulus. -/
private theorem fixed_coeff_is_masked_mobius
    (retainOdd : List ℕ → Bool) (N cap d : ℕ) (w z : ℝ) :
    fixedRoughCoefficient retainOdd N cap w z d =
      if d ∈ fixedRoughSupport retainOdd N cap w z then
        (ArithmeticFunction.moebius d : ℝ)
      else 0 := by
  classical
  simp [fixedRoughCoefficient, fixedRoughSupport,
    oddFirstExitRetainedCoefficient]

/-- The cutoff-separated product is injective. At each occupied q=a*b,
the two genuine coefficient masks select either the SAME signed attached
small beta, or zero. This costs one beta, never two. -/
private theorem masked_pair_difference_abs_le_one
    (small rough fresh old : Finset ℕ) (w : ℝ)
    (mu betaMinus betaPlus : ℕ → ℝ)
    (hsmall : ∀ a ∈ small, SmallPrimeSupportedAt w a)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (hmu : ∀ b, |mu b| ≤ 1)
    (hminus : ∀ a, |betaMinus a| ≤ 1)
    (hplus : ∀ a, |betaPlus a| ≤ 1)
    (d : ℕ) :
    |smallRoughRho small rough
        (fun b => if b ∈ fresh then mu b else 0)
        betaMinus betaPlus d -
      smallRoughRho small rough
        (fun b => if b ∈ old then mu b else 0)
        betaMinus betaPlus d| ≤ 1 := by
  classical
  by_cases hd : d ∈ smallRoughModuli small rough
  · rcases Finset.mem_image.mp hd with ⟨⟨a, b⟩, hab, hprod⟩
    change (a, b) ∈ small ×ˢ rough at hab
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    rw [← hprod]
    rw [smallRoughRho_mul hsmall hrough _ _ _ ha hb,
      smallRoughRho_mul hsmall hrough _ _ _ ha hb]
    change |signAttachedCoefficient
        (if b ∈ fresh then mu b else 0) (betaMinus a) (betaPlus a) -
      signAttachedCoefficient
        (if b ∈ old then mu b else 0) (betaMinus a) (betaPlus a)| ≤ 1
    have hbound := abs_signAttachedCoefficient_le_one
      (hmu b) (hminus a) (hplus a)
    by_cases hf : b ∈ fresh
    · by_cases ho : b ∈ old
      · simp [hf, ho]
      · simpa [hf, ho, signAttachedCoefficient] using hbound
    · by_cases ho : b ∈ old
      · simpa [hf, ho, signAttachedCoefficient, abs_neg] using hbound
      · simp [hf, ho, signAttachedCoefficient]
  · have hzeroFresh :
        smallRoughRho small rough
          (fun b => if b ∈ fresh then mu b else 0)
          betaMinus betaPlus d = 0 :=
      smallRoughRho_eq_zero_of_not_mem small rough _ _ _ hd
    have hzeroOld :
        smallRoughRho small rough
          (fun b => if b ∈ old then mu b else 0)
          betaMinus betaPlus d = 0 :=
      smallRoughRho_eq_zero_of_not_mem small rough _ _ _ hd
    rw [hzeroFresh, hzeroOld]
    norm_num

/-- Real small/rough coefficients share the same small Rosser support
and beta functions. Their rough carriers are combined only as a covering
support, with unchanged coefficients and no added branch mask. -/
theorem actual_policy_rho_difference_abs_le_one
    (old fresh : List ℕ → Bool) (N cap d : ℕ)
    (w z L : ℝ) :
    |actualSmallRoughRho fresh N cap w z L d -
      actualSmallRoughRho old N cap w z L d| ≤ 1 := by
  classical
  let small := actualSmallRosserSupport N cap w
  let rough := fixedRoughSupport fresh N cap w z ∪
    fixedRoughSupport old N cap w z
  have hs : ∀ a ∈ small, SmallPrimeSupportedAt w a := by
    intro a ha
    exact actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha
  have hr : ∀ b ∈ rough, RoughPrimeSupportedAt w b := by
    intro b hb
    rcases Finset.mem_union.mp hb with hf | ho
    · exact fixedRoughSupport_roughPrimeSupportedAt fresh N cap w z hf
    · exact fixedRoughSupport_roughPrimeSupportedAt old N cap w z ho
  have hnewCover : fixedRoughSupport fresh N cap w z ⊆ rough := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inl hb)
  have holdCover : fixedRoughSupport old N cap w z ⊆ rough := by
    intro b hb
    exact Finset.mem_union.mpr (Or.inr hb)
  have hnewRho :
      smallRoughRho small rough (fixedRoughCoefficient fresh N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) =
      actualSmallRoughRho fresh N cap w z L :=
    actualSmallRoughRho_eq_on_common_carrier
      fresh N cap w z L rough hnewCover
  have holdRho :
      smallRoughRho small rough (fixedRoughCoefficient old N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) =
      actualSmallRoughRho old N cap w z L :=
    actualSmallRoughRho_eq_on_common_carrier
      old N cap w z L rough holdCover
  have hnewMask :
      fixedRoughCoefficient fresh N cap w z =
        (fun b => if b ∈ fixedRoughSupport fresh N cap w z then
          (ArithmeticFunction.moebius b : ℝ) else 0) := by
    funext b
    exact fixed_coeff_is_masked_mobius fresh N cap b w z
  have holdMask :
      fixedRoughCoefficient old N cap w z =
        (fun b => if b ∈ fixedRoughSupport old N cap w z then
          (ArithmeticFunction.moebius b : ℝ) else 0) := by
    funext b
    exact fixed_coeff_is_masked_mobius old N cap b w z
  have hmu : ∀ b, |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 := by
    intro b
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := b))
  have hminus : ∀ a, |actualSmallRosserMinus N cap w L a| ≤ 1 :=
    actualSmallRosserMinus_abs_le_one N cap w L
  have hplus : ∀ a, |actualSmallRosserPlus N cap w L a| ≤ 1 :=
    actualSmallRosserPlus_abs_le_one N cap w L
  rw [← hnewRho, ← holdRho, hnewMask, holdMask]
  exact masked_pair_difference_abs_le_one
    small rough
    (fixedRoughSupport fresh N cap w z)
    (fixedRoughSupport old N cap w z)
    w (fun b => (ArithmeticFunction.moebius b : ℝ))
    (actualSmallRosserMinus N cap w L)
    (actualSmallRosserPlus N cap w L)
    hs hr hmu hminus hplus d

/-- Repeating a coefficient at a modulus outside its actual support is
already zero. The zero-extension in the true-d policy difference does
not change the physical coefficient function. -/
private theorem actual_rho_zero_extension
    (retainOdd : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ) :
    (if d ∈ actualSmallRoughModuli retainOdd N cap w z then
       actualSmallRoughRho retainOdd N cap w z L d else 0) =
      actualSmallRoughRho retainOdd N cap w z L d := by
  classical
  by_cases hd : d ∈ actualSmallRoughModuli retainOdd N cap w z
  · simp [hd]
  · have hz : actualSmallRoughRho retainOdd N cap w z L d = 0 :=
      smallRoughRho_eq_zero_of_not_mem
        (actualSmallRosserSupport N cap w)
        (fixedRoughSupport retainOdd N cap w z)
        (fixedRoughCoefficient retainOdd N cap w z)
        (actualSmallRosserMinus N cap w L)
        (actualSmallRosserPlus N cap w L) hd
    simp [hd, hz]

/-- Stronger exact pointwise bound for the ACTUAL true-small-d policy
difference, in particular for RAW vs LICENSED full87 policies.
Unlike the old bound 2, this uses common Mobius signs and unique
small/rough factorization, not a comparison of two unrelated estimates.
It proves ONLY the size test, not full signed PP admissibility. -/
theorem trueDDeltaRho_abs_le_one
    (old fresh : List ℕ → Bool) (N cap d : ℕ) (w z L : ℝ) :
    |trueDDeltaRho old fresh N cap w z L d| ≤ (1 : ℝ) := by
  have h := actual_policy_rho_difference_abs_le_one
    old fresh N cap d w z L
  simpa only [trueDDeltaRho,
    actual_rho_zero_extension fresh N cap d w z L,
    actual_rho_zero_extension old N cap d w z L] using h

end
end ImbalancedChen.P1Full87TrueDUnitBound
