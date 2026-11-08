import ImbalancedChen.P3ActualU8SmallNormLevel
import ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient
import ImbalancedChen.FirstExitGenericModuli
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The genuine first-exit integer coefficient is a *single signed Mobius
lookup on its retained support*. Two first-exit policies on the SAME
original rough prime carrier cannot contribute opposite nonzero signs
at a modulus. Their coefficient difference is confined to the symmetric
difference of the two retained-product supports, with cost ONE per
disagreeing modulus, not the generic two from arbitrary signed integers.

This is a literal finite combinatorial improvement for actual policy
coefficients. The comparison policy is not identified as the unbuilt
global causal compiler; small Rosser remains real-valued after attaching.
No support-symmetric-difference cardinality saving, analytic PP saving,
or external distribution hypothesis is assumed or proved.
-/

namespace ImbalancedChen.P3ActualU8FirstExitSupportDelta

noncomputable section
open scoped BigOperators
open Classical

/-- Exact first-exit Möbius lookup: disagreements between two actual
retained policies arise only when exactly one physical rough support
contains the modulus. Because both policies use the SAME Mobius sign
there, the total integer coefficient variation is at most the
CARDINALITY of the symmetric support difference inside the chosen
common rough carrier (rather than twice that cardinality). -/
theorem firstExit_rough_delta_le_support_mismatch
    (carrier : List ℕ) (rough : Finset ℕ)
    (policy₁ policy₀ : Bool → List ℕ → Bool) :
    let S₁ := firstExitRetainedModuli policy₁ carrier
    let S₀ := firstExitRetainedModuli policy₀ carrier
    let D := rough.filter (fun b =>
      (b ∈ S₁ ∧ b ∉ S₀) ∨ (b ∈ S₀ ∧ b ∉ S₁))
    (∑ b ∈ rough,
       |(firstExitRetainedCoefficient policy₁ carrier b : ℝ) -
        (firstExitRetainedCoefficient policy₀ carrier b : ℝ)|) ≤
      (D.card : ℝ) := by
  classical
  let S₁ := firstExitRetainedModuli policy₁ carrier
  let S₀ := firstExitRetainedModuli policy₀ carrier
  let D := rough.filter (fun b =>
    (b ∈ S₁ ∧ b ∉ S₀) ∨ (b ∈ S₀ ∧ b ∉ S₁))
  change (∑ b ∈ rough,
       |(firstExitRetainedCoefficient policy₁ carrier b : ℝ) -
        (firstExitRetainedCoefficient policy₀ carrier b : ℝ)|) ≤ (D.card : ℝ)
  have hsub : D ⊆ rough := Finset.filter_subset _ _
  have hzero : ∀ b ∈ rough, b ∉ D →
      |(firstExitRetainedCoefficient policy₁ carrier b : ℝ) -
       (firstExitRetainedCoefficient policy₀ carrier b : ℝ)| = 0 := by
    intro b hb hnot
    have hnotxor :
        ¬ ((b ∈ S₁ ∧ b ∉ S₀) ∨ (b ∈ S₀ ∧ b ∉ S₁)) := by
      intro hx
      exact hnot (Finset.mem_filter.mpr ⟨hb, hx⟩)
    by_cases h₁ : b ∈ S₁
    · have h₀ : b ∈ S₀ := by
        by_contra hn₀
        exact hnotxor (Or.inl ⟨h₁, hn₀⟩)
      simp [firstExitRetainedCoefficient, S₁, S₀, h₁, h₀]
    · have h₀ : b ∉ S₀ := by
        intro hh₀
        exact hnotxor (Or.inr ⟨hh₀, h₁⟩)
      simp [firstExitRetainedCoefficient, S₁, S₀, h₁, h₀]
  have hbound₁ (b : ℕ) :
      |(firstExitRetainedCoefficient policy₁ carrier b : ℝ)| ≤ 1 := by
    exact_mod_cast firstExitRetainedCoefficient_abs_le_one policy₁ carrier b
  have hbound₀ (b : ℕ) :
      |(firstExitRetainedCoefficient policy₀ carrier b : ℝ)| ≤ 1 := by
    exact_mod_cast firstExitRetainedCoefficient_abs_le_one policy₀ carrier b
  have hterm : ∀ b ∈ D,
      |(firstExitRetainedCoefficient policy₁ carrier b : ℝ) -
       (firstExitRetainedCoefficient policy₀ carrier b : ℝ)| ≤ 1 := by
    intro b hb
    rcases (Finset.mem_filter.mp hb).2 with ⟨h₁, h₀⟩ | ⟨h₀, h₁⟩
    · have hz₀ : firstExitRetainedCoefficient policy₀ carrier b = 0 := by
        simp [firstExitRetainedCoefficient, S₀, h₀]
      simpa [hz₀] using hbound₁ b
    · have hz₁ : firstExitRetainedCoefficient policy₁ carrier b = 0 := by
        simp [firstExitRetainedCoefficient, S₁, h₁]
      simpa [hz₁] using hbound₀ b
  calc
    (∑ b ∈ rough,
       |(firstExitRetainedCoefficient policy₁ carrier b : ℝ) -
        (firstExitRetainedCoefficient policy₀ carrier b : ℝ)|) =
      ∑ b ∈ D,
       |(firstExitRetainedCoefficient policy₁ carrier b : ℝ) -
        (firstExitRetainedCoefficient policy₀ carrier b : ℝ)| := by
          exact (Finset.sum_subset hsub hzero).symm
    _ ≤ ∑ _b ∈ D, (1 : ℝ) := by
      exact Finset.sum_le_sum hterm
    _ = (D.card : ℝ) := by simp

/-- Actual sharp-K labelled U8 rank-three signed PP, with exact
coprime mean, the literal fifth historical first-exit policy,
and another genuine first-exit rough policy attached through the
SAME original small Rosser signs on the SAME physical carrier.

Unlike the predecessor's generic |c|<=1 comparison, the real
integer first-exit coefficients have a common Möbius sign, so the
finite discrepancy is charged only once per *support* mismatch.
This bound does not establish that the global final policy is this
comparison policy or that the mismatch support is small. -/
theorem original_fifth_u8_firstExit_support_mismatch_PP
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (other : Bool → List ℕ → Bool) :
    let fifth := P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ)
    let carrier := roughPrimeUniverse N cap w z
    let Sother := firstExitRetainedModuli other carrier
    let Sfifth := firstExitRetainedModuli fifth carrier
    let D := rough.filter (fun b =>
      (b ∈ Sother ∧ b ∉ Sfifth) ∨ (b ∈ Sfifth ∧ b ∉ Sother))
    let small := actualSmallRosserSupport N cap w
    let Q := smallRoughModuli small rough
    let rhoOther := smallRoughRho small rough
      (fun b => (firstExitRetainedCoefficient other carrier b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let rhoFifth := smallRoughRho small rough
      (fun b => (firstExitRetainedCoefficient fifth carrier b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    |Part3.primeProductSignedError 3 N N Q rhoOther
        (P5U8SharpKSource.physicalWeight N) -
     Part3.primeProductSignedError 3 N N Q rhoFifth
        (P5U8SharpKSource.physicalWeight N)| ≤
      ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((Nat.ceil L : ℝ) * (D.card : ℝ)) := by
  dsimp
  have hfifth :
      fixedRoughCoefficient
        ((P1OriginalHistoricalPhysicalCoefficient.finalPolicy
          e chi m omega J4 cap4 J5 cap5 (N : ℝ)) false)
        N cap w z =
      (fun b => (firstExitRetainedCoefficient
        (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
          e chi m omega J4 cap4 J5 cap5 (N : ℝ))
        (roughPrimeUniverse N cap w z) b : ℝ)) := by
    funext b
    exact UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
      (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
        e chi m omega J4 cap4 J5 cap5 (N : ℝ))
      (P1OriginalHistoricalPhysicalCoefficient.finalPolicy_even
        e chi m omega J4 cap4 J5 cap5 (N : ℝ))
      N cap w z b
  have hphysical := P3ActualU8SmallNormLevel.actual_u8_PP_delta_le_ceil_level_rough
    ((P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ)) false)
    N cap w z L rough hrough
    (fun b => firstExitRetainedCoefficient other
      (roughPrimeUniverse N cap w z) b)
  dsimp at hphysical
  rw [hfifth] at hphysical
  have hmass := firstExit_rough_delta_le_support_mismatch
    (roughPrimeUniverse N cap w z) rough other
    (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
      e chi m omega J4 cap4 J5 cap5 (N : ℝ))
  dsimp at hmass
  calc
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((Nat.ceil L : ℝ) *
          (∑ b ∈ rough,
            |(firstExitRetainedCoefficient other
               (roughPrimeUniverse N cap w z) b : ℝ) -
             (firstExitRetainedCoefficient
               (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
                 e chi m omega J4 cap4 J5 cap5 (N : ℝ))
               (roughPrimeUniverse N cap w z) b : ℝ)|)) := hphysical
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
          ((Nat.ceil L : ℝ) *
            (((rough.filter (fun b =>
              (b ∈ firstExitRetainedModuli other (roughPrimeUniverse N cap w z) ∧
               b ∉ firstExitRetainedModuli
                 (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
                   e chi m omega J4 cap4 J5 cap5 (N : ℝ))
                 (roughPrimeUniverse N cap w z)) ∨
              (b ∈ firstExitRetainedModuli
                 (P1OriginalHistoricalPhysicalCoefficient.finalPolicy
                   e chi m omega J4 cap4 J5 cap5 (N : ℝ))
                 (roughPrimeUniverse N cap w z) ∧
               b ∉ firstExitRetainedModuli other
                 (roughPrimeUniverse N cap w z)))).card : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hmass (by positivity)
      · positivity

end
end ImbalancedChen.P3ActualU8FirstExitSupportDelta
