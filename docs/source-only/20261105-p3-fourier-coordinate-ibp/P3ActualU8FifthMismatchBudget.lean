import ImbalancedChen.P3ActualU8SmallNormLevel
import ImbalancedChen.P1OriginalHistoricalPhysicalCoefficient
import Mathlib.Tactic

/-!
P3.6 SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

A finite DISAGREEMENT-CARDINALITY bound for a genuinely integer-valued,
one-bounded rough coefficient compared to the literal original fifth-policy
integer coefficient. The small Rosser plus/minus attachment is kept on both
sides. This is not an identification of the final causal compiler and does
not assert that its disagreement set is small.

All complete physical moduli, the original U8 sharp-K labelled occurrences
(including the repeated terminal-prime wall), and the exact coprime mean
remain inside the actual signed prime-product discrepancy.
-/

namespace ImbalancedChen.P3ActualU8FifthMismatchBudget

noncomputable section
open scoped BigOperators
open Classical

/-- A one-bounded integer coefficient can differ from another such
coefficient by at most two at each *disagreeing* rough modulus. Equal
coefficients contribute exactly zero, rather than a full carrier cost.
No arithmetic estimate or target smallness is a premise. -/
theorem integer_rough_delta_le_disagreement_card
    (rough : Finset ℕ) (c₁ c₀ : ℕ → ℤ)
    (h₁ : ∀ b ∈ rough, |c₁ b| ≤ 1)
    (h₀ : ∀ b ∈ rough, |c₀ b| ≤ 1) :
    (∑ b ∈ rough, |(c₁ b : ℝ) - (c₀ b : ℝ)|) ≤
      2 * (((rough.filter (fun b => c₁ b ≠ c₀ b)).card : ℝ)) := by
  classical
  let D := rough.filter (fun b => c₁ b ≠ c₀ b)
  have hsub : D ⊆ rough := Finset.filter_subset _ _
  have hzero : ∀ b ∈ rough, b ∉ D →
      |(c₁ b : ℝ) - (c₀ b : ℝ)| = 0 := by
    intro b hb hnot
    have heq : c₁ b = c₀ b := by
      by_contra hn
      exact hnot (Finset.mem_filter.mpr ⟨hb, hn⟩)
    simp [heq]
  calc
    (∑ b ∈ rough, |(c₁ b : ℝ) - (c₀ b : ℝ)|) =
        ∑ b ∈ D, |(c₁ b : ℝ) - (c₀ b : ℝ)| := by
          exact (Finset.sum_subset hsub hzero).symm
    _ ≤ ∑ _b ∈ D, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro b hb
      have hbR : b ∈ rough := hsub hb
      have hb₁ : |(c₁ b : ℝ)| ≤ 1 := by
        exact_mod_cast h₁ b hbR
      have hb₀ : |(c₀ b : ℝ)| ≤ 1 := by
        exact_mod_cast h₀ b hbR
      calc
        |(c₁ b : ℝ) - (c₀ b : ℝ)| ≤
            |(c₁ b : ℝ)| + |(c₀ b : ℝ)| := abs_sub _ _
        _ ≤ (1 : ℝ) + 1 := add_le_add hb₁ hb₀
        _ = 2 := by norm_num
    _ = 2 * (D.card : ℝ) := by simp [mul_comm]

/-- The real physical coefficient of the literal ORIGINAL fifth-capped
historical policy is compared with any explicitly bounded integer rough
candidate on ONE common cutoff-separated rough carrier. The compiler
is NOT identified with the final full-domain causal coefficient.

This is a usable finite mismatch criterion, not an asserted count of bad
rough moduli. If the disagreement set is large, the resulting bound is
necessarily too weak to pay arbitrary logarithmic PP discrepancy. -/
theorem original_fifth_u8_disagreement_PP
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J4 : Finset (Fin 4 → Fin (m + 1)))
    (cap4 : (Fin 4 → Fin (m + 1)) → ℚ)
    (J5 : Finset (Fin 5 → Fin (m + 1)))
    (cap5 : (Fin 5 → Fin (m + 1)) → ℚ)
    (N cap : ℕ) (w z L : ℝ) (rough : Finset ℕ)
    (hrough : ∀ b ∈ rough, RoughPrimeSupportedAt w b)
    (compiled : ℕ → ℤ)
    (hcompiled : ∀ b ∈ rough, |compiled b| ≤ 1) :
    let c₀ := P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
      e chi m omega J4 cap4 J5 cap5 N cap w z
    let small := actualSmallRosserSupport N cap w
    let Q := smallRoughModuli small rough
    let rhoCompiled := smallRoughRho small rough
      (fun b => (compiled b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let rhoFifth := smallRoughRho small rough
      (fun b => (c₀ b : ℝ))
      (actualSmallRosserMinus N cap w L)
      (actualSmallRosserPlus N cap w L)
    let disagreements := rough.filter (fun b => compiled b ≠ c₀ b)
    |Part3.primeProductSignedError 3 N N Q rhoCompiled
        (P5U8SharpKSource.physicalWeight N) -
      Part3.primeProductSignedError 3 N N Q rhoFifth
        (P5U8SharpKSource.physicalWeight N)| ≤
      ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((Nat.ceil L : ℝ) * (2 * (disagreements.card : ℝ))) := by
  dsimp
  have hfifth :
      fixedRoughCoefficient
          ((P1OriginalHistoricalPhysicalCoefficient.finalPolicy
            e chi m omega J4 cap4 J5 cap5 (N : ℝ)) false)
          N cap w z =
        (fun b => (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
          e chi m omega J4 cap4 J5 cap5 N cap w z b : ℝ)) := by
    funext b
    exact (P1OriginalHistoricalPhysicalCoefficient.roughCoefficient_eq_fixed
      e chi m omega J4 cap4 J5 cap5 N cap w z b).symm
  have hphysical :=
    P3ActualU8SmallNormLevel.actual_u8_PP_delta_le_ceil_level_rough
      ((P1OriginalHistoricalPhysicalCoefficient.finalPolicy
        e chi m omega J4 cap4 J5 cap5 (N : ℝ)) false)
      N cap w z L rough hrough compiled
  dsimp at hphysical
  rw [hfifth] at hphysical
  have hmass := integer_rough_delta_le_disagreement_card rough
    compiled
    (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
      e chi m omega J4 cap4 J5 cap5 N cap w z)
    hcompiled
    (fun b _ => P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt_abs_le_one
      e chi m omega J4 cap4 J5 cap5 N cap w z b)
  calc
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((Nat.ceil L : ℝ) *
          (∑ b ∈ rough, |(compiled b : ℝ) -
            (P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
              e chi m omega J4 cap4 J5 cap5 N cap w z b : ℝ)|)) :=
      hphysical
    _ ≤ ((P5U8SharpKSource.arithmeticTriples N).card : ℝ) *
        ((Nat.ceil L : ℝ) * (2 *
          (((rough.filter (fun b => compiled b ≠
            P1OriginalHistoricalPhysicalCoefficient.roughCoefficientInt
              e chi m omega J4 cap4 J5 cap5 N cap w z b)).card : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hmass (by positivity)
      · positivity

end
end ImbalancedChen.P3ActualU8FifthMismatchBudget
