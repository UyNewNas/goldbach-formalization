import ImbalancedChen.ActualPrimeFineWordMultiplicity

/-!
# Original fine-word multiplicity on the same computed whole-box slots

The original sorted squarefree selector and its literal M_J are identified
with the existing exact three-group normalization on the same computed
endpoint slot lists. The original scalar becomes (c/M_J) K1 K2 K3 exactly
once. The full Mobius factor remains mu(r*a*b*d), including collisions
between groups and the fixed outside factor r.

These are whole Cartesian boxes on fixed original slot lists. They are
not decision fibres of the tuplewise selected-pair algorithm. Distribution
and arithmetic mean estimates remain separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- Integer endpoints stay below the original real fine-box endpoint. -/
def actualPrimeFineLabelIntegerUpper (N : ℕ) (τ : ℝ) (j : ℕ) : ℕ :=
  Nat.floor ((N : ℝ) ^ (τ * ((j : ℝ) + 1)))

theorem actualPrimeFineLabelFinset_le_integerUpper {N j q : ℕ} {τ : ℝ}
    (hq : q ∈ actualPrimeFineLabelFinset N τ j) :
    q ≤ actualPrimeFineLabelIntegerUpper N τ j :=
  Nat.le_floor (mem_actualPrimeFineLabelFinset.mp hq).2.2.2.le

theorem actualPrimeFineLabelIntegerUpper_le_power (N j : ℕ) (τ : ℝ) :
    (actualPrimeFineLabelIntegerUpper N τ j : ℝ) ≤
      (N : ℝ) ^ (τ * ((j : ℝ) + 1)) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The coefficient bound is on every integer, including repeated-prime
products, not only on the squarefree original selector. -/
theorem actualPrimeFineWord_normalized_abs_le_one (N : ℕ) (τ : ℝ)
    (input : List ℕ) (n : ℕ) :
    |actualNormalizedPrimeTupleCoefficient
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input) input.length n| ≤ 1 := by
  exact actualPrimeSlotBox_normalized_abs_le_one _ input
    (fun _ _ q hq => (mem_actualPrimeFineLabelFinset.mp hq).1) n

/-- The original sorted selector is regrouped on the exact same fixed
endpoint slots, with all original and group factorials restored once. -/
theorem actualPrimeFineWord_sameSlots_original_scalar {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (D A : ℝ) (yz : Bool)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (horder : (p 0 :: p 1 :: p 2 :: tail).Pairwise (· ≥ ·))
    (r : ℕ) (c : ℝ) (H : ℕ → ℝ) :
    let input := p 0 :: p 1 :: p 2 :: tail
    let upper := actualPrimeFineLabelIntegerUpper N τ
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    let T₁ := actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) slots.1
    let T₂ := actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) slots.2.1
    let T₃ := actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) slots.2.2
    c * (∑ n ∈ ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input).filter
        List.SortedGT).image List.prod,
        (ArithmeticFunction.moebius (r * n) : ℝ) * H n) =
      ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod, ∑ d ∈ T₃.image List.prod,
        ((c / (actualPrimeFineWordMultiplicity input : ℝ)) *
          (slots.1.length.factorial : ℝ) * (slots.2.1.length.factorial : ℝ) *
          (slots.2.2.length.factorial : ℝ)) *
          actualNormalizedPrimeTupleCoefficient T₁ slots.1.length a *
          actualNormalizedPrimeTupleCoefficient T₂ slots.2.1.length b *
          actualNormalizedPrimeTupleCoefficient T₃ slots.2.2.length d *
          ((ArithmeticFunction.moebius (r * (a * b * d)) : ℝ) * H (a * b * d)) := by
  dsimp only
  calc
    _ = (c / (actualPrimeFineWordMultiplicity (p 0 :: p 1 :: p 2 :: tail) : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (p 0 :: p 1 :: p 2 :: tail),
          (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) :=
      (actualPrimeFineWord_original_scalar hN hτ _ horder r c H).symm
    _ = ∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (p 0 :: p 1 :: p 2 :: tail),
        (c / (actualPrimeFineWordMultiplicity (p 0 :: p 1 :: p 2 :: tail) : ℝ)) *
          ((ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) :=
      Finset.mul_sum _ _ _
    _ = _ := actualFrozenSelectedPair_signed_regroup D A yz
      (actualPrimeFineLabelIntegerUpper N τ) p tail
      (actualPrimeFineLabelFinset N τ)
      (c / (actualPrimeFineWordMultiplicity (p 0 :: p 1 :: p 2 :: tail) : ℝ))
      (fun n => (ArithmeticFunction.moebius (r * n) : ℝ) * H n)

/-- On those same slot lists the actual product supports obey the
computed factor endpoints; the fine-interval bound is proved internally. -/
theorem actualPrimeFineWord_sameSlots_group_support (N : ℕ) (τ : ℝ)
    (D A : ℝ) (yz : Bool) (p : Fin 3 → ℕ) (tail : List ℕ) :
    let upper := actualPrimeFineLabelIntegerUpper N τ
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    let abc := actualFrozenSelectedPairFactors D A yz upper upper p tail
    (∀ a ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) slots.1).image List.prod,
      a ≤ abc.1) ∧
      (∀ b ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) slots.2.1).image List.prod,
        b ≤ abc.2.1) ∧
      (∀ d ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) slots.2.2).image List.prod,
        d ≤ abc.2.2) := by
  exact actualFrozenSelectedPair_group_support D A yz
    (actualPrimeFineLabelIntegerUpper N τ) p tail (actualPrimeFineLabelFinset N τ)
    (fun _ _ _ hq => actualPrimeFineLabelFinset_le_integerUpper hq)

end

end ImbalancedChen
