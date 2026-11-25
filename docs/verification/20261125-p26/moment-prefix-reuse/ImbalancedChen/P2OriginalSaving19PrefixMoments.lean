import ImbalancedChen.P2OriginalSaving19PrefixInterface
import Mathlib.Data.Rat.Cast.Order

/-! Exact finite representation of the original weighted homogeneous sum.
The existing prefix table is computed once for degrees zero through six.
Only a coefficient-interface hypothesis is used here; the Saving19 facade
specialization closes it with completeH's original defining equations. -/
namespace ImbalancedChen.P2OriginalSaving19PrefixMoments

open scoped BigOperators
open P2Winner9HomogeneousRecurrence
open P2OriginalSaving19PrefixInterface

def weightedNumerator (g z : Fin 9 → Nat) (k : Nat) : Nat :=
  let table := prefixCoefficients 6 9 z
  ∑ j : Fin (k + 1), table[k - j.val]?.getD 0 *
    ∑ i : Fin 9, g i * z i ^ j.val

def normalizedMoment (g z : Fin 9 → Nat) (d k : Nat) : ℚ :=
  (weightedNumerator g z k : ℚ) /
    (((∑ i : Fin 9, g i) * (9 + k).choose k * d ^ k : Nat) : ℚ)

/-- Full equality to the same weighted convolution, with one final rational
normalization. There is no witness premise, rounding or omitted term. -/
theorem normalizedMoment_eq_convolution
    (F : List ℚ → Nat → ℚ)
    (empty_rule : ∀ k, F [] k = if k = 0 then 1 else 0)
    (cons_rule : ∀ a xs k, F (a :: xs) k =
      ∑ j : Fin (k + 1), a ^ j.val * F xs (k - j.val))
    (g z : Fin 9 → Nat) (d k : Nat) (hk : k ≤ 6) :
    normalizedMoment g z d k =
      (∑ j : Fin (k + 1),
        F (List.ofFn (fun i => (z i : ℚ))) (k - j.val) *
          ∑ i : Fin 9, (g i : ℚ) * (z i : ℚ) ^ j.val) /
      ((∑ i : Fin 9, (g i : ℚ)) * ((9 + k).choose k : ℚ) * (d : ℚ) ^ k) := by
  unfold normalizedMoment weightedNumerator
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [prefixCoefficient_cast_eq F empty_rule cons_rule z (k - j.val)
    ((Nat.sub_le k j.val).trans hk)]

#print axioms normalizedMoment_eq_convolution

end ImbalancedChen.P2OriginalSaving19PrefixMoments
