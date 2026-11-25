import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The elementary rank step for a complete labelled list. Repeated values
remain repeated factors, and the empty list is allowed. This lemma has
no source-admission meaning by itself: its floor and product hypotheses
must be derived from the actual source in a separate caller.
-/
namespace ImbalancedChen.P2MarkedSourceRankCore

noncomputable section

/-- A common positive power floor and the complete product cap bound the
number of slots, including repetitions, independently of the scale. -/
theorem list_length_le_floor_inv {x a : ℝ} (hx : 1 < x) (ha : 0 < a)
    (xs : List ℕ) (hfloor : ∀ q ∈ xs, x ^ a ≤ (q : ℝ))
    (hprod : (xs.prod : ℝ) ≤ x) :
    xs.length ≤ ⌊a⁻¹⌋₊ := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlower := List.prod_map_le_prod_map₀ (fun _ : ℕ => x ^ a)
    (fun q : ℕ => (q : ℝ))
    (fun _ _ => Real.rpow_nonneg hx0.le a) hfloor
  have hpow : x ^ (a * (xs.length : ℝ)) ≤ x ^ (1 : ℝ) := by
    rw [Real.rpow_mul hx0.le, Real.rpow_natCast, Real.rpow_one]
    apply le_trans ?_ hprod
    simpa only [List.map_const', List.prod_replicate, Nat.cast_list_prod] using hlower
  have hlen : a * (xs.length : ℝ) ≤ 1 :=
    (Real.rpow_le_rpow_left_iff hx).mp hpow
  apply (Nat.le_floor_iff (inv_nonneg.mpr ha.le)).mpr
  rw [inv_eq_one_div]
  apply (le_div_iff₀ ha).mpr
  simpa only [mul_comm] using hlen

end
end ImbalancedChen.P2MarkedSourceRankCore
