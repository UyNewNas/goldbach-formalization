import ImbalancedChen.P2PrimeProductCoordinateCore
import ImbalancedChen.P2FiniteMarkedGamma5AtlasEulerBudget
import ImbalancedChen.Part5OriginalH430SmoothPrefixRequests

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL OR KERNEL CREDIT.

The complete Gamma5 tuple always has at least its two fresh slots. Under
the explicit complete-product cap 2*N, primality therefore puts each slot
in Fin(N+1) and, for N >= 2, every original logarithmic coordinate in the
old atlas Cube. Repeated primes and empty old/tail blocks are retained.

The logarithmic unit-interval proof is the existing physicalPrime_unit.
This is a coordinate/carrier bridge, not a selected-history dictionary.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5PrimeCube

noncomputable section
open Finset
open Part5OriginalH430JointQueryEnclosure (Cube)
open P2FiniteMarkedGamma5AtlasEulerBudget (oldLogCoordinates)
open P2PrimeProductCoordinateCore
open scoped Classical BigOperators

theorem prime_coordinates_le_target {N k r : ℕ}
    (u : Fin (k + (2 + r)) → ℕ) (hu : ∀ i, (u i).Prime)
    (hprod : (∏ i, u i) ≤ 2 * N) (i : Fin (k + (2 + r))) :
    u i ≤ N :=
  coordinate_le_of_prod_le_two_mul (by omega) u (fun j => (hu j).two_le) hprod i

/-- The same natural values enter the old target-sized coordinate type.
This does not sort, quotient, identify, or delete any slot. -/
theorem prime_tuple_in_target_carrier {N k r : ℕ}
    (u : Fin (k + (2 + r)) → ℕ) (hu : ∀ i, (u i).Prime)
    (hprod : (∏ i, u i) ≤ 2 * N) :
    ∃ v : Fin (k + (2 + r)) → Fin (N + 1), ∀ i, (v i).val = u i :=
  ⟨fun i => ⟨u i, Nat.lt_succ_of_le (prime_coordinates_le_target u hu hprod i)⟩,
    fun _ => rfl⟩

/-- Exact transfer from the existing 2*N bounded enumerator. -/
theorem bounded_prime_tuple_in_target_carrier {N k r : ℕ}
    (u : Fin (k + (2 + r)) → Fin (2 * N + 1))
    (hu : ∀ i, (u i).val.Prime)
    (hprod : (∏ i, (u i).val) ≤ 2 * N) :
    ∃ v : Fin (k + (2 + r)) → Fin (N + 1), ∀ i, (v i).val = (u i).val :=
  prime_tuple_in_target_carrier (fun i => (u i).val) hu hprod

theorem prime_log_cube {N k r : ℕ} (hN : 2 ≤ N)
    (u : Fin (k + (2 + r)) → ℕ) (hu : ∀ i, (u i).Prime)
    (hprod : (∏ i, u i) ≤ 2 * N) :
    Cube (fun i => Real.log (u i : ℝ) / Real.log (N : ℝ)) := by
  intro i
  exact Part5OriginalH430SmoothPrefixRequests.physicalPrime_unit
    (by omega : 1 < N) (hu i).one_lt.le (prime_coordinates_le_target u hu hprod i)

/-- The precise old-coordinate function used by AtlasEulerBudget is in
the original Cube. For k = 0 this is the unchanged empty-coordinate cube. -/
theorem old_log_cube {N k r : ℕ} (hN : 2 ≤ N)
    (u : Fin (k + (2 + r)) → ℕ) (hu : ∀ i, (u i).Prime)
    (hprod : (∏ i, u i) ≤ 2 * N) :
    Cube (oldLogCoordinates (k := k) (r := r) (N : ℝ) (fun i => (u i : ℝ))) := by
  intro i
  exact prime_log_cube hN u hu hprod (Fin.castAdd (2 + r) i)

end
end ImbalancedChen.P2FiniteMarkedGamma5PrimeCube
