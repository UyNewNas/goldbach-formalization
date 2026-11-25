import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL OR KERNEL CREDIT.

In a tuple with at least two slots and every entry at least two, another
slot supplies the factor two. Equal values at different slots are allowed.
The complete-product cap remains 2*N; no product <= N conclusion is used.
-/
namespace ImbalancedChen.P2PrimeProductCoordinateCore

open Finset
open scoped BigOperators

theorem two_mul_coordinate_le_prod {d : ℕ} (hd : 2 ≤ d)
    (u : Fin d → ℕ) (hu : ∀ i, 2 ≤ u i) (i : Fin d) :
    2 * u i ≤ ∏ j, u j := by
  obtain ⟨j, hji⟩ : ∃ j : Fin d, j ≠ i := by
    by_cases hi : i.val = 0
    · refine ⟨⟨1, by omega⟩, ?_⟩
      intro h
      have hval := congrArg Fin.val h
      change 1 = i.val at hval
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      have hval := congrArg Fin.val h
      change 0 = i.val at hval
      exact hi hval.symm
  calc
    2 * u i = u i * 2 := Nat.mul_comm _ _
    _ ≤ u i * u j := Nat.mul_le_mul_left _ (hu j)
    _ ≤ ∏ j, u j := Finset.mul_le_prod
      (s := (univ : Finset (Fin d))) (f := u)
      (fun j _ => (by decide : (1 : ℕ) ≤ 2).trans (hu j))
      (mem_univ i) (mem_univ j) (Ne.symm hji)

theorem coordinate_le_of_prod_le_two_mul {N d : ℕ} (hd : 2 ≤ d)
    (u : Fin d → ℕ) (hu : ∀ i, 2 ≤ u i)
    (hprod : (∏ i, u i) ≤ 2 * N) (i : Fin d) :
    u i ≤ N := by
  have h := (two_mul_coordinate_le_prod hd u hu i).trans hprod
  omega

end ImbalancedChen.P2PrimeProductCoordinateCore
