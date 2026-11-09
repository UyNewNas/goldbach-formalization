import ImbalancedChen.Part3DistributionTargets
import Mathlib.Tactic

/-!
P3.6 — the exact complete-product=T diagonal of EVERY original labelled
prime-product rank is absent from a geometrically admitted source once
the prime-coordinate lower cutoff exceeds 2 and T is even.

The k=3 U8 result already had this argument. Here the original Part3
rank-k labelled carrier and genuine primeProductSignedError are used
without deduplicating tuples, changing the physical Q/rho, inserting an
arithmetic parity mask into W, or asserting an unproved PP estimate.

These are SOURCE_ONLY candidates; no Lean elaboration or kernel check has
been performed. HB integer slots are NOT original prime coordinates
and are not covered by this argument.
-/

namespace ImbalancedChen.P3ActualAllRankGeometricTarget

noncomputable section
open scoped BigOperators
open Classical

/-- The product of ANY finite number of original labelled primes, each
strictly above 2, is odd. The empty product is 1. -/
theorem labelledProduct_odd_of_all_gt_two
    (k P : ℕ) (u : Fin k → Fin (P + 1))
    (hu : u ∈ Part3.labelledPrimeTuples k P)
    (hbig : ∀ i : Fin k, 2 < (u i).val) :
    Odd (Part3.labelledProduct u) := by
  have hprime : ∀ i : Fin k, Nat.Prime (u i).val :=
    (Finset.mem_filter.mp hu).2
  have hodd (i : Fin k) : Odd (u i).val :=
    (hprime i).odd_of_ne_two (by have hi := hbig i; omega)
  have hprod : ∀ s : Finset (Fin k), Odd (∏ i ∈ s, (u i).val) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simpa [Finset.prod_insert hi] using (hodd i).mul ih
  simpa [Part3.labelledProduct] using (hprod Finset.univ)

/-- A positive geometric lower scale above 2 kills any weight on a
labelled prime tuple whose complete product is the EVEN target.
This is pointwise and does not require any bound on rho or a fibre
distribution theorem; P is the actual coordinate cap. -/
theorem geometric_weight_zero_at_target
    (k P N : ℕ) (hEven : Even N)
    (c a : ℝ) (hcut : (2 : ℝ) < c * (N : ℝ) ^ a)
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (hgeo : ∀ u ∈ Part3.labelledPrimeTuples k P,
      W u ≠ 0 → ∀ i : Fin k,
        c * (N : ℝ) ^ a ≤ ((u i).val : ℝ))
    (u : Fin k → Fin (P + 1))
    (hu : u ∈ Part3.labelledPrimeTuples k P)
    (hp : Part3.labelledProduct u = N) :
    W u = 0 := by
  by_contra hW
  have hbig (i : Fin k) : 2 < (u i).val := by
    have hi : (2 : ℝ) < ((u i).val : ℝ) :=
      lt_of_lt_of_le hcut (hgeo u hu hW i)
    exact_mod_cast hi
  have hodd : Odd N := by
    rw [← hp]
    exact labelledProduct_odd_of_all_gt_two k P u hu hbig
  exact (not_odd_iff_even.mpr hEven) hodd

/-- The exact target-product labelled mass vanishes at EVERY rank k,
without collapsing different source tuples having the same product. -/
theorem target_label_mass_zero
    (k P N : ℕ) (hEven : Even N)
    (c a : ℝ) (hcut : (2 : ℝ) < c * (N : ℝ) ^ a)
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (hgeo : ∀ u ∈ Part3.labelledPrimeTuples k P,
      W u ≠ 0 → ∀ i : Fin k,
        c * (N : ℝ) ^ a ≤ ((u i).val : ℝ)) :
    (∑ u ∈ (Part3.labelledPrimeTuples k P).filter
      (fun u => Part3.labelledProduct u = N), W u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hl := (Finset.mem_filter.mp hu).1
  have hp := (Finset.mem_filter.mp hu).2
  exact geometric_weight_zero_at_target k P N hEven c a hcut W hgeo u hl hp

/-- The actual Part3 physical signed-error functional vanishes on the
EXACT-TARGET portion of a geometrically admitted original-prime W.
The same arbitrary Q and signed rho are retained in both the AP count
and the exact coprime mean. This is NOT a bound on the off-target part,
nor does it establish the required admissible W_T class. -/
theorem target_fibre_physical_signed_error_zero
    (k P N : ℕ) (hEven : Even N)
    (c a : ℝ) (hcut : (2 : ℝ) < c * (N : ℝ) ^ a)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ)
    (hgeo : ∀ u ∈ Part3.labelledPrimeTuples k P,
      W u ≠ 0 → ∀ i : Fin k,
        c * (N : ℝ) ^ a ≤ ((u i).val : ℝ)) :
    Part3.primeProductSignedError k P N Q rho
      (fun u => if Part3.labelledProduct u = N then W u else 0) = 0 := by
  unfold Part3.primeProductSignedError
  apply Finset.sum_eq_zero
  intro q hq
  have hinner :
      (∑ u ∈ Part3.labelledPrimeTuples k P,
        (if Part3.labelledProduct u = N then W u else 0) *
          ((if Nat.ModEq q (Part3.labelledProduct u) N
            then (1 : ℝ) else 0) -
           (if Nat.Coprime (Part3.labelledProduct u) q
            then (1 : ℝ) else 0) / (Nat.totient q : ℝ))) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    by_cases hp : Part3.labelledProduct u = N
    · simp [hp, geometric_weight_zero_at_target
        k P N hEven c a hcut W hgeo u hu hp]
    · simp [hp]
  rw [hinner, mul_zero]

end
end ImbalancedChen.P3ActualAllRankGeometricTarget
