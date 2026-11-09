import ImbalancedChen.P3ActualU8ExactTargetResponse
import Mathlib.Tactic

/-!
P3.6 — arithmetic removal of the exact-product=N diagonal for a
GEOMETRICALLY supported rank-three weight on ORIGINAL labelled primes.

This is a new alternative to trying to bound the signed targetResponse:
when N is even and the geometric support keeps each prime coordinate
strictly above 2, all three actual primes are odd, hence their complete
product cannot equal N. The precise source hypothesis is the manuscript's
lower geometric cutoff c*N^a > 2 on every nonzero labelled W tuple.
No parity mask is inserted into W and no modulus-dependent filter is used.

The result is restricted to prime rank three and even N. It does not
cover arbitrary HB integer slots or prove that an arbitrary proposed W
has the required lower cutoff, derivative budget or Fourier norm.
No analytic PP saving or external theorem is used. Compilation pending.
-/

namespace ImbalancedChen.P3ActualU8EvenGeometricTarget

noncomputable section
open scoped BigOperators
open Classical
open ImbalancedChen.P3ActualU8StrictPhysicalPP
open ImbalancedChen.P3ActualU8StrictSmoothBoundary
open ImbalancedChen.P3ActualU8StrictBoundarySourcewise
open ImbalancedChen.P3ActualU8ExactTargetResponse

/-- Each original labelled prime is odd once the actual coordinate is
strictly above 2. In particular, the complete three-prime product is
odd. This uses the ORIGINAL Part3 product over all three labels. -/
theorem labelledProduct_odd_of_coordinate_gt_two
    (N : ℕ) (u : Fin 3 → Fin (N + 1))
    (hu : u ∈ Part3.labelledPrimeTuples 3 N)
    (hbig : ∀ i : Fin 3, 2 < (u i).val) :
    Odd (Part3.labelledProduct u) := by
  have hprime : ∀ i : Fin 3, Nat.Prime (u i).val :=
    (Finset.mem_filter.mp hu).2
  have hodd (i : Fin 3) : Odd (u i).val :=
    (hprime i).odd_of_ne_two (by have hi := hbig i; omega)
  simpa only [Part3.labelledProduct, Fin.prod_univ_three] using
    ((hodd 0).mul (hodd 1)).mul (hodd 2)

/-- The manuscript's geometric lower cutoff c*N^a (not a parity
filter) prevents ANY exact-product=N label from carrying nonzero W
when N is even and 2<c*N^a. Labels are not deduplicated by product.

This theorem proves the entire target W mass is ZERO, rather than
assuming a bound on the target fibre or on the physical response. -/
theorem target_weight_mass_zero_of_geometric_cutoff
    (N : ℕ) (hEven : Even N)
    (c a : ℝ) (hcut : (2 : ℝ) < c * (N : ℝ) ^ a)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (hgeo : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      W u ≠ 0 → ∀ i : Fin 3,
        c * (N : ℝ) ^ a ≤ ((u i).val : ℝ)) :
    (∑ u ∈ targetProductLabels N, W u) = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  have hl : u ∈ Part3.labelledPrimeTuples 3 N :=
    (Finset.mem_filter.mp hu).1
  have hp : Part3.labelledProduct u = N :=
    (Finset.mem_filter.mp hu).2
  by_contra hW
  have hbig (i : Fin 3) : 2 < (u i).val := by
    have hi : (2 : ℝ) < ((u i).val : ℝ) :=
      lt_of_lt_of_le hcut (hgeo u hl hW i)
    exact_mod_cast hi
  have hodd : Odd N := by
    rw [← hp]
    exact labelledProduct_odd_of_coordinate_gt_two N u hl hbig
  exact (not_odd_iff_even.mpr hEven) hodd

/-- For the SAME arbitrary signed physical Q/rho as in the preceding
rank-three exact-target factorization, the entire target-product
contribution to strict-minus-geometric PP is exactly ZERO.

No smallness or cancellation of targetResponse is required: the
geometrically admitted labelled target fibre is empty. This does
not remove off-target arithmetic boundary costs or other HB sources. -/
theorem target_signed_exception_zero_of_geometric_cutoff
    (N : ℕ) (hEven : Even N)
    (c a : ℝ) (hcut : (2 : ℝ) < c * (N : ℝ) ^ a)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin 3 → Fin (N + 1)) → ℝ)
    (hgeo : ∀ u ∈ Part3.labelledPrimeTuples 3 N,
      W u ≠ 0 → ∀ i : Fin 3,
        c * (N : ℝ) ^ a ≤ ((u i).val : ℝ)) :
    (∑ q ∈ Q, rho q *
      ∑ u ∈ targetProductLabels N,
        (strictPhysicalWeight N u - W u) * physicalKernel N q u) = 0 := by
  calc
    _ = -(∑ u ∈ targetProductLabels N, W u) *
          targetResponse N Q rho :=
      target_product_signed_factor N Q rho W
    _ = 0 := by
      rw [target_weight_mass_zero_of_geometric_cutoff
        N hEven c a hcut W hgeo]
      ring

end
end ImbalancedChen.P3ActualU8EvenGeometricTarget
