import ImbalancedChen.P3ActualPrimitivePhysicalRhoSupport
import Mathlib.Tactic

/-!
P3.6 — exact arithmetic separation of the ORIGINAL signed physical rho
response at a nonzero COMPLETE product shift.  Manuscript frozen at
chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product-completion §§1,4 (F), eq:current-PP.

The count uses Q intersect divisors of |N-r*m|, with NO extra product-
primitivity filter.  The exact coprime mean uses the ORIGINAL full-product
gcd filter and the SAME rho(q).  For physical (q,N)=1, divisibility of
the shift automatically supplies product primitivity.  The target
r*m=N is strictly excluded BEFORE forming divisors.

This is a manuscript-internal SOURCE_ONLY proof candidate, not an
arithmetic logarithmic saving, a uniform moment estimate or a proof
of full compiler coverage. UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualOffshiftSignedPhysicalDivisorMean

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualMarkedOffShiftDivisors
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualPrimitivePhysicalRhoSupport

/-- At nonzero complete shift, an original divisor modulus of the
shift must be primitive to the COMPLETE product whenever it is
primitive to the target N. No hypothesis about an auxiliary level,
positive rho, or HB-factor product is introduced. -/
theorem offshift_divisor_is_primitive
    (N r m q : ℕ) (hN : Nat.Coprime N q)
    (hne : r * m ≠ N)
    (hdiv : q ∈ (markedShiftAbs r N m).divisors) :
    Nat.Coprime (r * m) q := by
  by_contra hnon
  have hzero : fineKernel N q (r * m) = 0 :=
    fineKernel_zero_of_nonprimitive_full_product N q (r * m) hN hnon
  have hone : fineKernel N q (r * m) = 1 := by
    rw [fineKernel_marked_off_divisors r N q m hne]
    simp [hdiv, hnon]
  have hbad : (0 : ℝ) = 1 := hzero.symm.trans hone
  norm_num at hbad

/-- Exact signed offshift separation:
  (1) congruence COUNT is the original physical Q intersect the
      divisors of the nonzero COMPLETE shift |N-r*m|;
  (2) MEAN retains precisely the q with gcd(r*m,q)=1, and 1/phi(q).
The same integer signed rho(q) is used in both. This identity does
not require dropping product-primitivity or target-primitivity from
the coprime MEAN. No rho modulus estimate is presumed. -/
theorem sameRhoFixedProductResponse_offshift_count_mean
    (N r m : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hne : r * m ≠ N) :
    sameRhoFixedProductResponse N r m Q rho =
      (∑ q ∈ Q.filter
        (fun q => q ∈ (markedShiftAbs r N m).divisors),
        (rho q : ℂ)) -
      (∑ q ∈ Q.filter (fun q => Nat.Coprime (r * m) q),
        (rho q : ℂ) *
          (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)) := by
  unfold sameRhoFixedProductResponse
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [fineKernel_marked_off_divisors r N q m hne]
  by_cases hd : q ∈ (markedShiftAbs r N m).divisors
  <;> by_cases hc : Nat.Coprime (r * m) q
  <;> simp [hd, hc] <;> push_cast <;> ring

/-- An honest elementary absolute bound obtained from the exact signed
split, without converting signed cancellation into a claimed saving.
The first sum ranges over ORIGINAL physical divisors of the nonzero
shift; the second sum retains the precise primitive mean. -/
theorem sameRhoFixedProductResponse_offshift_norm_le
    (N r m : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hne : r * m ≠ N) :
    ‖sameRhoFixedProductResponse N r m Q rho‖ ≤
      (∑ q ∈ Q.filter
        (fun q => q ∈ (markedShiftAbs r N m).divisors),
        ‖(rho q : ℂ)‖) +
      (∑ q ∈ Q.filter (fun q => Nat.Coprime (r * m) q),
        ‖(rho q : ℂ) *
          (((Nat.totient q : ℝ)⁻¹ : ℝ) : ℂ)‖) := by
  rw [sameRhoFixedProductResponse_offshift_count_mean
    N r m Q rho hne]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))

end
end ImbalancedChen.P3ActualOffshiftSignedPhysicalDivisorMean
