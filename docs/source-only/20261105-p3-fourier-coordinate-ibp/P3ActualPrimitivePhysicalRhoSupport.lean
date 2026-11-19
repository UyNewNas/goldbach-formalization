import ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
import ImbalancedChen.P3ActualMarkedOffShiftDivisors
import Mathlib.Data.Nat.ModEq

/-!
P3.6 / frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§1,3,4: primitive physical-modulus support
for the genuine full product (three frozen fine-prime words)*(literal HB m).

Unlike an unrestricted mean replacement, the original exact coprime
mean and the same integer signed rho survive. The congruence indicator
itself forces the product to be a unit at every physical q coprime to N.
Thus every NONunit product term has exact zero discrepancy, and the
nonzero-shift signed response is supported on Q intersect the units of
the COMPLETE physical product, with its true divisors of |N-r*m|.

No full PP compiler exhaustiveness, shifted-divisor bound, rho mass
estimate, actual W_T admission or Fourier inversion is asserted.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualPrimitivePhysicalRhoSupport
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualMarkedOffShiftDivisors
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualFrozenWholeBoxHBOffshift
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords

/-- Exact original congruence plus target primitivity implies
primitivity of the COMPLETE product, including any literal HB factor.
This is gcd invariance of congruent integers, not a distribution input. -/
theorem full_product_coprime_of_target_congruent
    (N q B : ℕ) (hN : Nat.Coprime N q)
    (hc : B % q = N % q) : Nat.Coprime B q := by
  have hmod : Nat.ModEq q B N := hc
  have hgcd : Nat.gcd B q = Nat.gcd N q := hmod.gcd_eq
  change Nat.gcd B q = 1
  exact hgcd.trans hN

/-- On the original physical moduli (q,N)=1, a nonunit FULL product
contributes neither a congruence count nor its exact coprime mean.
This holds at q=0 as well if the stated coprimality permits it. -/
theorem fineKernel_zero_of_nonprimitive_full_product
    (N q B : ℕ) (hN : Nat.Coprime N q)
    (hB : ¬ Nat.Coprime B q) :
    fineKernel N q B = 0 := by
  have hc : B % q ≠ N % q := by
    intro he
    exact hB (full_product_coprime_of_target_congruent N q B hN he)
  rw [fineKernel_literal]
  simp [hc, hB]

/-- Remove every nonunit physical modulus at its ORIGINAL complete
product, after preserving signed integer rho inside the same response.
This does not replace the mean by an unrestricted reciprocal totient. -/
theorem sameRhoFixedProductResponse_restrict_primitive
    (N r m : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hQ : ∀ q ∈ Q, Nat.Coprime N q) :
    sameRhoFixedProductResponse N r m Q rho =
      ∑ q ∈ Q.filter (fun q => Nat.Coprime (r * m) q),
        (rho q : ℂ) *
          (((fineKernel N q (r * m) : ℝ) : ℂ)) := by
  unfold sameRhoFixedProductResponse
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hB : Nat.Coprime (r * m) q
  · simp [hB]
  · have hzero : fineKernel N q (r * m) = 0 :=
      fineKernel_zero_of_nonprimitive_full_product
        N q (r * m) (hQ q hq) hB
    simp [hB, hzero]

/-- NONZERO full physical shift: exact signed restricted divisor-minus-
mean formula. In particular, divisisors(0) is NEVER formed. The
coprime indicator is discharged only on the filtered primitive Q,
and the filter depends on the full product r*m, not on m alone. -/
theorem sameRhoFixedProductResponse_offshift_primitive
    (N r m : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hQ : ∀ q ∈ Q, Nat.Coprime N q)
    (hne : r * m ≠ N) :
    sameRhoFixedProductResponse N r m Q rho =
      ∑ q ∈ Q.filter (fun q => Nat.Coprime (r * m) q),
        (rho q : ℂ) *
          ((((if q ∈ (markedShiftAbs r N m).divisors
               then (1 : ℝ) else 0) -
             (Nat.totient q : ℝ)⁻¹) : ℝ) : ℂ) := by
  rw [sameRhoFixedProductResponse_restrict_primitive
    N r m Q rho hQ]
  apply Finset.sum_congr rfl
  intro q hq
  have hB : Nat.Coprime (r * m) q := (Finset.mem_filter.mp hq).2
  rw [fineKernel_marked_off_divisors r N q m hne]
  simp [hB]

/-- Exact complete product N is NOT treated as a nonzero shift. Its
signed physical mass survives intact, with the EXACT primitive mean. -/
theorem sameRhoFixedProductResponse_exact_target
    (N r m : ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (hQ : ∀ q ∈ Q, Nat.Coprime N q)
    (heq : r * m = N) :
    sameRhoFixedProductResponse N r m Q rho =
      ∑ q ∈ Q, (rho q : ℂ) *
        (((1 - (Nat.totient q : ℝ)⁻¹ : ℝ) : ℝ) : ℂ) := by
  unfold sameRhoFixedProductResponse
  apply Finset.sum_congr rfl
  intro q hq
  rw [heq, fineKernel_exact N q (hQ q hq)]

/-- Genuine THREE independent frozen boxes and the original ordered
rough-HB positional coefficient: each physical response is restricted
to moduli primitive to its own COMPLETE product. One signed rho appears
in both the residue count and the exact coprime mean; positional W,
the HB log/Mobius/rough mask and duplicate prime values remain intact.

This is source admission only for the previously defined three boxes,
not the full unproved PP/HB atom compiler. -/
theorem threeWholeHB_sameRho_restrict_primitive
    (N m j : ℕ) (τ z y : ℝ)
    (u v w : List ℕ) (Q : Finset ℕ) (rho : ℕ → ℤ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hQ : ∀ q ∈ Q, Nat.Coprime N q) :
    (∑ q ∈ Q, (rho q : ℂ) *
      threeWholeHBAtQ N m j q τ z y u v w W) =
      ∑ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
        ∑ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
          ∑ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
            hbPositionalMass m j z y W a b d *
              (∑ q ∈ Q.filter
                (fun q => Nat.Coprime
                  (a.prod * b.prod * d.prod * m) q),
                (rho q : ℂ) *
                  (((fineKernel N q
                     (a.prod * b.prod * d.prod * m) : ℝ) : ℂ))) := by
  rw [threeWholeHB_sameRho_fixed]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  rw [sameRhoFixedProductResponse_restrict_primitive
    N (a.prod * b.prod * d.prod) m Q rho hQ]

end
end ImbalancedChen.P3ActualPrimitivePhysicalRhoSupport
