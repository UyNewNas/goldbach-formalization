import ImbalancedChen.P3ActualMarkedOffShiftDivisors
import ImbalancedChen.ActualPrimeFineLabelSortedSelector

/-!
P3.6 / fixed manuscript 9731290, original fine-prime source and full product.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.

The actual fine prime alphabet explicitly excludes every prime dividing N.
For an EVEN target N this excludes 2, hence EVERY original fine-prime
tuple has ODD product, including the empty tuple. If the outside marked
product r is also odd, its COMPLETE physical integer r * ps.prod cannot
equal an even target T. Thus the full-product=T exceptional fibre vanishes
for this precisely delimited original prime source, not for arbitrary
integer HB variables or unverified marked compiler outputs.

The same signed rho, original geometric W, physical modulus and exact
coprime mean remain unchanged. No analytic discrepancy estimate follows.
-/

namespace ImbalancedChen.P3ActualEvenOriginalPrimeException
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualMarkedOffShiftDivisors

private theorem odd_list_prod (ps : List ℕ)
    (hall : ∀ p ∈ ps, Odd p) : Odd ps.prod := by
  induction ps with
  | nil =>
      simp
  | cons p rest ih =>
      have hp : Odd p := hall p (by simp)
      have hrest : ∀ q ∈ rest, Odd q := by
        intro q hq
        exact hall q (by simp [hq])
      simpa only [List.prod_cons] using hp.mul (ih hrest)

/-- The ACTUAL fine-label prime carrier excludes the even prime,
because its literal membership requires p not dividing the even N.
No lower-cutoff or prime-size surrogate is introduced. -/
theorem actual_fine_prime_odd_of_even_N {N τi p : ℕ} {τ : ℝ}
    (hN : Even N)
    (hp : p ∈ actualPrimeFineLabelFinset N τ τi) : Odd p := by
  have hmem := (mem_actualPrimeFineLabelFinset.mp hp)
  apply hmem.1.odd_of_ne_two
  intro hp2
  exact hmem.2.1 (by
    simpa [hp2] using (even_iff_two_dvd.mp hN))

/-- The genuine strictly sorted original fine-prime box has odd product
when N is even. Sorting is NOT used to permute an arbitrary W; the proof
only reads prime membership in the underlying ordered slot box. -/
theorem actual_sorted_residual_product_odd
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (hN : Even N) (ps : List ℕ)
    (hps : ps ∈ actualPrimeFineLabelSortedTuples N τ blocks) :
    Odd ps.prod := by
  have hbox : ps ∈ actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ) (actualPrimeLabelBlocksWord blocks) := by
    change ps ∈ (actualPrimeSlotBox
      (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord blocks)).filter List.SortedGT at hps
    exact (Finset.mem_filter.mp hps).1
  apply odd_list_prod ps
  exact actualPrimeSlotBox_forall
    (actualPrimeFineLabelFinset N τ)
    (actualPrimeLabelBlocksWord blocks)
    (fun p : ℕ => Odd p)
    (by
      intro i hi p hp
      exact actual_fine_prime_odd_of_even_N hN hp)
    ps hbox

/-- Concrete full physical product parity eliminates the exact-T fibre
for the actual sorted PRIME selector. Oddness of the separate marked
product r is explicit; it is not inferred from an unconnected compiler. -/
theorem actual_sorted_even_full_fibre_empty
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (T r : ℕ) (hN : Even N) (hT : Even T) (hr : Odd r) :
    (actualPrimeFineLabelSortedTuples N τ blocks).filter
      (fun ps => r * ps.prod = T) = ∅ := by
  classical
  ext ps
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro h
  rcases h with ⟨hps, hfull⟩
  have hodd : Odd (r * ps.prod) :=
    hr.mul (actual_sorted_residual_product_odd N τ blocks hN ps hps)
  have heven : Even (r * ps.prod) := by
    rw [hfull]
    exact hT
  exact ((not_even_iff_odd).mpr hodd) heven

/-- Consequently the FULL original signed-rho exact-product term is
zero for this genuinely original prime selector, even with arbitrary
tuple-dependent W, a signed restoring scalar, and arbitrary rho. -/
theorem actual_sorted_even_exact_source_zero
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ)
    (hN : Even N) (hT : Even T) (hr : Odd r) :
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun ps => r * ps.prod = T),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps * fineKernel T q (r * ps.prod)) = 0 := by
  rw [actual_sorted_even_full_fibre_empty N τ blocks T r hN hT hr]
  simp

/-- For this ACTUAL ORIGINAL PRIME source the entire signed
complete-modulus discrepancy equals its NONZERO FULL-SHIFT divisor
expression. It still retains the literal exact coprime mean, arbitrary
positional W and the same rho. This is NOT a mixed-moment bound and
does NOT extend to unconstrained HB integer factors. -/
theorem weightedSortedPP_even_eq_full_shift_divisors
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ)
    (hN : Even N) (hT : Even T) (hr : Odd r) :
    weightedSortedPP N τ blocks Q rho T r c W =
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun ps => r * ps.prod ≠ T),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps *
          ((if q ∈ (markedShiftAbs r T ps.prod).divisors
              then (1 : ℝ) else 0) -
           (if Nat.Coprime (r * ps.prod) q
              then (Nat.totient q : ℝ)⁻¹ else 0))) := by
  rw [weightedSortedPP_split_full_product]
  rw [actual_sorted_even_full_fibre_empty N τ blocks T r hN hT hr]
  simpa using (weightedSortedPP_off_divisors N τ blocks Q rho T r c W)

end
end ImbalancedChen.P3ActualEvenOriginalPrimeException
