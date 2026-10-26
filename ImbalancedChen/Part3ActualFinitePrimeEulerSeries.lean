import ImbalancedChen.Part3FinitePrimeExponentLattice
import ImbalancedChen.Part3ActualCriticalPrimeEulerSeries

/-! True finite distinct-prime exponent-lattice series, including every
nonnegative coordinate exponent. Actual head/tail coefficient splitting
and native norm-product induction pay absolute convergence and the full
finite Euler evaluation. No tuple factorization or series convergence is
an assumption. SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Complex
open scoped BigOperators
open ImbalancedChen.Part3ActualRamanujanDirichletSeries
open ImbalancedChen.Part3.NormalizedEisensteinPrimeAmplitude20261026b
open ImbalancedChen.Part3.FinitePrimeExponentLattice20261026b
open ImbalancedChen.Part3.ActualCriticalPrimeEulerSeries20261026b

namespace ImbalancedChen.Part3.ActualFinitePrimeEulerSeries20261026b

/-- Genuine absolute convergence over the complete finite prime-exponent
lattice; no exponent cutoff, repetition deletion or series premise. -/
theorem finitePrimeEuler_norm_summable (L : List ℕ) (hL : L.Nodup)
    (hPrime : ∀ p ∈ L, p.Prime) (t : ℝ) (X : ℕ → ℂ)
    (hX : ∀ p ∈ L, ‖X p‖ < 1) :
    Summable (fun e : PrimeExponentCarrier L => ‖finitePrimeEulerTerm L t X e‖) := by
  induction L generalizing hL hPrime hX with
  | nil => exact summable_fintype _
  | cons p L ih =>
      obtain ⟨hnot, hTail⟩ := List.nodup_cons.mp hL
      have hp : p.Prime := hPrime p (by simp)
      have hTailPrime : ∀ q ∈ L, q.Prime := fun q hq => hPrime q (List.mem_cons_of_mem _ hq)
      have hTailX : ∀ q ∈ L, ‖X q‖ < 1 := fun q hq => hX q (List.mem_cons_of_mem _ hq)
      have hf := actualCriticalLocalEuler_norm_summable hp t (hX p (by simp))
      have hg := ih hTail hTailPrime hTailX
      have hprod := hf.mul_norm hg
      exact hprod.congr (fun e => congrArg norm
        (finitePrimeEulerTerm_cons hp L hTailPrime hnot t X e).symm)

/-- Every local denominator in the literal finite product is genuinely
nonzero, so no totalized inverse hides a local singularity. -/
theorem finitePrimeEuler_denominators_ne_zero (L : List ℕ)
    (hPrime : ∀ p ∈ L, p.Prime) (t : ℝ) (X : ℕ → ℂ)
    (hX : ∀ p ∈ L, ‖X p‖ < 1) :
    (L.map (fun p => 1 - criticalPrimeScalar p t * X p + (X p) ^ 2)).prod ≠ 0 := by
  induction L generalizing hPrime hX with
  | nil => simp
  | cons p L ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_ne_zero
        (actualCriticalLocalEuler_eq_inverse (hPrime p (by simp)) t (hX p (by simp))).1
        (ih (fun q hq => hPrime q (List.mem_cons_of_mem _ hq))
          (fun q hq => hX q (List.mem_cons_of_mem _ hq)))

/-- The original infinite coefficient sum on the actual injective
integer-frequency lattice equals the genuine finite Euler product.
Coordinate exponents remain unbounded; the prime list alone is finite. -/
theorem finitePrimeEuler_eq_product (L : List ℕ) (hL : L.Nodup)
    (hPrime : ∀ p ∈ L, p.Prime) (t : ℝ) (X : ℕ → ℂ)
    (hX : ∀ p ∈ L, ‖X p‖ < 1) :
    (∑' e : PrimeExponentCarrier L, finitePrimeEulerTerm L t X e) =
      (L.map (fun p => (1 - criticalPrimeScalar p t * X p + (X p) ^ 2)⁻¹)).prod := by
  induction L generalizing hL hPrime hX with
  | nil =>
      simp [PrimeExponentCarrier, finitePrimeEulerTerm, exponentFrequency,
        exponentWeight, normalizedDivisorAmplitude, divisorFactor]
  | cons p L ih =>
      obtain ⟨hnot, hTail⟩ := List.nodup_cons.mp hL
      have hp : p.Prime := hPrime p (by simp)
      have hTailPrime : ∀ q ∈ L, q.Prime := fun q hq => hPrime q (List.mem_cons_of_mem _ hq)
      have hTailX : ∀ q ∈ L, ‖X q‖ < 1 := fun q hq => hX q (List.mem_cons_of_mem _ hq)
      have hf := actualCriticalLocalEuler_norm_summable hp t (hX p (by simp))
      have hg := finitePrimeEuler_norm_summable L hTail hTailPrime t X hTailX
      calc
        _ = ∑' e : ℕ × PrimeExponentCarrier L,
            (normalizedDivisorAmplitude (p ^ e.1) (1 / 2 + (t : ℂ) * Complex.I) * X p ^ e.1) *
              finitePrimeEulerTerm L t X e.2 :=
          tsum_congr (finitePrimeEulerTerm_cons hp L hTailPrime hnot t X)
        _ = actualCriticalLocalEulerSeries p t (X p) *
            (∑' e : PrimeExponentCarrier L, finitePrimeEulerTerm L t X e) :=
          (tsum_mul_tsum_of_summable_norm hf hg).symm
        _ = (1 - criticalPrimeScalar p t * X p + (X p) ^ 2)⁻¹ *
            (L.map (fun q => (1 - criticalPrimeScalar q t * X q + (X q) ^ 2)⁻¹)).prod := by
          rw [(actualCriticalLocalEuler_eq_inverse hp t (hX p (by simp))).2,
            ih hTail hTailPrime hTailX]
        _ = _ := rfl

end ImbalancedChen.Part3.ActualFinitePrimeEulerSeries20261026b
