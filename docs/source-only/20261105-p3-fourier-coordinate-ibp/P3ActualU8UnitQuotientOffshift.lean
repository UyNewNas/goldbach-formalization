import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP

/-!
P3.6 SOURCE_ONLY: the genuine U8 q=1 QUOTIENT fibre, not the
repeated terminal prime q=p2 and not a physical sieve modulus q.

The original U8 count is prime-quotient triples PLUS these labelled
unit-quotient pairs. The pair product remains the complete physical
product for this source; it is not an empty Gamma mother word.
Every congruence count and exact coprime mean uses the same physical
Q and signed rho. No PP saving or source coverage is assumed.
UNCOMPILED; kernel/CI have NOT been run.
-/

namespace ImbalancedChen.P3ActualU8UnitQuotientOffshift

noncomputable section
open scoped BigOperators
open Classical
open ImbalancedChen.P5U8SharpKSource

def unitPairProduct (p : ℕ × ℕ) : ℕ := p.1 * p.2

/-- In the literal source the quotient ONE has a positive prime
receiver, hence the complete pair product is STRICTLY below N.
This is not a claim that the terminal prime q=1 is a prime. -/
theorem actual_u8_unit_product_lt_target {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ currentChenUpsilon8UnitFibres N) :
    unitPairProduct p < N := by
  obtain ⟨hpair, hunit⟩ := Finset.mem_filter.mp hp
  have hselected : p ∈ pairSelector N := hpair
  have hprimes := pair_prime_data hselected
  have hpositive : 0 < p.1 * p.2 :=
    mul_pos hprimes.1.pos hprimes.2.1.pos
  have hraw : (1 : ℕ) ∈ chenQuotientPrimeSource N (p.1 * p.2) :=
    (Finset.mem_filter.mp hunit).1
  obtain ⟨P, hP, heq, hlt, hq, hreal⟩ :=
    currentChenUpsilon9_quotient_witness hpositive hraw
  simpa only [unitPairProduct, mul_one] using hlt

/-- Positive complete-product shift: the unit QUOTIENT does not
create an actual product=N diagonal. -/
theorem actual_u8_unit_shift_pos {N : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ currentChenUpsilon8UnitFibres N) :
    0 < N - unitPairProduct p :=
  Nat.sub_pos.mpr (actual_u8_unit_product_lt_target hp)

/-- Exact diagonal exclusion on the literal labelled unit-pair set. -/
theorem actual_u8_unit_exact_fibre_empty (N : ℕ) :
    (currentChenUpsilon8UnitFibres N).filter
      (fun p => unitPairProduct p = N) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hlabel, hprod⟩ := Finset.mem_filter.mp hp
  exact (ne_of_lt (actual_u8_unit_product_lt_target hlabel)) hprod

/-- Full physical divisor expression for the missing q=1 U8
quotient family. The original pair labels are not collapsed by
product image. The last term is the EXACT coprime correction. -/
def actualU8UnitOffshift (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  (∑ p ∈ currentChenUpsilon8UnitFibres N,
      physicalDivisorSum Q rho (N - unitPairProduct p)) -
    p5z_labelledMass (currentChenUpsilon8UnitFibres N)
      (fun _ => (1 : ℝ)) * physicalDensitySum Q rho -
    p5z_labelledCoprimeCorrection (currentChenUpsilon8UnitFibres N)
      unitPairProduct (fun _ => (1 : ℝ)) Q rho

/-- Genuine unit-quotient signed distribution minus exact coprime mean
equals its nonzero complete-product divisor expression, for ONE
unchanged rho and original physical Q. -/
theorem actual_u8_unit_same_rho_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
      unitPairProduct (fun _ => (1 : ℝ)) N Q rho =
    actualU8UnitOffshift N Q rho := by
  have hmain := p5z_labelled_physical_sum_eq_main_add_errors
    (currentChenUpsilon8UnitFibres N) unitPairProduct
    (fun _ => (1 : ℝ)) N Q rho
    (by
      intro p hp
      exact (actual_u8_unit_product_lt_target hp).le)
  simp only [one_mul] at hmain
  unfold actualU8UnitOffshift
  linarith only [hmain]

/-- The original U8 arithmetic source is prime-quotient triples
together with q=1 PAIRS. Both receive the SAME physical signed
modulus coefficient before taking any absolute value.
The prime triple part is the existing genuine physical rank-3 PP
coefficient; the unit part remains its actual labelled pair source. -/
def actualU8PrimeUnitOffshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  (∑ t ∈ arithmeticTriples N,
      physicalDivisorSum Q rho (N - product t)) +
  (∑ p ∈ currentChenUpsilon8UnitFibres N,
      physicalDivisorSum Q rho (N - unitPairProduct p)) -
  (p5z_labelledMass (arithmeticTriples N) (fun _ => (1 : ℝ)) +
    p5z_labelledMass (currentChenUpsilon8UnitFibres N)
      (fun _ => (1 : ℝ))) * physicalDensitySum Q rho -
  (p5z_labelledCoprimeCorrection (arithmeticTriples N) product
      (fun _ => (1 : ℝ)) Q rho +
    p5z_labelledCoprimeCorrection (currentChenUpsilon8UnitFibres N)
      unitPairProduct (fun _ => (1 : ℝ)) Q rho)

/-- Signed sum of both ACTUAL U8 source types. Not an analytic PP
estimate, not a coupling to the final integer rho_T, and not a
replacement for any general HB atom source. -/
theorem actual_u8_prime_unit_same_rho_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho (physicalWeight N) +
      p5z_labelledDistributionError (currentChenUpsilon8UnitFibres N)
        unitPairProduct (fun _ => (1 : ℝ)) N Q rho =
    actualU8PrimeUnitOffshift N Q rho := by
  have hprime := p5z_labelled_physical_sum_eq_main_add_errors
    (arithmeticTriples N) product (fun _ => (1 : ℝ)) N Q rho
    (by
      intro t ht
      exact (arithmetic_product_lt ht).le)
  have hunit := p5z_labelled_physical_sum_eq_main_add_errors
    (currentChenUpsilon8UnitFibres N) unitPairProduct
    (fun _ => (1 : ℝ)) N Q rho
    (by
      intro p hp
      exact (actual_u8_unit_product_lt_target hp).le)
  simp only [one_mul] at hprime hunit
  rw [← distribution_eq_physicalPP N Q rho]
  unfold actualU8PrimeUnitOffshift
  linear_combination -hprime -hunit

end

end ImbalancedChen.P3ActualU8UnitQuotientOffshift
