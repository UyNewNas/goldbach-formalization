import ImbalancedChen.P5U7OriginalPhysicalPP
import Mathlib.Tactic

/-!
P3.6 | One genuinely compiled marked prime-product family, the original U7
arithmetic three/four-rank branches. SOURCE_ONLY, NOT LEAN COMPILED.

The original rank-three and rank-four membership itself proves that every
complete physical product is STRICTLY below N. Thus the physical shift
N - product is positive, never the forbidden zero divisor shift.
The existing exact labelled transport and finite Fubini identify the ONE
signed physical rho-weighted PP3+PP4 discrepancy with physical divisor sums
MINUS density and the EXACT coprime correction, after retaining both marked
ranks separately. No assumption of PP, analytic saving, extra prime factor,
or per-fibre relative estimate is introduced.

These P5U7 physical receivers are one concrete manuscript internal
prime-product source; they are NOT the general marked/HB atom compiler,
and the upstream source remains source-only/uncompiled.
-/

namespace ImbalancedChen.P3ActualU7PhysicalOffshift

noncomputable section
open scoped BigOperators Classical
open ImbalancedChen.P5U7OriginalPhysicalPP

/-- The REAL three-prime U7 compiler, not an arbitrary supplied box,
puts the complete physical product strictly below the target. -/
theorem actual_u7_three_full_product_lt_target {N : ℕ} {x : P5U7ThreeLabel}
    (hx : x ∈ p5U7ArithmeticThree N) : p5U7ThreeProduct x < N := by
  rcases p5U7ArithmeticThree_data hx with
    ⟨_, _, _, _, _, _, _, hlt, _⟩
  exact hlt

/-- The same strict physical bound for the actual four-prime U7 compiler.
Repeated terminal prime slots are not discarded. -/
theorem actual_u7_four_full_product_lt_target {N : ℕ} {x : P5U7FourLabel}
    (hx : x ∈ p5U7ArithmeticFour N) : p5U7FourProduct x < N := by
  rcases p5U7ArithmeticFour_data hx with
    ⟨_, _, _, _, _, _, _, _, _, hlt, _⟩
  exact hlt

/-- Both true marked source fibres at COMPLETE product=N are empty;
in particular no shift zero can enter a divisor moment. -/
theorem actual_u7_three_four_no_full_diagonal (N : ℕ) :
    (p5U7ArithmeticThree N).filter (fun x => p5U7ThreeProduct x = N) = ∅ ∧
    (p5U7ArithmeticFour N).filter (fun x => p5U7FourProduct x = N) = ∅ := by
  constructor
  · ext x
    simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
    intro hx
    exact (ne_of_lt (actual_u7_three_full_product_lt_target hx.1)) hx.2
  · ext x
    simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
    intro hx
    exact (ne_of_lt (actual_u7_four_full_product_lt_target hx.1)) hx.2

/-- Exact signed OFF-shift expression of this original two-rank family.
The same Q and rho occur in every divisor sum, density and coprime mean.
The correction is NOT replaced by the total source mass. -/
def actualU7PhysicalOffshift (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
    (∑ x ∈ p5U7ArithmeticThree N,
      physicalDivisorSum Q rho (N - p5U7ThreeProduct x)) +
    (∑ x ∈ p5U7ArithmeticFour N,
      physicalDivisorSum Q rho (N - p5U7FourProduct x)) -
    (p5z_labelledMass (p5U7ArithmeticThree N) (fun _ => (1 : ℝ)) +
      p5z_labelledMass (p5U7ArithmeticFour N) (fun _ => (1 : ℝ))) *
      physicalDensitySum Q rho -
    (p5z_labelledCoprimeCorrection (p5U7ArithmeticThree N)
        p5U7ThreeProduct (fun _ => (1 : ℝ)) Q rho +
      p5z_labelledCoprimeCorrection (p5U7ArithmeticFour N)
        p5U7FourProduct (fun _ => (1 : ℝ)) Q rho)

/-- The two genuine original labelled PP atoms share ONE physical rho.
Their signed errors are added before taking any absolute value; the entire
nonzero physical shift is used, with an exact coprime correction. -/
theorem actual_u7_two_ranks_same_rho_offshift
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho (weight3 N) +
      Part3.primeProductSignedError 4 N N Q rho (weight4 N) =
      actualU7PhysicalOffshift N Q rho := by
  have h3 := p5z_labelled_physical_sum_eq_main_add_errors
    (p5U7ArithmeticThree N) p5U7ThreeProduct (fun _ => (1 : ℝ)) N Q rho
    (by intro x hx; exact (actual_u7_three_full_product_lt_target hx).le)
  have h4 := p5z_labelled_physical_sum_eq_main_add_errors
    (p5U7ArithmeticFour N) p5U7FourProduct (fun _ => (1 : ℝ)) N Q rho
    (by intro x hx; exact (actual_u7_four_full_product_lt_target hx).le)
  simp only [one_mul] at h3 h4
  rw [← distribution3_eq_PP N Q rho, ← distribution4_eq_PP N Q rho]
  unfold actualU7PhysicalOffshift
  linarith only [h3, h4]

/-- The literal original U7 marked source (not a generic rank placeholder)
is the SAME signed off-shift expression: two distinct marked source labels,
one original physical modulus coefficient, no norm split. -/
theorem actual_u7_original_marked_same_rho_offshift
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (Finset.range N) id
        (p5U7ArithmeticProductWeight N) N Q rho =
      actualU7PhysicalOffshift N Q rho := by
  rw [total_source_error_eq_PP3_add_PP4]
  exact actual_u7_two_ranks_same_rho_offshift N Q rho

end
end ImbalancedChen.P3ActualU7PhysicalOffshift
