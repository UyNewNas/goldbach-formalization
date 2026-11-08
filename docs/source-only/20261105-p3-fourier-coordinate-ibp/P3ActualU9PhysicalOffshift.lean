import ImbalancedChen.CurrentChenP5U9OrderedPhysicalPP
import Mathlib.Tactic

/-!
P3.6 | Actual U9 three ordered marked-prime branches, complete physical
off-shift at ONE signed rho. SOURCE_ONLY / NOT LEAN COMPILED.

This is the literal U9 switched-label source. The order branches are
disjoint as LABELS, not as product values: a repeated physical product
in different original labels is deliberately counted more than once.

The original source membership proves product < N. Thus no divisor of
the full shift N-product is zero. The exact finite Fubini identity
retains the coprime correction; density is NOT substituted for it.
The result neither supplies an analytic saving nor identifies this
parameter rho with the full physical sieve compiler's rho_N.
-/

namespace ImbalancedChen.P3ActualU9PhysicalOffshift

noncomputable section
open scoped BigOperators
open Classical

/-- Literal membership of a marked U9 order branch proves that the
entire three-prime physical product is strictly less than N. -/
theorem actual_u9_order_product_lt {N : ℕ} {j : Fin 3}
    {t : P5zU9Triple} (ht : t ∈ p5z_u9_orderBranch j N) :
    p5z_u9_product t < N := by
  exact (p5z_u9_order_source_data (Finset.mem_filter.mp ht).1).2.2.2.1

/-- The shift is a genuinely positive natural number on the actual
source, not a formal subtraction that may truncate or equal zero. -/
theorem actual_u9_order_shift_pos {N : ℕ} {j : Fin 3}
    {t : P5zU9Triple} (ht : t ∈ p5z_u9_orderBranch j N) :
    0 < N - p5z_u9_product t := by
  have h := actual_u9_order_product_lt ht
  omega

/-- Even after the original order permutation, a nonzero physical
rank-three coefficient cannot have complete product N. -/
theorem actual_u9_physical_weight_shift_pos {N : ℕ} {j : Fin 3}
    {u : Fin 3 → Fin (N + 1)}
    (hu : p5z_u9_orderedPhysicalWeight j N u ≠ 0) :
    0 < N - Part3.labelledProduct u := by
  have hs := p5z_u9_orderedPhysicalWeight_support hu
  have h := actual_u9_order_product_lt (j := j) hs
  rw [p5z_u9_physicalInverse_product j u] at h
  omega

/-- All three actual marked order branches have empty complete-product=N
fibres. This is source support, not an exceptional-mass estimate. -/
theorem actual_u9_order_no_diagonal (N : ℕ) (j : Fin 3) :
    (p5z_u9_orderBranch j N).filter
        (fun t => p5z_u9_product t = N) = ∅ := by
  ext t
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ht
  exact (ne_of_lt (actual_u9_order_product_lt ht.1)) ht.2

/-- The UNION of all actual U9 marked labels also has no exact
complete-product=N exception, including equal terminal prime slots. -/
theorem actual_u9_original_no_diagonal (N : ℕ) :
    (p5z_u9_switchedLabels N).filter
        (fun t => p5z_u9_product t = N) = ∅ := by
  ext t
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ht
  exact (ne_of_lt
    ((p5z_u9_order_source_data ht.1).2.2.2.1)) ht.2

/-- Exact full-modulus off-shift expression of ONE actual U9 order branch.
Both the density and the correction carry the SAME signed physical rho. -/
def actualU9OrderOffshift (j : Fin 3) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
    (∑ t ∈ p5z_u9_orderBranch j N,
      physicalDivisorSum Q rho (N - p5z_u9_product t)) -
    p5z_labelledMass (p5z_u9_orderBranch j N) (fun _ => (1 : ℝ)) *
      physicalDensitySum Q rho -
    p5z_labelledCoprimeCorrection
      (p5z_u9_orderBranch j N) p5z_u9_product
      (fun _ => (1 : ℝ)) Q rho

/-- Literal finite source identity: original q congruence mass minus the
exact coprime mean equals nonzero full-shift divisor mass minus original
source density and coprime correction. No PP estimate is a premise. -/
theorem actual_u9_order_same_rho_offshift
    (j : Fin 3) (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5z_u9_orderBranch j N)
      p5z_u9_product (fun _ => (1 : ℝ)) N Q rho =
      actualU9OrderOffshift j N Q rho := by
  have h := p5z_labelled_physical_sum_eq_main_add_errors
    (p5z_u9_orderBranch j N) p5z_u9_product
    (fun _ => (1 : ℝ)) N Q rho
    (by
      intro t ht
      exact (actual_u9_order_product_lt ht).le)
  simp only [one_mul] at h
  unfold actualU9OrderOffshift
  linarith only [h]

/-- THE actual switched U9 marked source with all three order labels:
sum the real physical signed modulus discrepancies before taking a norm.
The three exact coprime corrections are not collapsed into total mass. -/
theorem actual_u9_switched_same_rho_offshift
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5z_u9_switchedLabels N)
        p5z_u9_product (fun _ => (1 : ℝ)) N Q rho =
      actualU9OrderOffshift 0 N Q rho +
      actualU9OrderOffshift 1 N Q rho +
      actualU9OrderOffshift 2 N Q rho := by
  rw [p5z_u9_orderBranches_distribution]
  rw [actual_u9_order_same_rho_offshift 0,
      actual_u9_order_same_rho_offshift 1,
      actual_u9_order_same_rho_offshift 2]

/-- The SAME equality expressed on the three concrete ordered
rank-three Part3 physical PP coefficients, not abstract mark placeholders.
No per-branch norm, extra multiplicity quotient, or second rho is used. -/
theorem actual_u9_physical_three_PP_same_rho_offshift
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho
        (p5z_u9_orderedPhysicalWeight 0 N) +
      Part3.primeProductSignedError 3 N N Q rho
        (p5z_u9_orderedPhysicalWeight 1 N) +
      Part3.primeProductSignedError 3 N N Q rho
        (p5z_u9_orderedPhysicalWeight 2 N) =
      actualU9OrderOffshift 0 N Q rho +
      actualU9OrderOffshift 1 N Q rho +
      actualU9OrderOffshift 2 N Q rho := by
  rw [← p5z_u9_orderedPhysicalPP_decomposition N Q rho]
  exact actual_u9_switched_same_rho_offshift N Q rho

end
end ImbalancedChen.P3ActualU9PhysicalOffshift
