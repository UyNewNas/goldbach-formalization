import ImbalancedChen.CurrentChenUpsilon8SharpKPhysicalPP
import Mathlib.Tactic

/-!
P3.6 | The *actual* U8 sharp-K prime-quotient source, with its inclusive
terminal-prime wall, original labelled multiplicity, and one physical rho.
SOURCE_ONLY / NOT LEAN COMPILED / KERNEL_UNVERIFIED.

The real source is P5U8SharpKSource.arithmeticTriples N. Its ordered
p1 < p2 <= q is inclusive at q=p2; that diagonal cannot be silently
discarded. The external additive-prime test is NOT put into these
coefficients. The real U8 unit-quotient fibres are a separate summand
(currentChenUpsilon8_eq_primeMass_add_units).

All congruence, divisor and exact coprime means use the full physical
product p1*p2*q and the identical signed physical Q,rho. This is only
finite manuscript-internal arithmetic, not a logarithmic PP saving or
the all-marked/HB atom compiler; rho_T/Q_T are not identified here.
-/

namespace ImbalancedChen.P3ActualU8SharpKOffshift

noncomputable section
open scoped BigOperators
open Classical
open ImbalancedChen.P5U8SharpKSource

/-- The genuine U8 sharp-K arithmetic family forces its complete
three-prime product strictly below the physical target. -/
theorem actual_u8_full_product_lt {N : ℕ} {t : Triple}
    (ht : t ∈ arithmeticTriples N) : product t < N :=
  arithmetic_product_lt ht

/-- No natural subtraction is truncated at zero on this actual source. -/
theorem actual_u8_shift_pos {N : ℕ} {t : Triple}
    (ht : t ∈ arithmeticTriples N) :
    0 < N - product t := by
  have h := actual_u8_full_product_lt ht
  omega

/-- The full-product=N exceptional fibre is empty for this actual U8
prime-quotient family. This does NOT eliminate its unit-quotient part. -/
theorem actual_u8_full_diagonal_empty (N : ℕ) :
    (arithmeticTriples N).filter (fun t => product t = N) = ∅ := by
  ext t
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false]
  intro ht
  exact (ne_of_lt (actual_u8_full_product_lt ht.1)) ht.2

/-- The inclusive q=p₂ terminal-prime diagonal and strict p₂<q
partition the *literal labelled* U8 source, not its product image. -/
theorem actual_u8_source_partition (N : ℕ) :
    arithmeticTriples N = strictTriples N ∪ diagonalTriples N := by
  ext t
  constructor
  · intro ht
    have hsorted := (arithmetic_sorted ht).2
    by_cases heq : t.2 = t.1.2
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_filter.mpr ⟨ht, heq⟩))
    · have hlt : t.1.2 < t.2 := by omega
      exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨ht, hlt⟩))
  · intro ht
    rcases Finset.mem_union.mp ht with hs | hd
    · exact (Finset.mem_filter.mp hs).1
    · exact (Finset.mem_filter.mp hd).1

theorem actual_u8_source_partition_disjoint (N : ℕ) :
    Disjoint (strictTriples N) (diagonalTriples N) := by
  apply Finset.disjoint_left.mpr
  intro t hs hd
  have hlt := (Finset.mem_filter.mp hs).2
  have heq := (Finset.mem_filter.mp hd).2
  omega

/-- No repeated product is deduplicated, even when distinct source
tuples happen to have the same complete product. -/
theorem actual_u8_sum_partition (N : ℕ) (F : Triple → ℝ) :
    (∑ t ∈ arithmeticTriples N, F t) =
      (∑ t ∈ strictTriples N, F t) +
      (∑ t ∈ diagonalTriples N, F t) := by
  rw [actual_u8_source_partition N]
  exact Finset.sum_union (actual_u8_source_partition_disjoint N)

/-- In particular the FULL physical signed modulus discrepancy splits
before taking an absolute value. The terminal-prime diagonal is present
with its original exact coprime mean and original multiplicity. -/
theorem actual_u8_distribution_partition (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (arithmeticTriples N) product
        (fun _ => (1 : ℝ)) N Q rho =
      p5z_labelledDistributionError (strictTriples N) product
        (fun _ => (1 : ℝ)) N Q rho +
      p5z_labelledDistributionError (diagonalTriples N) product
        (fun _ => (1 : ℝ)) N Q rho := by
  have hcong (q : ℕ) :
      p5z_labelledCongruenceMass (arithmeticTriples N) product
          (fun _ => (1 : ℝ)) N q =
        p5z_labelledCongruenceMass (strictTriples N) product
          (fun _ => (1 : ℝ)) N q +
        p5z_labelledCongruenceMass (diagonalTriples N) product
          (fun _ => (1 : ℝ)) N q := by
    simpa only [p5z_labelledCongruenceMass] using
      (actual_u8_sum_partition N
        (fun t => if Nat.ModEq q (product t) N then (1 : ℝ) else 0))
  have hcop (q : ℕ) :
      p5z_labelledCoprimeMass (arithmeticTriples N) product
          (fun _ => (1 : ℝ)) q =
        p5z_labelledCoprimeMass (strictTriples N) product
          (fun _ => (1 : ℝ)) q +
        p5z_labelledCoprimeMass (diagonalTriples N) product
          (fun _ => (1 : ℝ)) q := by
    simpa only [p5z_labelledCoprimeMass] using
      (actual_u8_sum_partition N
        (fun t => if Nat.Coprime (product t) q then (1 : ℝ) else 0))
  unfold p5z_labelledDistributionError
  simp_rw [hcong, hcop]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- The existing original U8 inclusive-terminal family, not a generic
surrogate atom, has its exact finite offshift expression. -/
def actualU8SharpKOffshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  (∑ t ∈ arithmeticTriples N,
    physicalDivisorSum Q rho (N - product t)) -
  p5z_labelledMass (arithmeticTriples N) (fun _ => (1 : ℝ)) *
    physicalDensitySum Q rho -
  p5z_labelledCoprimeCorrection
    (arithmeticTriples N) product (fun _ => (1 : ℝ)) Q rho

/-- Original congruence count minus exact coprime mean equals the
literal complete-product divisor mass after full physical q-summation,
with the exact signed coprime correction retained. -/
theorem actual_u8_same_rho_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (arithmeticTriples N) product
        (fun _ => (1 : ℝ)) N Q rho =
      actualU8SharpKOffshift N Q rho := by
  have h := p5z_labelled_physical_sum_eq_main_add_errors
    (arithmeticTriples N) product (fun _ => (1 : ℝ)) N Q rho
    (by
      intro t ht
      exact (actual_u8_full_product_lt ht).le)
  simp only [one_mul] at h
  unfold actualU8SharpKOffshift
  linarith only [h]

/-- The repeated q=p₂ diagonal has the SAME nonzero full shift and
an exact, unmodified coprime correction, rather than being thrown away
as a supposed measure-zero boundary. -/
theorem actual_u8_terminal_diagonal_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (diagonalTriples N) product
        (fun _ => (1 : ℝ)) N Q rho =
      (∑ t ∈ diagonalTriples N,
        physicalDivisorSum Q rho (N - product t)) -
      p5z_labelledMass (diagonalTriples N) (fun _ => (1 : ℝ)) *
        physicalDensitySum Q rho -
      p5z_labelledCoprimeCorrection
        (diagonalTriples N) product (fun _ => (1 : ℝ)) Q rho := by
  have h := p5z_labelled_physical_sum_eq_main_add_errors
    (diagonalTriples N) product (fun _ => (1 : ℝ)) N Q rho
    (by
      intro t ht
      exact (actual_u8_full_product_lt (Finset.mem_filter.mp ht).1).le)
  simp only [one_mul] at h
  linarith only [h]

/-- Exact original physical rank-three PP target. Source multiplicity,
inclusive terminal q=p₂, centre coprimality and sharp-K square-root
gate remain in physicalWeight. rho is the same physical coefficient. -/
theorem actual_u8_physical_PP_same_rho_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    Part3.primeProductSignedError 3 N N Q rho (physicalWeight N) =
      actualU8SharpKOffshift N Q rho := by
  rw [← distribution_eq_physicalPP N Q rho]
  exact actual_u8_same_rho_offshift N Q rho

/-- The actual value-level coefficient counts all ORIGINAL prime
tuples over each product, without identifying equal-product labels. -/
theorem actual_u8_productWeight_same_rho_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (Finset.range N) id
        (productWeight N) N Q rho =
      actualU8SharpKOffshift N Q rho := by
  rw [productWeight_distribution_eq_labels N Q rho]
  exact actual_u8_same_rho_offshift N Q rho

/-- A single signed physical rho covers strict and repeated-terminal
parts simultaneously; no separate per-branch estimate or norm occurs. -/
theorem actual_u8_strict_diagonal_same_rho_offshift (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (strictTriples N) product
        (fun _ => (1 : ℝ)) N Q rho +
      p5z_labelledDistributionError (diagonalTriples N) product
        (fun _ => (1 : ℝ)) N Q rho =
      actualU8SharpKOffshift N Q rho := by
  rw [← actual_u8_distribution_partition N Q rho]
  exact actual_u8_same_rho_offshift N Q rho

end
end ImbalancedChen.P3ActualU8SharpKOffshift
