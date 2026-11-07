import ImbalancedChen.ActualSmallRosser

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A finite arithmetic regime for automatic literal small-prime Rosser gates.
The bound uses the actual target-prime-deleted product, not an assumed
admissibility predicate. Both parity choices are proved simultaneously.
-/

namespace ImbalancedChen.P5Z.PresieveGateRegime

noncomputable section
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- Every actual small prefix divides the actual complete small product. -/
theorem actual_prefix_product_le {N cap e : ℕ} {w : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (p : ℕ) :
    (((e.primeFactors.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) ≤
      (actualSmallPrimeProduct N cap w : ℝ) := by
  have hsf := actualSmallRosserSupport_squarefree N cap w he
  have hdiv := Finset.prod_dvd_prod_of_subset
    (e.primeFactors.filter (fun q => p ≤ q)) e.primeFactors id
    (Finset.filter_subset _ _)
  rw [Nat.prod_primeFactors_of_squarefree hsf] at hdiv
  have hdivM := hdiv.trans (Nat.mem_divisors.mp he).1
  exact_mod_cast Nat.le_of_dvd
    (Nat.pos_of_ne_zero (actualSmallPrimeProduct_ne_zero N cap w)) hdivM

/-- This controls ALL small prefixes, before selecting either parity. -/
theorem actual_prefix_test_of_product_bound {N cap e : ℕ} {w R : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R)
    {p : ℕ} (hp : p ∈ e.primeFactors) :
    (((e.primeFactors.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
      (p : ℝ) ^ 2 < R := by
  have hpw := (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he).2 p hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hp2 : (p : ℝ) ^ 2 ≤ w ^ 2 := by nlinarith
  exact (mul_le_mul (actual_prefix_product_le he p) hp2
    (sq_nonneg (p : ℝ)) (Nat.cast_nonneg _)).trans_lt hbound

/-- The same arithmetic bound also supplies the strict total-product cutoff. -/
theorem actual_small_cutoff_of_product_bound {N cap e : ℕ} {w R : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R) :
    (e : ℝ) < R := by
  have heM : e ≤ actualSmallPrimeProduct N cap w := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (actualSmallPrimeProduct_ne_zero N cap w))
    (Nat.mem_divisors.mp he).1
  have heMR : (e : ℝ) ≤ (actualSmallPrimeProduct N cap w : ℝ) := by exact_mod_cast heM
  have hM0 : (0 : ℝ) ≤ actualSmallPrimeProduct N cap w := Nat.cast_nonneg _
  have hw2 : (1 : ℝ) ≤ w ^ 2 := by nlinarith
  have hM : (actualSmallPrimeProduct N cap w : ℝ) ≤
      (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 := by nlinarith
  exact heMR.trans_lt (hM.trans_lt hbound)

/-- Genuine product-size input discharges both literal Rosser gate systems. -/
theorem actual_both_admissible_of_product_bound {N cap e : ℕ} {w R : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R) :
    UpperAdmissibleSet R e.primeFactors ∧ LowerAdmissibleSet R e.primeFactors := by
  constructor
  all_goals
    intro p hp _hparity
    exact actual_prefix_test_of_product_bound he hw hbound hp

/-- On this explicit regime both actual small coefficients are the full
squarefree Mobius sign. In particular their value is independent of the
rough parity, including the empty small factor e=1. -/
theorem actual_small_signs_of_product_bound {N cap e : ℕ} {w R : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R) :
    actualSmallRosserPlus N cap w R e = (-1 : ℝ) ^ e.primeFactors.card ∧
      actualSmallRosserMinus N cap w R e = (-1 : ℝ) ^ e.primeFactors.card := by
  have hcut := actual_small_cutoff_of_product_bound he hw hbound
  have hadm := actual_both_admissible_of_product_bound he hw hbound
  constructor
  · change upperWeight (actualSmallPrimeProduct N cap w) R e = _
    rw [upperWeight_apply, if_pos ⟨he, hcut, hadm.1⟩]
  · change lowerWeight (actualSmallPrimeProduct N cap w) R e = _
    rw [lowerWeight_apply, if_pos ⟨he, hcut, hadm.2⟩]

/-- Exact residual version, with the actual rough product d in the bound.
No target gate or factorization assertion is an input. -/
theorem actual_residual_small_signs {N cap e d : ℕ} {w L : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hd : 0 < d) (hw : 1 ≤ w)
    (hbound : (d : ℝ) * (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < L) :
    actualSmallRosserPlus N cap w (L / (d : ℝ)) e = (-1 : ℝ) ^ e.primeFactors.card ∧
      actualSmallRosserMinus N cap w (L / (d : ℝ)) e = (-1 : ℝ) ^ e.primeFactors.card := by
  apply actual_small_signs_of_product_bound he hw
  apply (lt_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
  nlinarith only [hbound]

end
end ImbalancedChen.P5Z.PresieveGateRegime
