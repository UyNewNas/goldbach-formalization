import ImbalancedChen.P5PresieveAutomaticPrefixGates
import ImbalancedChen.P4APhysicalMoebiusLookup
import ImbalancedChen.ActualSmallRosserDensity

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Exact Mobius and Euler behavior in the proved automatic-prefix regime.
The preexisting actual-weight/Mobius lookup and multiplicative Euler
identity are reused. No density asymptotic or fixed-beta premise occurs.
-/

namespace ImbalancedChen.P5Z.PresieveGateRegime

noncomputable section
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuPrereqWF
open P4APhysicalMoebiusLookup

/-- Both actual coefficients equal Mobius on the entire actual small carrier. -/
theorem actual_small_moebius_of_product_bound {N cap e : ℕ} {w R : ℝ}
    (he : e ∈ actualSmallRosserSupport N cap w) (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R) :
    actualSmallRosserPlus N cap w R e = (ArithmeticFunction.moebius e : ℝ) ∧
      actualSmallRosserMinus N cap w R e = (ArithmeticFunction.moebius e : ℝ) := by
  have hs := actual_small_signs_of_product_bound he hw hbound
  have hsign : (-1 : ℝ) ^ e.primeFactors.card ≠ 0 := pow_ne_zero _ (by norm_num)
  exact ⟨actualPlus_eq_moebius_of_ne_zero N cap w R (by rw [hs.1]; exact hsign),
    actualMinus_eq_moebius_of_ne_zero N cap w R (by rw [hs.2]; exact hsign)⟩

/-- Exact Euler evaluation for any multiplicative local arithmetic density.
It holds for both parity choices, with the actual excluded-prime carrier. -/
theorem actual_small_euler_pair_of_product_bound {N cap : ℕ} {w R : ℝ}
    (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R)
    (g : ArithmeticFunction ℝ) (hg : g.IsMultiplicative) :
    (∑ e ∈ actualSmallRosserSupport N cap w, actualSmallRosserPlus N cap w R e * g e) =
      (∏ p ∈ actualSmallPrimeFinset N cap w, (1 - g p)) ∧
    (∑ e ∈ actualSmallRosserSupport N cap w, actualSmallRosserMinus N cap w R e * g e) =
      (∏ p ∈ actualSmallPrimeFinset N cap w, (1 - g p)) := by
  have hEuler := ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    g hg (actualSmallPrimeProduct_squarefree N cap w)
  rw [actualSmallPrimeProduct_primeFactors] at hEuler
  constructor
  · calc
      _ = ∑ e ∈ actualSmallRosserSupport N cap w, (ArithmeticFunction.moebius e : ℝ) * g e := by
        apply Finset.sum_congr rfl
        intro e he
        rw [(actual_small_moebius_of_product_bound he hw hbound).1]
      _ = _ := hEuler.symm
  · calc
      _ = ∑ e ∈ actualSmallRosserSupport N cap w, (ArithmeticFunction.moebius e : ℝ) * g e := by
        apply Finset.sum_congr rfl
        intro e he
        rw [(actual_small_moebius_of_product_bound he hw hbound).2]
      _ = _ := hEuler.symm

/-- In particular both actual reciprocal-totient densities are EXACTLY the
actual Euler factor, without an error term or an even-target hypothesis. -/
theorem actual_small_totient_pair_of_product_bound {N cap : ℕ} {w R : ℝ}
    (hw : 1 ≤ w)
    (hbound : (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < R) :
    actualSmallRosserPlusDensity N cap w R = actualSmallEulerProduct N cap w ∧
      actualSmallRosserMinusDensity N cap w R = actualSmallEulerProduct N cap w := by
  have h := actual_small_euler_pair_of_product_bound hw hbound
    (primeDensity (progressionOmega N))
    (primeDensity_isMultiplicative (progressionOmega_isMultiplicative N))
  simp only [primeDensity_apply, actualSmallRosserSupport_sourceDensity_eq,
    actualSmallEulerProduct_eq_source] at h
  exact h

/-- The exact same Euler factor works at every residual rough state d
whose numerical product-size budget holds; rough parity is immaterial. -/
theorem actual_residual_totient_pair {N cap d : ℕ} {w L : ℝ}
    (hd : 0 < d) (hw : 1 ≤ w)
    (hbound : (d : ℝ) * (actualSmallPrimeProduct N cap w : ℝ) * w ^ 2 < L) :
    actualSmallRosserPlusDensity N cap w (L / (d : ℝ)) = actualSmallEulerProduct N cap w ∧
      actualSmallRosserMinusDensity N cap w (L / (d : ℝ)) = actualSmallEulerProduct N cap w := by
  apply actual_small_totient_pair_of_product_bound hw
  apply (lt_div_iff₀ (show (0 : ℝ) < d by exact_mod_cast hd)).mpr
  nlinarith only [hbound]

end
end ImbalancedChen.P5Z.PresieveGateRegime

