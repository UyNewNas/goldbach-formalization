import ImbalancedChen.P5U7ActualFullComponentMeans

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
Separate physical-product fibre weights for the actual prime and ordered
semiprime branches. Each fibre cardinality retains every marked label;
product injectivity and squarefreeness are not needed. Arbitrary signed
physical tests are transported exactly before component mean limits.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology
open scoped BigOperators
open Classical

def p5U7ActualPrimeProductWeight (N m : ℕ) : ℝ :=
  (((p5U7ArithmeticThree N).filter (fun x => p5U7ThreeProduct x=m)).card : ℝ)

def p5U7ActualSemiprimeProductWeight (N m : ℕ) : ℝ :=
  (((p5U7ArithmeticFour N).filter (fun x => p5U7FourProduct x=m)).card : ℝ)

theorem p5U7ActualPrimeProductWeight_nonneg (N m : ℕ) :
    0 ≤ p5U7ActualPrimeProductWeight N m := Nat.cast_nonneg _

theorem p5U7ActualSemiprimeProductWeight_nonneg (N m : ℕ) :
    0 ≤ p5U7ActualSemiprimeProductWeight N m := Nat.cast_nonneg _

/-- The full source weight is the sum of two actual carrier weights,
not an alternative name for either separate component. -/
theorem p5U7ArithmeticProductWeight_eq_components (N m : ℕ) :
    p5U7ArithmeticProductWeight N m =
      p5U7ActualPrimeProductWeight N m+p5U7ActualSemiprimeProductWeight N m := rfl

/-- Separate signed-test Fubini on actual physical products. -/
theorem p5U7ActualPrimeProductWeight_Fubini (N : ℕ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N,p5U7ActualPrimeProductWeight N m*H m) =
      ∑ x ∈ p5U7ArithmeticThree N,H (p5U7ThreeProduct x) := by
  have hmap : ∀ x ∈ p5U7ArithmeticThree N,p5U7ThreeProduct x ∈ Finset.range N :=
    fun x hx => Finset.mem_range.mpr (p5U7ArithmeticThree_data hx).2.2.2.2.2.2.2.1
  simpa only [p5U7ActualPrimeProductWeight,Finset.sum_const,nsmul_eq_mul] using
    Finset.sum_fiberwise_of_maps_to' hmap H

theorem p5U7ActualSemiprimeProductWeight_Fubini (N : ℕ) (H : ℕ → ℝ) :
    (∑ m ∈ Finset.range N,p5U7ActualSemiprimeProductWeight N m*H m) =
      ∑ x ∈ p5U7ArithmeticFour N,H (p5U7FourProduct x) := by
  have hmap : ∀ x ∈ p5U7ArithmeticFour N,p5U7FourProduct x ∈ Finset.range N :=
    fun x hx => Finset.mem_range.mpr (p5U7ArithmeticFour_data hx).2.2.2.2.2.2.2.2.2.1
  simpa only [p5U7ActualSemiprimeProductWeight,Finset.sum_const,nsmul_eq_mul] using
    Finset.sum_fiberwise_of_maps_to' hmap H

theorem p5U7ActualPrimeProductWeight_mass (N : ℕ) :
    (∑ m ∈ Finset.range N,p5U7ActualPrimeProductWeight N m) =
      ((p5U7ArithmeticThree N).card : ℝ) := by
  simpa only [mul_one,Finset.sum_const,nsmul_eq_mul] using
    p5U7ActualPrimeProductWeight_Fubini N (fun _ => 1)

theorem p5U7ActualSemiprimeProductWeight_mass (N : ℕ) :
    (∑ m ∈ Finset.range N,p5U7ActualSemiprimeProductWeight N m) =
      ((p5U7ArithmeticFour N).card : ℝ) := by
  simpa only [mul_one,Finset.sum_const,nsmul_eq_mul] using
    p5U7ActualSemiprimeProductWeight_Fubini N (fun _ => 1)

/-- A physical congruence may be tested separately on either genuine
branch; this finite identity is not a distribution estimate. -/
theorem p5U7ActualPrimeProductWeight_progression (N d : ℕ) :
    (∑ m ∈ Finset.range N,
      if Nat.ModEq d m N then p5U7ActualPrimeProductWeight N m else 0) =
      ∑ x ∈ p5U7ArithmeticThree N,
        if Nat.ModEq d (p5U7ThreeProduct x) N then (1 : ℝ) else 0 := by
  have h := p5U7ActualPrimeProductWeight_Fubini N
    (fun m => if Nat.ModEq d m N then (1 : ℝ) else 0)
  simpa only [mul_ite,mul_one,mul_zero] using h

theorem p5U7ActualSemiprimeProductWeight_progression (N d : ℕ) :
    (∑ m ∈ Finset.range N,
      if Nat.ModEq d m N then p5U7ActualSemiprimeProductWeight N m else 0) =
      ∑ x ∈ p5U7ArithmeticFour N,
        if Nat.ModEq d (p5U7FourProduct x) N then (1 : ℝ) else 0 := by
  have h := p5U7ActualSemiprimeProductWeight_Fubini N
    (fun m => if Nat.ModEq d m N then (1 : ℝ) else 0)
  simpa only [mul_ite,mul_one,mul_zero] using h

/-- Separate full prime PRODUCT-weight mass limit, with exact marked
fibre multiplicities and the original logarithmic normalization. -/
theorem tendsto_p5U7ActualPrimeProductWeight_mass :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range N,p5U7ActualPrimeProductWeight N m)) atTop
        (𝓝 p5U7ComponentPrimeIntegral) := by
  simpa only [p5U7ActualPrimeProductWeight_mass] using
    tendsto_p5U7ActualFullPrimeMass_normalized

/-- Separate full ordered-semiprime PRODUCT-weight mass limit. Repeated
terminal factors and all product collisions retain their original weight. -/
theorem tendsto_p5U7ActualSemiprimeProductWeight_mass :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      (∑ m ∈ Finset.range N,p5U7ActualSemiprimeProductWeight N m)) atTop
        (𝓝 p5U7ComponentSemiprimeIntegral) := by
  simpa only [p5U7ActualSemiprimeProductWeight_mass] using
    tendsto_p5U7ActualFullSemiprimeMass_normalized

end
end ImbalancedChen
