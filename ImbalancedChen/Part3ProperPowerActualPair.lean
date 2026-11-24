import ImbalancedChen.Part3ProperPowerChartSum
import ImbalancedChen.P4BSmoothPrimeVariableProfile

/-!
# Proper-power deletion for the actual smooth ordered pair source

This module applies the full original-chart theorem to the literal P4B smooth physical pair
weight. The real-coordinate support theorems apply to every effective
von Mangoldt tuple, including proper powers; no prime-only support is
used for the integer source. The amplitude is bounded by one.

The original signed rho, exact coprime mean, and complete-product diagonal
are unchanged. The physical modulus cap and fixed divisor-order rho bound
remain explicit inputs. No choice of an actual retention policy, spectral
estimate, or new smooth-family construction is made here.
-/

namespace ImbalancedChen.Part3.ProperPowerActualPair

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open ImbalancedChen.P4B

private theorem effective_primeTuplePoint_positive {N : ℕ}
    {W : (Fin 2 → Fin (N + 1)) → ℝ} {t : Fin 2 → Fin (N + 1)}
    (ht : W t * labelledVonMangoldtWeight t ≠ 0) :
    primeTuplePoint N t ∈ positivePrimeOrthant := by
  have hprod : labelledProduct t ≠ 0 := by
    intro hzero
    apply ht
    rw [labelledVonMangoldtWeight_eq_zero_of_product_eq_zero t hzero, mul_zero]
  intro i
  change (0 : ℝ) < ((t i).val : ℝ)
  exact_mod_cast Nat.pos_of_ne_zero
    ((Finset.prod_ne_zero_iff.mp hprod) i (mem_univ i))

/-- Actual integer-source geometry, rather than geometry restricted to
the prime carrier. The source amplitude is supplied independently below. -/
theorem smoothPair_effective_geometry
    {b κ width a : ℝ} {N : ℕ} (hb : 0 < b) (ha : 0 < a)
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (hgap : 2 * width ≤ P4BOuterRampRoughness.baseline b κ - a)
    (t : Fin 2 → Fin (N + 1))
    (ht : smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width t *
      labelledVonMangoldtWeight t ≠ 0) :
    (∀ i, (1 : ℝ) * (N : ℝ) ^ a ≤ ((t i).val : ℝ)) ∧
      (labelledProduct t : ℝ) ≤ Real.exp width * N := by
  have hp := effective_primeTuplePoint_positive ht
  have hW : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff κ N)
      width (primeTuplePoint N t) ≠ 0 := by
    simpa only [← smoothPhysicalPairOuterRamp_eq_primeVariableProfile] using
      (mul_ne_zero_iff.mp ht).1
  have hlow := smoothPrimeVariableProfile_nonzero_above_rpow
    hb ha hN hwidth hgap hp hW
  have hNreal : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hprod := smoothPrimeVariableProfile_nonzero_product_lt_exp_mul_N
    hNreal hwidth hp hW
  constructor
  · intro i
    simpa only [one_mul, primeTuplePoint] using (hlow i).le
  · simpa only [labelledProduct, Fin.prod_univ_two, Nat.cast_mul, primeTuplePoint]
      using hprod.le

private theorem smoothPair_amplitude (b κ width : ℝ) (N : ℕ)
    (t : Fin 2 → Fin (N + 1)) :
    |smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width t| ≤
      (1 : ℝ) * Real.log (N : ℝ) ^ (0 : ℕ) := by
  obtain ⟨hzero, hone⟩ := smoothPhysicalPairOuterRamp_bounds
    b N (manuscriptHalfProductCutoff κ N) width t
  simpa only [pow_zero, mul_one, abs_of_nonneg hzero] using hone

/-- The same literal source has the required finite prime-product carrier. -/
theorem smoothPair_prime_support {b κ width : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hwidth : 0 < width)
    (t : Fin 2 → Fin (N + 1)) (ht : t ∈ labelledPrimeTuples 2 N)
    (hW : smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width t ≠ 0) :
    labelledProduct t ∈ Icc 1 (Nat.ceil (Real.exp width * (N : ℝ))) := by
  have hp := primeTuplePoint_mem_positivePrimeOrthant ht
  have hNreal : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hWprofile : smoothPrimeVariableProfile b N (manuscriptHalfProductCutoff κ N)
      width (primeTuplePoint N t) ≠ 0 := by
    simpa only [← smoothPhysicalPairOuterRamp_eq_primeVariableProfile] using hW
  have hprod := smoothPrimeVariableProfile_nonzero_product_lt_exp_mul_N
    hNreal hwidth hp hWprofile
  have hcap : (labelledProduct t : ℝ) ≤ Real.exp width * (N : ℝ) := by
    simpa only [labelledProduct, Fin.prod_univ_two, Nat.cast_mul, primeTuplePoint]
      using hprod.le
  apply mem_Icc.mpr
  constructor
  · have hpositive : 0 < labelledProduct t := by
      unfold labelledProduct
      apply Finset.prod_pos
      intro i _
      have hi : (0 : ℝ) < ((t i).val : ℝ) := hp i
      exact_mod_cast hi
    exact Nat.succ_le_iff.mpr hpositive
  · exact_mod_cast hcap.trans (Nat.le_ceil (Real.exp width * (N : ℝ)))

/-- Every logarithmic saving for the actual smooth pair's proper-power
residual. Its weight, geometry, and amplitude are fully instantiated. -/
theorem eventually_smoothPair_properPower_logAccuracy
    (J : ℕ) {b κ width a K Cρ θ : ℝ}
    (hb : 0 < b) (ha : 0 < a) (hwidth : 0 < width)
    (hgap : 2 * width ≤ P4BOuterRampRoughness.baseline b κ - a)
    (hK : 0 < K) (hCρ : 0 < Cρ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ B Q : Finset ℕ, ∀ ρ : ℕ → ℂ, ∀ χ : ℝ → ℝ,
      B ⊆ Icc 1 (Nat.ceil (Real.exp width * (N : ℝ))) →
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      ‖finiteProductSignedError B Q N ρ
        (labelledProperPowerResidual 2 N
          (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width))‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  have hBase := ProperPowerChartSum.eventually_labelledProperPowerResidual_logAccuracy
    (M := 1) (C := Real.exp width) (c := 1) (K := K) (Cρ := Cρ) (a := a) (θ := θ)
    2 J 0 (by norm_num) (Real.exp_pos width) (by norm_num)
    hK hCρ ha hθ0 hθ1 A ε hε
  filter_upwards [hBase, eventually_ge_atTop (2 : ℕ)] with N hBaseN hN
  intro B Q ρ χ hB hQ hρ χlo χhi χrange
  exact hBaseN N B Q ρ
    (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width)
    χ hB hQ hρ χlo χhi χrange (smoothPair_amplitude b κ width N)
    (smoothPair_effective_geometry hb ha hN hwidth hgap)

/-- Prime-minus-VM error for the actual smooth pair, with its full physical
product carrier and the same signed real rho in both discrepancies. -/
theorem eventually_smoothPair_prime_sub_vonMangoldt_logAccuracy
    (J : ℕ) {b κ width a K Cρ θ : ℝ}
    (hb : 0 < b) (ha : 0 < a) (hwidth : 0 < width)
    (hgap : 2 * width ≤ P4BOuterRampRoughness.baseline b κ - a)
    (hK : 0 < K) (hCρ : 0 < Cρ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : Finset ℕ, ∀ ρ : ℕ → ℝ, ∀ χ : ℝ → ℝ,
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, |ρ q| ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      ‖(primeProductSignedError 2 N N Q ρ
          (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width) : ℂ) -
        finiteProductSignedError (Icc 1 (Nat.ceil (Real.exp width * (N : ℝ)))) Q N
          (fun q => (ρ q : ℂ))
          (labelledVonMangoldtProductMass 2 N
            (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width))‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_smoothPair_properPower_logAccuracy
    J hb ha hwidth hgap hK hCρ hθ0 hθ1 A ε hε,
    eventually_ge_atTop (2 : ℕ)] with N hPay hN
  intro Q ρ χ hQ hρ χlo χhi χrange
  rw [primeProductSignedError_eq_vonMangoldt_sub_properPower 2 N N Q
    (Icc 1 (Nat.ceil (Real.exp width * (N : ℝ)))) ρ
    (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width)
    (smoothPair_prime_support hN hwidth), sub_sub_cancel_left, norm_neg]
  exact hPay _ Q (fun q => (ρ q : ℂ)) χ (by intro q hq; exact hq) hQ
    (fun q hq => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ q hq)
    χlo χhi χrange

end
end ImbalancedChen.Part3.ProperPowerActualPair
