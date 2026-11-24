import ImbalancedChen.Part3ProperPowerActualPair

/-!
# Uniform proper-power deletion for actual smooth pair families

The fixed-precision ordered-pair argument already admits a fixed smoothing width.
This module retains the stronger quantifier order needed when the P3 source is a
family W_N: a common threshold works for every positive width at most widthMax.
The complete-product carrier is always Icc 1 (ceil (exp(widthMax) * N)).

The proof uses the original-chart theorem's uniformity in the weight and the
existing geometry of every effective integer tuple. It does not interchange
separate fixed-width eventual statements. The original signed rho, exact coprime
mean, and complete-product diagonal are preserved.

This result concerns proper-power deletion. A varying width still needs the
manuscript's polylogarithmic Euler-derivative bounds before the remaining HB and
spectral steps can be applied to its smooth family.
-/

namespace ImbalancedChen.Part3.ProperPowerActualPairFamily

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open ImbalancedChen.P4B ProperPowerActualPair

/-- Every smaller positive width has the same integer-source roughness and
complete-product cap. The nonzero condition includes the VM coefficient. -/
theorem smoothPair_effective_geometry_uniformWidth
    {b κ width widthMax a : ℝ} {N : ℕ} (hb : 0 < b) (ha : 0 < a)
    (hN : 2 ≤ N) (hwidth : 0 < width) (hwidth_le : width ≤ widthMax)
    (hgap : 2 * widthMax ≤ P4BOuterRampRoughness.baseline b κ - a)
    (t : Fin 2 → Fin (N + 1))
    (ht : smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width t *
      labelledVonMangoldtWeight t ≠ 0) :
    (∀ i, (1 : ℝ) * (N : ℝ) ^ a ≤ ((t i).val : ℝ)) ∧
      (labelledProduct t : ℝ) ≤ Real.exp widthMax * N := by
  have hgapWidth : 2 * width ≤ P4BOuterRampRoughness.baseline b κ - a :=
    (mul_le_mul_of_nonneg_left hwidth_le (by norm_num : (0 : ℝ) ≤ 2)).trans hgap
  obtain ⟨hlow, hproduct⟩ :=
    smoothPair_effective_geometry hb ha hN hwidth hgapWidth t ht
  exact ⟨hlow, hproduct.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hwidth_le) (Nat.cast_nonneg N))⟩

/-- The finite prime carrier may be chosen once for the whole width interval. -/
theorem smoothPair_prime_support_uniformWidth {b κ width widthMax : ℝ} {N : ℕ}
    (hN : 2 ≤ N) (hwidth : 0 < width) (hwidth_le : width ≤ widthMax)
    (t : Fin 2 → Fin (N + 1)) (ht : t ∈ labelledPrimeTuples 2 N)
    (hW : smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width t ≠ 0) :
    labelledProduct t ∈ Icc 1 (Nat.ceil (Real.exp widthMax * (N : ℝ))) := by
  have hs := mem_Icc.mp (smoothPair_prime_support hN hwidth t ht hW)
  refine mem_Icc.mpr ⟨hs.1, hs.2.trans ?_⟩
  exact Nat.ceil_mono
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hwidth_le) (Nat.cast_nonneg N))

/-- A single threshold precedes the width, finite carriers, signed coefficient,
and cutoff. No geometry or amplitude assumption on the actual source remains. -/
theorem eventually_smoothPair_uniformWidth_properPower_logAccuracy
    (J : ℕ) {b κ widthMax a K Cρ θ : ℝ}
    (hb : 0 < b) (ha : 0 < a)
    (hgap : 2 * widthMax ≤ P4BOuterRampRoughness.baseline b κ - a)
    (hK : 0 < K) (hCρ : 0 < Cρ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, 0 < width → width ≤ widthMax →
      ∀ B Q : Finset ℕ, ∀ ρ : ℕ → ℂ, ∀ χ : ℝ → ℝ,
      B ⊆ Icc 1 (Nat.ceil (Real.exp widthMax * (N : ℝ))) →
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      ‖finiteProductSignedError B Q N ρ
        (labelledProperPowerResidual 2 N
          (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width))‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  have hBase := ProperPowerChartSum.eventually_labelledProperPowerResidual_logAccuracy
    (M := 1) (C := Real.exp widthMax) (c := 1) (K := K) (Cρ := Cρ) (a := a) (θ := θ)
    2 J 0 (by norm_num) (Real.exp_pos widthMax) (by norm_num)
    hK hCρ ha hθ0 hθ1 A ε hε
  filter_upwards [hBase, eventually_ge_atTop (2 : ℕ)] with N hBaseN hN
  intro width hwidth hwidth_le B Q ρ χ hB hQ hρ χlo χhi χrange
  apply hBaseN N B Q ρ
    (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width)
    χ hB hQ hρ χlo χhi χrange
  · intro t
    obtain ⟨hzero, hone⟩ := smoothPhysicalPairOuterRamp_bounds
      b N (manuscriptHalfProductCutoff κ N) width t
    simpa only [pow_zero, mul_one, abs_of_nonneg hzero] using hone
  · exact smoothPair_effective_geometry_uniformWidth hb ha hN hwidth hwidth_le hgap

/-- Uniform prime-minus-VM error on the same complete-product carrier for
every admitted width, with the same signed real rho in both discrepancies. -/
theorem eventually_smoothPair_uniformWidth_prime_sub_vonMangoldt_logAccuracy
    (J : ℕ) {b κ widthMax a K Cρ θ : ℝ}
    (hb : 0 < b) (ha : 0 < a)
    (hgap : 2 * widthMax ≤ P4BOuterRampRoughness.baseline b κ - a)
    (hK : 0 < K) (hCρ : 0 < Cρ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ width : ℝ, 0 < width → width ≤ widthMax →
      ∀ Q : Finset ℕ, ∀ ρ : ℕ → ℝ, ∀ χ : ℝ → ℝ,
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, |ρ q| ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      ‖(primeProductSignedError 2 N N Q ρ
          (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width) : ℂ) -
        finiteProductSignedError (Icc 1 (Nat.ceil (Real.exp widthMax * (N : ℝ)))) Q N
          (fun q => (ρ q : ℂ))
          (labelledVonMangoldtProductMass 2 N
            (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width))‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_smoothPair_uniformWidth_properPower_logAccuracy
    J hb ha hgap hK hCρ hθ0 hθ1 A ε hε,
    eventually_ge_atTop (2 : ℕ)] with N hPay hN
  intro width hwidth hwidth_le Q ρ χ hQ hρ χlo χhi χrange
  rw [primeProductSignedError_eq_vonMangoldt_sub_properPower 2 N N Q
    (Icc 1 (Nat.ceil (Real.exp widthMax * (N : ℝ)))) ρ
    (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N) width)
    (smoothPair_prime_support_uniformWidth hN hwidth hwidth_le),
    sub_sub_cancel_left, norm_neg]
  exact hPay width hwidth hwidth_le _ Q (fun q => (ρ q : ℂ)) χ
    (by intro q hq; exact hq) hQ
    (fun q hq => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ q hq)
    χlo χhi χrange

/-- Direct specialization to an N-dependent width. The only extra threshold
comes from eventual membership of the width in the fixed interval. -/
theorem eventually_smoothPair_varyingWidth_prime_sub_vonMangoldt_logAccuracy
    (J : ℕ) {b κ widthMax a K Cρ θ : ℝ}
    (hb : 0 < b) (ha : 0 < a)
    (hgap : 2 * widthMax ≤ P4BOuterRampRoughness.baseline b κ - a)
    (hK : 0 < K) (hCρ : 0 < Cρ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) (width : ℕ → ℝ)
    (hwidth : ∀ᶠ N : ℕ in atTop, 0 < width N ∧ width N ≤ widthMax) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : Finset ℕ, ∀ ρ : ℕ → ℝ, ∀ χ : ℝ → ℝ,
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, |ρ q| ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      ‖(primeProductSignedError 2 N N Q ρ
          (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N)
            (width N)) : ℂ) -
        finiteProductSignedError (Icc 1 (Nat.ceil (Real.exp widthMax * (N : ℝ)))) Q N
          (fun q => (ρ q : ℂ))
          (labelledVonMangoldtProductMass 2 N
            (smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff κ N)
              (width N)))‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_smoothPair_uniformWidth_prime_sub_vonMangoldt_logAccuracy
    J hb ha hgap hK hCρ hθ0 hθ1 A ε hε, hwidth] with N hPay hwidthN
  exact hPay (width N) hwidthN.1 hwidthN.2

end
end ImbalancedChen.Part3.ProperPowerActualPairFamily
