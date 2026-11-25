import ImbalancedChen.Part3ProperPowerLogSaving

/-!
# Proper-prime-power deletion over the full original chart bank

This closes the chart summation in the proper-power deletion of Appendix
D.3 of the frozen 2026-11-06 manuscript. The original cutoff partition is
applied on the effective integer support `W * labelledVonMangoldtWeight`.
The bank starts at zero and ends at the logarithm of the physical complete
product cap; it does not depend on the modulus or the source carrier.

The exact residual and its same-rho signed discrepancy are reconstructed
before estimating their norms. The existing single-chart theorem is used
with accuracy `A + k`, paying the entire bank cardinality. Its primitive
coprime mean and full-product diagonal remain those of the original error.
All constants and the eventual threshold precede `P`, `B`, `Q`, `rho`,
`W`, and the cutoff. No chart-error estimate or distance-divisor bound is
an assumption.
-/

namespace ImbalancedChen.Part3.ProperPowerChartSum

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology

/-- The upper cutoff includes the next dyadic scale above the physical cap. -/
def originalChartHeight (X : ℝ) : ℕ := Nat.log 2 (Nat.ceil X) + 2

/-- The finite bank of the original labelled coordinate windows. -/
def originalChartBank (k : ℕ) (X : ℝ) : Finset (Fin k → ℕ) :=
  Fintype.piFinset (fun _ : Fin k => range (originalChartHeight X))

theorem originalChartBank_card (k : ℕ) (X : ℝ) :
    (originalChartBank k X).card = originalChartHeight X ^ k := by
  unfold originalChartBank
  rw [Fintype.card_piFinset_const, card_range]

/-- The original tensor partition covers every effective integer tuple,
including proper powers. A zero coordinate has zero von Mangoldt weight. -/
theorem originalDyadicChartWeight_sum_eq_one_of_effective
    {k P : ℕ} (χ : ℝ → ℝ) (W : (Fin k → Fin (P + 1)) → ℝ)
    (t : Fin k → Fin (P + 1)) {X : ℝ}
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (ht : W t * labelledVonMangoldtWeight t ≠ 0)
    (hProduct : (labelledProduct t : ℝ) ≤ X) :
    (∑ j ∈ originalChartBank k X, originalDyadicChartWeight χ 0 j t) = 1 := by
  have hprod0 : labelledProduct t ≠ 0 := by
    intro h
    apply ht
    rw [labelledVonMangoldtWeight_eq_zero_of_product_eq_zero t h, mul_zero]
  have hprod : 0 < labelledProduct t := Nat.pos_of_ne_zero hprod0
  have hpositive (i : Fin k) : 0 < (t i).val := by
    apply Nat.pos_of_ne_zero
    exact (Finset.prod_ne_zero_iff.mp hprod0) i (mem_univ i)
  have hcoordinate (i : Fin k) : ((t i).val : ℝ) ≤ X := by
    have hdiv : (t i).val ∣ labelledProduct t :=
      Finset.dvd_prod_of_mem (fun i => (t i).val) (mem_univ i)
    have hle : ((t i).val : ℝ) ≤ (labelledProduct t : ℝ) := by
      exact_mod_cast Nat.le_of_dvd hprod hdiv
    exact hle.trans hProduct
  unfold originalChartBank
  apply originalDyadicChartWeight_sum_eq_one χ 0 (originalChartHeight X) t χlo χhi
  · intro i
    have hi : (1 : ℝ) ≤ ((t i).val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr (hpositive i))
    norm_num only [zero_sub, zpow_neg_one, div_inv_eq_mul]
    linarith
  · intro i
    have he : (0 : ℤ) - 1 + (originalChartHeight X : ℤ) =
        ((Nat.log 2 (Nat.ceil X) + 1 : ℕ) : ℤ) := by
      unfold originalChartHeight
      omega
    rw [he, zpow_natCast]
    apply (div_le_one (by positivity)).mpr
    have hcap : ((t i).val : ℝ) ≤ (Nat.ceil X : ℝ) :=
      (hcoordinate i).trans (Nat.le_ceil X)
    have hpow : (Nat.ceil X : ℝ) < (2 : ℝ) ^ (Nat.log 2 (Nat.ceil X) + 1) := by
      exact_mod_cast Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (Nat.ceil X)
    exact hcap.trans hpow.le

/-- Exact coefficient reconstruction. Tuples outside the effective support
contribute zero to both sides; no partition assumption is imposed there. -/
theorem labelledProperPowerResidual_eq_sum_originalCharts
    (k P : ℕ) (W : (Fin k → Fin (P + 1)) → ℝ) (χ : ℝ → ℝ) (X : ℝ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hProduct : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 →
      (labelledProduct t : ℝ) ≤ X) (b : ℕ) :
    labelledProperPowerResidual k P W b =
      ∑ j ∈ originalChartBank k X,
        labelledProperPowerResidual k P (fun t => W t * originalDyadicChartWeight χ 0 j t) b := by
  have hcoefficient (t : Fin k → Fin (P + 1)) :
      W t * labelledVonMangoldtWeight t =
        ∑ j ∈ originalChartBank k X,
          (W t * originalDyadicChartWeight χ 0 j t) * labelledVonMangoldtWeight t := by
    symm
    calc
      _ = ∑ j ∈ originalChartBank k X,
          (W t * labelledVonMangoldtWeight t) * originalDyadicChartWeight χ 0 j t := by
        apply sum_congr rfl
        intro j _
        ring
      _ = (W t * labelledVonMangoldtWeight t) *
          ∑ j ∈ originalChartBank k X, originalDyadicChartWeight χ 0 j t := by
        rw [mul_sum]
      _ = W t * labelledVonMangoldtWeight t := by
        by_cases ht : W t * labelledVonMangoldtWeight t = 0
        · simp only [ht, zero_mul]
        · rw [originalDyadicChartWeight_sum_eq_one_of_effective χ W t χlo χhi ht
            (hProduct t ht), mul_one]
  unfold labelledProperPowerResidual finiteProductMass
  rw [sum_comm]
  apply sum_congr rfl
  intro t _
  by_cases hb : labelledProduct t = b
  · simp only [hb, if_true]
    simpa only [Complex.ofReal_sum] using
      congrArg (fun r : ℝ => (r : ℂ)) (hcoefficient t)
  · simp only [hb, if_false, sum_const_zero]

/-- Exact recombination with the original rho and primitive-coprime mean. -/
theorem labelledProperPowerResidual_signedError_eq_sum_originalCharts
    (k P N : ℕ) (B Q : Finset ℕ) (ρ : ℕ → ℂ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (χ : ℝ → ℝ) (X : ℝ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hProduct : ∀ t, W t * labelledVonMangoldtWeight t ≠ 0 →
      (labelledProduct t : ℝ) ≤ X) :
    finiteProductSignedError B Q N ρ (labelledProperPowerResidual k P W) =
      ∑ j ∈ originalChartBank k X, finiteProductSignedError B Q N ρ
        (labelledProperPowerResidual k P (fun t => W t * originalDyadicChartWeight χ 0 j t)) := by
  unfold finiteProductSignedError
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [labelledProperPowerResidual_eq_sum_originalCharts k P W χ X χlo χhi hProduct b,
    sum_mul]

/-- The full tensor bank costs exactly k additional logarithms. -/
theorem originalChartBank_card_le_log (k : ℕ) {C : ℝ} {N : ℕ}
    (hC : 0 < C) (hN : 1 ≤ N) (hCN : C + 1 ≤ (N : ℝ))
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    ((originalChartBank k (C * (N : ℝ))).card : ℝ) ≤
      (2 / Real.log 2 + 2) ^ k * Real.log (N : ℝ) ^ k := by
  have hheight : (originalChartHeight (C * (N : ℝ)) : ℝ) ≤
      (2 / Real.log 2 + 2) * Real.log (N : ℝ) := by
    have hl := ProperPowerLogSaving.log_ceil_linear_le hC hN hCN
    simp only [originalChartHeight, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  rw [originalChartBank_card, Nat.cast_pow]
  exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hheight k).trans_eq (mul_pow _ _ _)

/-- Every logarithmic saving for the complete original proper-power residual.
The common threshold is chosen before every carrier, weight, and cutoff. -/
theorem eventually_labelledProperPowerResidual_logAccuracy
    (k J m : ℕ) {M C c K Cρ a θ : ℝ}
    (hM : 0 < M) (hC : 0 < C) (hc : 0 < c) (hK : 0 < K)
    (hCρ : 0 < Cρ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ P : ℕ, ∀ B Q : Finset ℕ, ∀ ρ : ℕ → ℂ,
      ∀ W : (Fin k → Fin (P + 1)) → ℝ, ∀ χ : ℝ → ℝ,
      B ⊆ Icc 1 (Nat.ceil (C * (N : ℝ))) →
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      (∀ t, |W t| ≤ M * Real.log (N : ℝ) ^ m) →
      (∀ t, W t * labelledVonMangoldtWeight t ≠ 0 →
        (∀ i, c * (N : ℝ) ^ a ≤ ((t i).val : ℝ)) ∧
          (labelledProduct t : ℝ) ≤ C * N) →
      ‖finiteProductSignedError B Q N ρ (labelledProperPowerResidual k P W)‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  let D : ℝ := (2 / Real.log 2 + 2) ^ k
  have hD : 0 < D := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [D]
    positivity
  have hChart := ProperPowerLogSaving.eventually_labelledProperPowerResidual_originalChart_logAccuracy
    k J m hM hC hc hK hCρ ha hθ0 hθ1 (A + (k : ℝ)) (ε / D) (div_pos hε hD)
  have hLarge : ∀ᶠ N : ℕ in atTop, C + 1 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (C + 1))
  filter_upwards [hChart, hLarge, ImbalancedChen.eventually_one_le_nat_log,
    eventually_ge_atTop (1 : ℕ)] with N hChartN hLargeN hlog1 hN
  intro P B Q ρ W χ hB hQ hρ χlo χhi χrange hW hGeometry
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hcard : ((originalChartBank k (C * (N : ℝ))).card : ℝ) ≤
      D * Real.log (N : ℝ) ^ k := by
    simpa only [D] using originalChartBank_card_le_log k hC hN hLargeN hlog1
  rw [labelledProperPowerResidual_signedError_eq_sum_originalCharts
    k P N B Q ρ W χ (C * (N : ℝ)) χlo χhi (fun t ht => (hGeometry t ht).2)]
  calc
    _ ≤ ∑ j ∈ originalChartBank k (C * (N : ℝ)),
        ‖finiteProductSignedError B Q N ρ
          (labelledProperPowerResidual k P (fun t => W t * originalDyadicChartWeight χ 0 j t))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j ∈ originalChartBank k (C * (N : ℝ)),
        (ε / D) * (N : ℝ) / Real.log (N : ℝ) ^ (A + (k : ℝ)) := by
      apply sum_le_sum
      intro j _
      exact hChartN P B Q ρ W χ 0 j hB hQ hρ χlo χhi χrange hW hGeometry
    _ = ((originalChartBank k (C * (N : ℝ))).card : ℝ) *
        ((ε / D) * (N : ℝ) / Real.log (N : ℝ) ^ (A + (k : ℝ))) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (D * Real.log (N : ℝ) ^ k) *
        ((ε / D) * (N : ℝ) / Real.log (N : ℝ) ^ (A + (k : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
      rw [Real.rpow_add hlogpos, Real.rpow_natCast]
      field_simp [hD.ne', hlogpos.ne', (Real.rpow_pos_of_pos hlogpos A).ne']

/-- The exact prime/von-Mangoldt identity now has every logarithmic
accuracy after summing all original charts, with the same signed rho. -/
theorem eventually_primeProductSignedError_sub_vonMangoldt_logAccuracy
    (k J m : ℕ) {M C c K Cρ a θ : ℝ}
    (hM : 0 < M) (hC : 0 < C) (hc : 0 < c) (hK : 0 < K)
    (hCρ : 0 < Cρ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ P : ℕ, ∀ B Q : Finset ℕ, ∀ ρ : ℕ → ℝ,
      ∀ W : (Fin k → Fin (P + 1)) → ℝ, ∀ χ : ℝ → ℝ,
      B ⊆ Icc 1 (Nat.ceil (C * (N : ℝ))) →
      (∀ t ∈ labelledPrimeTuples k P, W t ≠ 0 → labelledProduct t ∈ B) →
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, |ρ q| ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      (∀ t, |W t| ≤ M * Real.log (N : ℝ) ^ m) →
      (∀ t, W t * labelledVonMangoldtWeight t ≠ 0 →
        (∀ i, c * (N : ℝ) ^ a ≤ ((t i).val : ℝ)) ∧
          (labelledProduct t : ℝ) ≤ C * N) →
      ‖(primeProductSignedError k P N Q ρ W : ℂ) -
        finiteProductSignedError B Q N (fun q => (ρ q : ℂ))
          (labelledVonMangoldtProductMass k P W)‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A := by
  filter_upwards [eventually_labelledProperPowerResidual_logAccuracy
    k J m hM hC hc hK hCρ ha hθ0 hθ1 A ε hε] with N hN
  intro P B Q ρ W χ hB hPrimeSupport hQ hρ χlo χhi χrange hW hGeometry
  rw [primeProductSignedError_eq_vonMangoldt_sub_properPower k P N Q B ρ W hPrimeSupport,
    sub_sub_cancel_left, norm_neg]
  exact hN P B Q (fun q => (ρ q : ℂ)) W χ hB hQ
    (fun q hq => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hρ q hq)
    χlo χhi χrange hW hGeometry

end
end ImbalancedChen.Part3.ProperPowerChartSum
