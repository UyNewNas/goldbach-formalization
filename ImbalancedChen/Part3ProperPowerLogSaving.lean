import ImbalancedChen.Part3ProperPowerOriginalChart
import ImbalancedChen.Part3PolynomialResidueDivisorBound
import ImbalancedChen.BoundaryArbitraryLog
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean

/-!
# Arbitrary logarithmic saving for an actual original-chart residual

This is the proper-prime-power deletion in Appendix D.3 of the frozen
2026-11-06 manuscript. The coefficient, labelled complete product, and
primitive-coprime mean are those of `finiteProductSignedError`.

The existing divisor subpower and weighted divisor means pay the actual
nonzero complete differences and the full-product N diagonal separately.
The only geometric assumptions are on the effective support W * VM.
No residual estimate or uniform distance-divisor bound is an input.

The ceiling/log calculation adapts the source-only
`P5ActualDyadicRankPolynomial.actual_cutoffIndex_le_log`; the distance
calculation adapts `P5ProperPowerPhysicalPolynomialPayment` to the current
`Nat.dist` and finite labelled carriers. Their older source types and
policy-specific modulus coefficient are not imported.

The final threshold precedes the source cap, carrier, chart, weight, and
same signed modulus coefficient. Summing a whole original chart bank and
constructing the actual upper/lower/marked coefficient are separate steps.
-/

namespace ImbalancedChen.Part3.ProperPowerLogSaving

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem divisor_power_subpower (s : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 0 < T ∧ ∀ n : ℕ, 0 < n →
      (n.divisors.card : ℝ) ^ s ≤ T * (n : ℝ) ^ δ := by
  obtain ⟨T, hT, hbound⟩ :=
    PolynomialResidueDivisorBound.fouvryTau_le_const_rpow
      (k := 2 ^ s) (by
        have hp : 0 < (2 : ℕ) ^ s := by positivity
        omega) hδ
  refine ⟨T, hT, fun n hn => ?_⟩
  have hτ : (n.divisors.card : ℝ) ^ s ≤ (fouvryTau (2 ^ s) n : ℝ) := by
    have h := fouvryTau_pow_le 2 s hn.ne'
    rw [fouvryTau_two] at h
    exact_mod_cast h
  exact hτ.trans (hbound n hn)

/-- The divisor budget is computed on the true off-diagonal carrier.
The constant precedes both N and the choice of any physical subcarrier. -/
theorem physical_dist_divisor_sup_pow_le (J : ℕ) {C δ : ℝ}
    (hC : 0 < C) (hδ : 0 < δ) :
    ∃ T : ℝ, 0 < T ∧ ∀ N : ℕ, 1 ≤ N → ∀ B : Finset ℕ,
      B ⊆ Icc 1 (Nat.ceil (C * (N : ℝ))) →
      (((B.erase N).sup (fun b => (Nat.dist b N).divisors.card) : ℕ) : ℝ) ^ (J + 1) ≤
        T * (N : ℝ) ^ δ := by
  obtain ⟨T, hT, hτ⟩ := divisor_power_subpower (J + 1) hδ
  refine ⟨T * (C + 2) ^ δ, by positivity, ?_⟩
  intro N hN B hB
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hceil : (Nat.ceil (C * (N : ℝ)) : ℝ) ≤ C * N + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hC.le hNpos.le)).le
  by_cases hne : (B.erase N).Nonempty
  · obtain ⟨b, hb, heq⟩ := Finset.exists_mem_eq_sup _ hne
      (fun b => (Nat.dist b N).divisors.card)
    rw [heq]
    have hbN : b ≠ N := (mem_erase.mp hb).1
    have hbcap : (b : ℝ) ≤ Nat.ceil (C * (N : ℝ)) := by
      exact_mod_cast (mem_Icc.mp (hB (mem_erase.mp hb).2)).2
    have hdistNat : Nat.dist b N ≤ b + N := by
      unfold Nat.dist
      omega
    have hdist : (Nat.dist b N : ℝ) ≤ (C + 2) * N := by
      have hd : (Nat.dist b N : ℝ) ≤ (b : ℝ) + N := by exact_mod_cast hdistNat
      nlinarith
    calc
      _ ≤ T * (Nat.dist b N : ℝ) ^ δ := hτ _ (Nat.dist_pos_of_ne hbN)
      _ ≤ T * ((C + 2) * (N : ℝ)) ^ δ :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hdist hδ.le) hT.le
      _ = _ := by rw [Real.mul_rpow (by linarith : 0 ≤ C + 2) hNpos.le]; ring
  · have he : B.erase N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [he, Finset.sup_empty, Nat.bot_eq_zero, Nat.cast_zero,
      zero_pow (Nat.succ_ne_zero J)]
    positivity

/-- Weighted divisor moments of the same rho. The primitive-mean mass
costs only logarithms; it is never replaced by the total modulus mass. -/
theorem modulus_masses_le_divisor_moments (J : ℕ) (Q : Finset ℕ) (ρ : ℕ → ℂ)
    {Cρ R : ℝ} (hCρ : 0 ≤ Cρ) (hR : 1 ≤ R)
    (hQ : Q ⊆ Ioc 0 (Nat.floor R))
    (hρ : ∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) :
    SignedModulusPayment.modulusMass Q ρ ≤
        Cρ * R * (1 + Real.log R) ^ (2 ^ J - 1) ∧
      SignedModulusPayment.meanMass Q ρ ≤
        Cρ * (1 + Real.log R) ^ (2 * 2 ^ J) := by
  constructor
  · calc
      _ ≤ ∑ q ∈ Q, Cρ * (q.divisors.card : ℝ) ^ J := sum_le_sum hρ
      _ = Cρ * ∑ q ∈ Q, (q.divisors.card : ℝ) ^ J := by rw [mul_sum]
      _ ≤ Cρ * ∑ q ∈ Ioc 0 (Nat.floor R), (q.divisors.card : ℝ) ^ J :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)) hCρ
      _ ≤ Cρ * (R * (1 + Real.log R) ^ (2 ^ J - 1)) := by
        apply mul_le_mul_of_nonneg_left _ hCρ
        simpa only [fouvryTau_two] using
          sum_fouvryTau_pow_le_real (k := 2) (by norm_num) J hR
      _ = _ := by ring
  · have hpoint (q : ℕ) (hq : q ∈ Q) :
        ‖ρ q‖ / (q.totient : ℝ) ≤ Cρ * ((fouvryTau (2 ^ J) q : ℝ) / q.totient) := by
      have hqpos : 0 < q := (mem_Ioc.mp (hQ hq)).1
      have hτ : (q.divisors.card : ℝ) ^ J ≤ (fouvryTau (2 ^ J) q : ℝ) := by
        have h := fouvryTau_pow_le 2 J hqpos.ne'
        rw [fouvryTau_two] at h
        exact_mod_cast h
      calc
        _ ≤ (Cρ * (q.divisors.card : ℝ) ^ J) / q.totient :=
          div_le_div_of_nonneg_right (hρ q hq) (Nat.cast_nonneg _)
        _ ≤ (Cρ * (fouvryTau (2 ^ J) q : ℝ)) / q.totient :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hCρ)
            (Nat.cast_nonneg _)
        _ = _ := by ring
    calc
      _ ≤ ∑ q ∈ Q, Cρ * ((fouvryTau (2 ^ J) q : ℝ) / q.totient) := sum_le_sum hpoint
      _ = Cρ * ∑ q ∈ Q, ((fouvryTau (2 ^ J) q : ℝ) / q.totient) := by rw [mul_sum]
      _ ≤ Cρ * ∑ q ∈ Ioc 0 (Nat.floor R), ((fouvryTau (2 ^ J) q : ℝ) / q.totient) :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)) hCρ
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_fouvryTau_div_totient_le_real (2 ^ J) hR) hCρ

theorem log_ceil_linear_le {C : ℝ} (hC : 0 < C) {N : ℕ}
    (hN : 1 ≤ N) (hCN : C + 1 ≤ (N : ℝ)) :
    (Nat.log 2 (Nat.ceil (C * (N : ℝ))) : ℝ) ≤
      (2 / Real.log 2) * Real.log (N : ℝ) := by
  let cap := Nat.ceil (C * (N : ℝ))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hN1
  have hceil : (cap : ℝ) ≤ C * N + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hC.le hNpos.le)).le
  have hcapSq : (cap : ℝ) ≤ (N : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hCN hNpos.le
    nlinarith
  by_cases hcap0 : cap = 0
  · change (Nat.log 2 cap : ℝ) ≤ _
    rw [hcap0, Nat.log_zero_right, Nat.cast_zero]
    positivity
  · have hpow : (2 : ℝ) ^ Nat.log 2 cap ≤ (N : ℝ) ^ 2 :=
      (show (2 : ℝ) ^ Nat.log 2 cap ≤ (cap : ℝ) by
        exact_mod_cast Nat.pow_log_le_self 2 hcap0).trans hcapSq
    have hl := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
    simp only [Real.log_pow, Nat.cast_ofNat] at hl
    change (Nat.log 2 cap : ℝ) ≤ _
    calc
      _ ≤ (2 * Real.log (N : ℝ)) / Real.log 2 := (le_div_iff₀ hlog2).mpr hl
      _ = _ := by ring

/-- The actual single-chart proper-power residual has every logarithmic
saving. All geometric and coefficient constants, including the amplitude
logarithm degree, are fixed before the target and before every chart.

Only positive moduli in the actual physical range are assumed. The same
rho remains in the count and its exact primitive-coprime mean. The
diagonal is the full labelled product equal to N, with its tau(N)^k cost.
-/
theorem eventually_labelledProperPowerResidual_originalChart_logAccuracy
    (k J m : ℕ) {M C c K Cρ a θ : ℝ}
    (hM : 0 < M) (hC : 0 < C) (hc : 0 < c) (_hK : 0 < K)
    (hCρ : 0 < Cρ) (ha : 0 < a) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (A ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ P : ℕ, ∀ B Q : Finset ℕ, ∀ ρ : ℕ → ℂ,
      ∀ W : (Fin k → Fin (P + 1)) → ℝ,
      ∀ χ : ℝ → ℝ, ∀ L : ℤ, ∀ j : Fin k → ℕ,
      B ⊆ Icc 1 (Nat.ceil (C * (N : ℝ))) →
      (∀ q ∈ Q, 0 < q ∧ (q : ℝ) ≤ K * (N : ℝ) ^ θ) →
      (∀ q ∈ Q, ‖ρ q‖ ≤ Cρ * (q.divisors.card : ℝ) ^ J) →
      (∀ s ≤ 1, χ s = 1) → (∀ s ≥ 2, χ s = 0) →
      (∀ s, χ s ∈ Set.Icc (0 : ℝ) 1) →
      (∀ t, |W t| ≤ M * (Real.log (N : ℝ)) ^ m) →
      (∀ t, W t * labelledVonMangoldtWeight t ≠ 0 →
        (∀ i, c * (N : ℝ) ^ a ≤ ((t i).val : ℝ)) ∧
          (labelledProduct t : ℝ) ≤ C * N) →
      ‖finiteProductSignedError B Q N ρ
        (labelledProperPowerResidual k P
          (fun t => W t * originalDyadicChartWeight χ L j t))‖ ≤
        ε * (N : ℝ) / (Real.log (N : ℝ)) ^ A := by
  let θ' : ℝ := (θ + 1) / 2
  have hθ'0 : 0 ≤ θ' := by dsimp [θ']; linarith
  have hθθ' : θ < θ' := by dsimp [θ']; linarith
  have hθ'1 : θ' < 1 := by dsimp [θ']; linarith
  let δ : ℝ := min (a / 4) ((1 - θ') / 2)
  have hδ : 0 < δ := by
    apply lt_min <;> linarith
  have hδa : δ ≤ a / 4 := min_le_left _ _
  have hδθ : δ ≤ (1 - θ') / 2 := min_le_right _ _
  have hOff : 1 - a / 2 + δ < 1 := by linarith
  have hDiag : θ' + δ < 1 := by linarith
  obtain ⟨T, hT, hDist⟩ := physical_dist_divisor_sup_pow_le J hC hδ
  obtain ⟨E, hE, hTauN⟩ := divisor_power_subpower k hδ
  let r : ℕ := 2 ^ J - 1
  let z : ℕ := 2 * 2 ^ J
  let V : ℝ := (k : ℝ) * (2 / Real.log 2) * ((5 : ℝ) ^ k * C) / Real.sqrt c
  let H : ℝ := Cρ * T + Cρ * (2 : ℝ) ^ z
  let cOff : ℝ := M * V * H
  let cDiag : ℝ := M * E * Cρ * (2 : ℝ) ^ r
  let A₀ : ℕ := Nat.ceil A
  have hpayOff := ImbalancedChen.eventually_powerLog_le_logAccuracy
    cOff (1 - a / 2 + δ) (m + 1 + z) A₀ hOff (ε / 2) (half_pos hε)
  have hpayDiag := ImbalancedChen.eventually_powerLog_le_logAccuracy
    cDiag (θ' + δ) (m + r) A₀ hDiag (ε / 2) (half_pos hε)
  have hCap := ImbalancedChen.eventually_const_mul_rpow_le_rpow K hθθ'
  have hLarge : ∀ᶠ N : ℕ in atTop, 5 * C + 1 ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (5 * C + 1))
  filter_upwards [hpayOff, hpayDiag, hCap, hLarge,
    ImbalancedChen.eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)]
    with N hpayO hpayD hCapN hLargeN hlog1 hN
  intro P B Q ρ W χ L j hB hQ hρ χlo χhi χrange hW hGeometry
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hNne : N ≠ 0 := by omega
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hlog0 : 0 ≤ Real.log (N : ℝ) := hlogpos.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hpowδ : 1 ≤ (N : ℝ) ^ δ := Real.one_le_rpow hN1 hδ.le
  have hR : 1 ≤ (N : ℝ) ^ θ' := Real.one_le_rpow hN1 hθ'0
  have hQ' : Q ⊆ Ioc 0 (Nat.floor ((N : ℝ) ^ θ')) := by
    intro q hq
    exact mem_Ioc.mpr ⟨(hQ q hq).1, Nat.le_floor ((hQ q hq).2.trans hCapN)⟩
  obtain ⟨hModuli, hMean⟩ := modulus_masses_le_divisor_moments J Q ρ hCρ.le hR hQ' hρ
  have hLogR : 1 + Real.log ((N : ℝ) ^ θ') ≤ 2 * Real.log (N : ℝ) := by
    rw [Real.log_rpow hNpos]
    have h := mul_le_mul_of_nonneg_right hθ'1.le hlog0
    linarith
  have hLogR0 : 0 ≤ 1 + Real.log ((N : ℝ) ^ θ') := by
    have := Real.log_nonneg hR
    linarith
  have hModuli' : SignedModulusPayment.modulusMass Q ρ ≤
      Cρ * (2 : ℝ) ^ r * (N : ℝ) ^ θ' * Real.log (N : ℝ) ^ r := by
    calc
      _ ≤ Cρ * (N : ℝ) ^ θ' * (1 + Real.log ((N : ℝ) ^ θ')) ^ r := hModuli
      _ ≤ Cρ * (N : ℝ) ^ θ' * (2 * Real.log (N : ℝ)) ^ r :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLogR0 hLogR r) (by positivity)
      _ = _ := by rw [mul_pow]; ring
  have hMean' : SignedModulusPayment.meanMass Q ρ ≤
      Cρ * (2 : ℝ) ^ z * Real.log (N : ℝ) ^ z := by
    calc
      _ ≤ Cρ * (1 + Real.log ((N : ℝ) ^ θ')) ^ z := hMean
      _ ≤ Cρ * (2 * Real.log (N : ℝ)) ^ z :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLogR0 hLogR z) hCρ.le
      _ = _ := by rw [mul_pow]; ring
  let D : ℕ := (B.erase N).sup (fun b => (Nat.dist b N).divisors.card)
  have hD : (D : ℝ) ^ (J + 1) ≤ T * (N : ℝ) ^ δ := hDist N hN B hB
  have hDiagonal : (properPowerDiagonalBudget k N : ℝ) ≤ E * (N : ℝ) ^ δ := by
    simpa only [properPowerDiagonalBudget, if_neg hNne, Nat.cast_pow] using
      hTauN N (by omega)
  have hrow : Cρ * (D : ℝ) ^ (J + 1) + SignedModulusPayment.meanMass Q ρ ≤
      H * (N : ℝ) ^ δ * Real.log (N : ℝ) ^ z := by
    have hlogz : 1 ≤ Real.log (N : ℝ) ^ z := one_le_pow₀ hlog1
    have hleft : Cρ * (D : ℝ) ^ (J + 1) ≤
        Cρ * T * (N : ℝ) ^ δ * Real.log (N : ℝ) ^ z := by
      calc
        _ ≤ Cρ * (T * (N : ℝ) ^ δ) := mul_le_mul_of_nonneg_left hD hCρ.le
        _ ≤ Cρ * (T * (N : ℝ) ^ δ) * Real.log (N : ℝ) ^ z :=
          le_mul_of_one_le_right (by positivity) hlogz
        _ = _ := by ring
    have hright : SignedModulusPayment.meanMass Q ρ ≤
        Cρ * (2 : ℝ) ^ z * (N : ℝ) ^ δ * Real.log (N : ℝ) ^ z := by
      apply hMean'.trans
      have h := mul_le_mul_of_nonneg_left hpowδ
        (show 0 ≤ Cρ * (2 : ℝ) ^ z * Real.log (N : ℝ) ^ z by positivity)
      nlinarith only [h]
    exact (add_le_add hleft hright).trans_eq (by dsimp [H]; ring)
  have hChartLog : (Nat.log 2 (Nat.ceil (5 * (C * (N : ℝ)))) : ℝ) ≤
      (2 / Real.log 2) * Real.log (N : ℝ) := by
    simpa only [mul_assoc] using log_ceil_linear_le (C := 5 * C) (by positivity) hN hLargeN
  have hChartCoefficient :
      (k : ℝ) * (Nat.log 2 (Nat.ceil (5 * (C * (N : ℝ)))) : ℝ) *
          ((5 : ℝ) ^ k * C) / Real.sqrt c ≤ V * Real.log (N : ℝ) := by
    calc
      _ ≤ (k : ℝ) * ((2 / Real.log 2) * Real.log (N : ℝ)) *
          ((5 : ℝ) ^ k * C) / Real.sqrt c := by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hChartLog (Nat.cast_nonneg _)) (by positivity)
      _ = _ := by dsimp [V]; ring
  let amplitude : ℝ := M * Real.log (N : ℝ) ^ m
  have hAmplitude : 0 ≤ amplitude := by dsimp [amplitude]; positivity
  have hChartMass :
      amplitude * (((k : ℝ) * (Nat.log 2 (Nat.ceil (5 * (C * (N : ℝ)))) : ℝ) *
        ((5 : ℝ) ^ k * C) / Real.sqrt c) * (N : ℝ) ^ (1 - a / 2)) ≤
      (M * V) * Real.log (N : ℝ) ^ (m + 1) * (N : ℝ) ^ (1 - a / 2) := by
    calc
      _ ≤ amplitude * ((V * Real.log (N : ℝ)) * (N : ℝ) ^ (1 - a / 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hChartCoefficient (by positivity)) hAmplitude
      _ = _ := by dsimp [amplitude]; rw [pow_add, pow_one]; ring
  have hfinite := ProperPowerOriginalChart.labelledProperPowerResidual_originalChart_norm_le
    k P N J D B Q ρ W χ L j hAmplitude hCρ.le hNpos hc hC.le
    χlo χhi χrange hW hGeometry hρ
    (fun b hb hbN => SignedModulusPayment.dist_divisors_card_le_sup B N hb hbN)
  have hoffBound :
      (amplitude * (((k : ℝ) * (Nat.log 2 (Nat.ceil (5 * (C * (N : ℝ)))) : ℝ) *
        ((5 : ℝ) ^ k * C) / Real.sqrt c) * (N : ℝ) ^ (1 - a / 2))) *
          (Cρ * (D : ℝ) ^ (J + 1) + SignedModulusPayment.meanMass Q ρ) ≤
      cOff * (N : ℝ) ^ (1 - a / 2 + δ) * Real.log (N : ℝ) ^ (m + 1 + z) := by
    calc
      _ ≤ ((M * V) * Real.log (N : ℝ) ^ (m + 1) * (N : ℝ) ^ (1 - a / 2)) *
          (H * (N : ℝ) ^ δ * Real.log (N : ℝ) ^ z) := by
        apply mul_le_mul hChartMass hrow
        · exact add_nonneg (by positivity) (SignedModulusPayment.meanMass_nonneg Q ρ)
        · positivity
      _ = cOff * ((N : ℝ) ^ (1 - a / 2) * (N : ℝ) ^ δ) *
          Real.log (N : ℝ) ^ (m + 1 + z) := by dsimp [cOff]; rw [pow_add]; ring
      _ = _ := by rw [← Real.rpow_add hNpos]
  have hdiagBound :
      (amplitude * (properPowerDiagonalBudget k N : ℝ)) *
          SignedModulusPayment.modulusMass Q ρ ≤
      cDiag * (N : ℝ) ^ (θ' + δ) * Real.log (N : ℝ) ^ (m + r) := by
    calc
      _ ≤ (amplitude * (E * (N : ℝ) ^ δ)) *
          (Cρ * (2 : ℝ) ^ r * (N : ℝ) ^ θ' * Real.log (N : ℝ) ^ r) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hDiagonal hAmplitude) hModuli'
        · exact SignedModulusPayment.modulusMass_nonneg Q ρ
        · positivity
      _ = cDiag * ((N : ℝ) ^ θ' * (N : ℝ) ^ δ) * Real.log (N : ℝ) ^ (m + r) := by
        dsimp [cDiag, amplitude]
        rw [pow_add]
        ring
      _ = _ := by rw [← Real.rpow_add hNpos]
  have hNaturalAccuracy :
      ‖finiteProductSignedError B Q N ρ
        (labelledProperPowerResidual k P (fun t => W t * originalDyadicChartWeight χ L j t))‖ ≤
        ε * (N : ℝ) / Real.log (N : ℝ) ^ A₀ := by
    apply (hfinite.trans (add_le_add hoffBound hdiagBound)).trans
    exact (add_le_add hpayO hpayD).trans_eq (by ring)
  apply hNaturalAccuracy.trans
  have hlogPower : Real.log (N : ℝ) ^ A ≤ Real.log (N : ℝ) ^ A₀ := by
    simpa only [Real.rpow_natCast] using
      Real.rpow_le_rpow_of_exponent_le hlog1 (Nat.le_ceil A)
  exact div_le_div_of_nonneg_left (by positivity)
    (Real.rpow_pos_of_pos hlogpos A) hlogPower

end
end ImbalancedChen.Part3.ProperPowerLogSaving
