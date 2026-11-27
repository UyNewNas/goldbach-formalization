import ImbalancedChen.P3OriginalU5PairNormalizedDensityReserve

/-!
# Exact-coprime prime correction for the rounded original U5 count

At each original ordered pair, only nonzero rounded coefficients incur the
modulus-prime and centre costs. Counting positive quotients under the full
physical modulus cap and using the bounded pair harmonic mass pays both costs.
The primitive discrepancy keeps its original signed rounded coefficient.
-/

namespace ImbalancedChen.P3OriginalU5RoundedPrimeCorrection

noncomputable section
open scoped Classical BigOperators
open Filter
open P3OriginalU5RoundedCountInsertion
open P3OriginalU5PairNormalizedDensityReserve (exists_pairSupport_harmonic_mass_bound)
open P5CausalPrimeCorrectionPayment (atomCost atomCost_nonneg atomCost_le_log)
open P5OriginalU5CausalFinite (pairSupport)
open P5OriginalU5PlateauPrimeBV (Policy fullModulus markedProduct)

def activeSupport (N : ℕ) (epsilon tau : ℝ) (keep : List ℕ → Bool) : Finset ℕ :=
  (roundedSupport N epsilon).filter (fun k => roundedRho N epsilon tau keep k ≠ 0)

theorem roundedSupport_pos {N k : ℕ} {epsilon : ℝ} (hk : k ∈ roundedSupport N epsilon) :
    0 < k := by
  obtain ⟨⟨s, r⟩, hsr, rfl⟩ := Finset.mem_image.mp hk
  obtain ⟨hs, hr⟩ := Finset.mem_product.mp hsr
  exact Nat.mul_pos (Nat.pos_of_ne_zero (actualSmallRosserSupport_squarefree _ _ _ hs).ne_zero)
    (Nat.pos_of_ne_zero (P2LowerFiniteCellRounding.universe_squarefree _ _ _ _ hr).ne_zero)

def rowSignedPrime (N : ℕ) (epsilon tau : ℝ) (keep : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau keep k *
    (chenPrimeDivisorCount N (fullModulus t k) / (Nat.totient (fullModulus t k) : ℝ))

theorem rowExactMean_eq (N : ℕ) (epsilon tau : ℝ) (keep : List ℕ → Bool) (t : ℕ × ℕ) :
    rowExactMean N epsilon tau keep t = ((chenPrimePrefix N).card : ℝ) *
      (∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau keep k /
        (Nat.totient (fullModulus t k) : ℝ)) - rowSignedPrime N epsilon tau keep t := by
  rw [rowExactMean, rowSignedPrime, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [chenPrimePrefix_coprime_mass]
  ring

def rowCorrectionCost (N : ℕ) (epsilon tau : ℝ) (keep : List ℕ → Bool) (t : ℕ × ℕ) : ℝ :=
  ∑ k ∈ activeSupport N epsilon tau keep, atomCost N (markedProduct t) k

def correctionCost (N : ℕ) (epsilon tau : ℝ) (policy : Policy) : ℝ :=
  ∑ t ∈ pairSupport N, rowCorrectionCost N epsilon tau (policy t) t

theorem correctionCost_nonneg (N : ℕ) (epsilon tau : ℝ) (policy : Policy) :
    0 ≤ correctionCost N epsilon tau policy :=
  Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun k _ => atomCost_nonneg N (markedProduct t) k

theorem abs_row_corrections_le (N : ℕ) (epsilon tau : ℝ) (keep : List ℕ → Bool) (t : ℕ × ℕ) :
    |rowSignedPrime N epsilon tau keep t + rowSignedCentre N epsilon tau keep t| ≤
      rowCorrectionCost N epsilon tau keep t := by
  rw [rowSignedPrime, rowSignedCentre, ← Finset.sum_add_distrib]
  simp_rw [← mul_add]
  change |∑ k ∈ roundedSupport N epsilon, roundedRho N epsilon tau keep k *
    atomCost N (markedProduct t) k| ≤ _
  rw [rowCorrectionCost, activeSupport, Finset.sum_filter]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  by_cases hz : roundedRho N epsilon tau keep k = 0
  · simp [hz]
  · rw [if_pos hz, abs_mul, abs_of_nonneg (atomCost_nonneg _ _ _)]
    have hr : |roundedRho N epsilon tau keep k| ≤ 1 :=
      P2LowerFiniteCellBetaCompiler.rho_abs_le_one _ _ _ _ _ _ _ _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr (atomCost_nonneg N (markedProduct t) k)

theorem abs_corrections_le (N : ℕ) (epsilon tau : ℝ) (policy : Policy) :
    |(∑ t ∈ pairSupport N, rowSignedPrime N epsilon tau (policy t) t) +
      (∑ t ∈ pairSupport N, rowSignedCentre N epsilon tau (policy t) t)| ≤
      correctionCost N epsilon tau policy := by
  rw [← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun t _ => abs_row_corrections_le N epsilon tau (policy t) t)

theorem original_U5_rounded_main_sub_correction_lower {N : ℕ} (hN : 2 ≤ N) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon8 : epsilon < 1 / 8) (tau : ℝ) (policy : Policy) :
    ((chenPrimePrefix N).card : ℝ) * (∑ t ∈ pairSupport N, ∑ k ∈ roundedSupport N epsilon,
      roundedRho N epsilon tau (policy t) k / (Nat.totient (fullModulus t k) : ℝ)) +
      (∑ t ∈ pairSupport N, rowSignedPrimitive N epsilon tau (policy t) t) -
      correctionCost N epsilon tau policy ≤ currentChenUpsilon5 N := by
  have h := original_U5_rounded_exact_mean_lower hN hepsilon hepsilon8 tau policy
  simp_rw [rowExactMean_eq] at h
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  have hc := (le_abs_self _).trans (abs_corrections_le N epsilon tau policy)
  linarith only [h, hc]

/-- At most X/(p*q) positive quotient integers can occur at this original pair. -/
theorem activeSupport_card_le {N : ℕ} {epsilon tau X : ℝ} {keep : List ℕ → Bool} {t : ℕ × ℕ}
    (hb : 0 < markedProduct t) (hX : 0 ≤ X)
    (hcap : ∀ k : ℕ, roundedRho N epsilon tau keep k ≠ 0 → (fullModulus t k : ℝ) < X) :
    ((activeSupport N epsilon tau keep).card : ℝ) ≤ X / (markedProduct t : ℝ) := by
  have hbR : (0 : ℝ) < markedProduct t := by exact_mod_cast hb
  have hx := div_nonneg hX hbR.le
  have hsub : activeSupport N epsilon tau keep ⊆ Finset.Icc 1 ⌊X / (markedProduct t : ℝ)⌋₊ := by
    intro k hk
    obtain ⟨hks, hkn⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_Icc.mpr ⟨roundedSupport_pos hks, (Nat.le_floor_iff hx).mpr ?_⟩
    apply (le_div_iff₀ hbR).mpr
    simpa only [fullModulus, Nat.cast_mul, mul_comm] using (hcap k hkn).le
  have hcard := Finset.card_le_card hsub
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hcard
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hx)

theorem correctionCost_le_power_log {N : ℕ} (hN : 1 ≤ N) (epsilon tau H : ℝ) (policy : Policy)
    (hmass : (∑ t ∈ pairSupport N, 1 / (Nat.totient (t.1 * t.2) : ℝ)) ≤ H)
    (hcap : ∀ t ∈ pairSupport N, ∀ k : ℕ, roundedRho N epsilon tau (policy t) k ≠ 0 →
      (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) :
    correctionCost N epsilon tau policy ≤
      (2 * H / Real.log 2) * (N : ℝ) ^ (599 / 1000 : ℝ) * Real.log (N : ℝ) := by
  let X := (N : ℝ) ^ (599 / 1000 : ℝ)
  let A := 2 * (Real.log (N : ℝ) / Real.log 2)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : 0 ≤ X := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hXN : X ≤ N := by
    simpa only [X, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hNR (by norm_num : (599 / 1000 : ℝ) ≤ 1)
  have hA : 0 ≤ A := mul_nonneg (by norm_num)
    (div_nonneg (Real.log_nonneg hNR) (Real.log_nonneg (by norm_num)))
  have hAX := mul_nonneg hA hX
  calc
    _ ≤ ∑ t ∈ pairSupport N, (A * X) * (1 / (Nat.totient (markedProduct t) : ℝ)) := by
      apply Finset.sum_le_sum
      intro t ht
      have hb : 0 < markedProduct t := Nat.zero_lt_one.trans (chenY5PrimeSelector_sieve_data ht).1
      have hphi := Nat.totient_pos.mpr hb
      have hrec : 1 / (markedProduct t : ℝ) ≤ 1 / (Nat.totient (markedProduct t) : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hphi) (Nat.cast_le.mpr (Nat.totient_le _))
      calc
        _ ≤ ∑ _k ∈ activeSupport N epsilon tau (policy t), A := by
          apply Finset.sum_le_sum
          intro k hk
          obtain ⟨hks, hkn⟩ := Finset.mem_filter.mp hk
          have hphys : fullModulus t k ≤ N := by exact_mod_cast (hcap t ht k hkn).le.trans hXN
          exact atomCost_le_log hN hb (roundedSupport_pos hks) hphys
        _ = ((activeSupport N epsilon tau (policy t)).card : ℝ) * A := by simp
        _ ≤ (X / (markedProduct t : ℝ)) * A :=
          mul_le_mul_of_nonneg_right (activeSupport_card_le hb hX (hcap t ht)) hA
        _ = (A * X) * (1 / (markedProduct t : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hrec hAX
    _ = (A * X) * (∑ t ∈ pairSupport N, 1 / (Nat.totient (markedProduct t) : ℝ)) :=
      (Finset.mul_sum ..).symm
    _ ≤ (A * X) * H := mul_le_mul_of_nonneg_left hmass hAX
    _ = _ := by dsimp only [A, X]; ring

theorem eventually_uniform_correction_payment (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (epsilon tau : ℝ) (policy : Policy),
      (∀ t ∈ pairSupport N, ∀ k : ℕ, roundedRho N epsilon tau (policy t) k ≠ 0 →
        (fullModulus t k : ℝ) < (N : ℝ) ^ (599 / 1000 : ℝ)) →
      correctionCost N epsilon tau policy ≤ eta * singularNormalization N := by
  obtain ⟨H, _, N0, hH⟩ := exists_pairSupport_harmonic_mass_bound
  filter_upwards [eventually_ge_atTop N0, eventually_ge_atTop (1 : ℕ),
    eventually_powerLog_le_singularNormalization (2 * H / Real.log 2)
      (599 / 1000) 1 (by norm_num) eta heta] with N hN0 hN hpaid
  intro epsilon tau policy hcap
  exact (correctionCost_le_power_log hN epsilon tau H policy (hH N hN0) hcap).trans
    (by simpa only [pow_one] using hpaid)

end
end ImbalancedChen.P3OriginalU5RoundedPrimeCorrection
