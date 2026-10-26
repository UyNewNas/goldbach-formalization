import ImbalancedChen.P5OriginalOrdinaryWholeAtomMonomials

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Unweakened ORIGINAL delta reserves for the same computed REAL-upper
ordinary15 atom partition. The full interval 1<=A<=N^(1/3) is retained.
The below-capacity-one branch is proved directly from its real product
and critical upper endpoint, without a tiny proof-buffer/A restriction.
The weaker kappa-scale native corollary in the preceding file is not
used to pay the later HB query shift or the common-beta inflation.
-/
namespace ImbalancedChen.P5Z.OriginalOrdinaryWholeAtomDelta
noncomputable section
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open PresievedRoughSlotAffineGates SelectedRealEndpointSupport SelectedRealWholeAtomGroups
open OriginalNearCapRealEndpointGeometry OriginalOrdinaryWholeAtomMonomials

/-- The original repair proof is numerical for positive REAL products.
Its first bound spends theta+delta<=2/3; no tightened A gate is needed. -/
private theorem repair_real_delta {x d theta alpha A a b : ℝ}
    (hx : 1 < x) (hd : d ≤ 3 / 4096) (htheta : theta ≤ 153 / 256)
    (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (hAupper : A ≤ x ^ (1 / 3 : ℝ)) (haa : a ≤ A)
    (hcap : A * b ≤ x ^ (theta - 2 * d))
    (hbupper : b ≤ x ^ actualSelectedSubproductUpper alpha theta) :
    A ^ 2 * b ≤ x ^ (1 - 3 * d) ∧
      x ^ (7 * alpha / 32) * A * a * b ^ 5 ≤ x ^ (2 - 4 * d) ∧
      (A / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 ≤ x ^ (2 - 39 * d / 8) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hL : 0 < Real.log x := Real.log_pos hx
  have hlogcap := (Real.le_rpow_iff_log_le (mul_pos hA hb) hx0).mp hcap
  rw [Real.log_mul hA.ne' hb.ne'] at hlogcap
  have hlogA := (Real.le_rpow_iff_log_le hA hx0).mp hAupper
  have hloga := (Real.log_le_log_iff ha hA).mpr haa
  have hlogb := (Real.le_rpow_iff_log_le hb hx0).mp hbupper
  have hb1 : Real.log b ≤ ((32 - 39 * theta) / 34) * Real.log x :=
    hlogb.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hb2 : Real.log b ≤ ((2 - 2 * theta - 7 * alpha / 32) / 3) * Real.log x :=
    hlogb.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have hbudget : theta + d ≤ 2 / 3 := by linarith
  have hbudgetL := mul_le_mul_of_nonneg_right hbudget hL.le
  refine ⟨?_, ?_, ?_⟩
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (pow_ne_zero 2 hA.ne') hb.ne', Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow hx0, Real.log_pow]
    nlinarith
  · apply Real.le_rpow_of_log_le hx0
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) ha.ne', Real.log_mul (by positivity) hA.ne',
      Real.log_rpow (div_pos hA hb), Real.log_div hA.ne' hb.ne', Real.log_pow]
    nlinarith

/-- SAME actual fixed label partition, now with the unweakened native
delta-scale margins in both capacity branches and the FULL A interval. -/
theorem actual_ordinary_whole_atom_delta {r N : ℕ} (hN : 1 < N)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    {roughWidth : ℝ} (hrw : roughWidth ≤ (delta p B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < (physicalResidual p B eta : ℝ) + roughWidth)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    {kappa : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (delta p B eta : ℝ) / 64) :
    let level := (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)
    let abc := endpointFactors N p u v level A
    abc.1 ≤ A ∧
      A ^ 2 * abc.2.1 * abc.2.2 ^ 2 ≤ (N : ℝ) ^ (1 - 3 * (delta p B eta : ℝ)) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 4 * (delta p B eta : ℝ)) ∧
      (A * abc.2.2 / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 39 * (delta p B eta : ℝ) / 8) := by
  let level : ℝ := (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)
  let abc := endpointFactors N p u v level A
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := zero_lt_one.trans hn
  have hd : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (rational_parameters p B eta hv hw hc heta).2.2.1
  have hdc : (delta p B eta : ℝ) ≤ 3 / 4096 := by
    exact_mod_cast NearCapRationalParameters.delta_le_cap (G p B) (capLower p B) eta
  have hgate : (G p B : ℝ) + 64 * (delta p B eta : ℝ) ≤ (nu p B eta : ℝ) := by
    exact_mod_cast NearCapRationalParameters.gate_buffer (G p B) (capLower p B) eta
  have hhalf : (1 / 2 : ℝ) ≤ (G p B : ℝ) := by exact_mod_cast half_le_G p B
  obtain ⟨hnu, hmlower, hmupper⟩ := ordinary_selected_endpoint_critical p hp B eta hv hw hc heta u hlo hhi hk0 hk
  have hMlower : (N : ℝ) ^ (2 * (nu p B eta : ℝ) - 1) ≤ middleEndpoint N p u := by
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    linarith
  have hMupper : middleEndpoint N p u ≤ (N : ℝ) ^ actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    linarith
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hAlevel : A ≤ (N : ℝ) ^ level := hAupper.trans
    (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [level]; linarith))
  obtain ⟨hfull, hselected, hbudget⟩ := actual_endpoint_support_inputs p hp B eta hv hw hc heta u hlo hhi hrw
  have caps := groups_endpoint_capacities hN p u v level ((physicalResidual p B eta : ℝ) + roughWidth) A
    hfull hselected hv0 hvanti hcubes hbudget hA hAlevel
  have hapos := (endpointFactors_positive hN p u v level A).1
  have hbpos := (endpointFactors_positive hN p u v level A).2.1
  have hcpos := (endpointFactors_positive hN p u v level A).2.2
  have ha : abc.1 ≤ A := caps.1
  by_cases hC : 1 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u)
  · have hb : abc.2.1 = middleEndpoint N p u := by simp only [abc, endpointFactors, groups, if_pos hC]
    have hcb : abc.2.2 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u) := by
      rcases caps.2 with h | h
      · exact h.2
      · exact h.2.le.trans hC
    have hcap : A * abc.2.1 * abc.2.2 ≤ (N : ℝ) ^ ((nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) := by
      rw [hb]
      calc
        _ = abc.2.2 * (A * middleEndpoint N p u) := by ring
        _ ≤ _ := (le_div_iff₀ (mul_pos hApos (Real.rpow_pos_of_pos hnpos _))).mp hcb
    obtain ⟨h1, h2, h3⟩ := selectedPair_monomials hn hApos hapos hbpos hcpos hcap
      (by simpa only [hb] using hMlower) (by simpa only [hb] using hMupper) ha
    exact ⟨ha, h1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)), h2, h3⟩
  · have hc1 : abc.2.2 = 1 := by simp only [abc, endpointFactors, groups, if_neg hC, List.map_nil, List.prod_nil]
    have hb : abc.2.1 ≤ (N : ℝ) ^ level / A := by
      rcases caps.2 with h | h
      · have hf : 1 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u) := by simpa only [hc1] using h.2
        exact False.elim (hC hf)
      · exact h.1
    have hBlt : (N : ℝ) ^ level / A < middleEndpoint N p u := by
      have hh := (div_lt_one (mul_pos hApos (Real.rpow_pos_of_pos hnpos _))).mp (lt_of_not_ge hC)
      exact (div_lt_iff₀ hApos).mpr (by nlinarith)
    have hbupper := (hb.trans hBlt.le).trans hMupper
    have hcap : A * abc.2.1 ≤ (N : ℝ) ^ ((nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) := by
      calc
        _ = abc.2.1 * A := by ring
        _ ≤ _ := (le_div_iff₀ hApos).mp hb
    obtain ⟨h1, h2, h3⟩ := repair_real_delta hn hdc hnu hApos hapos hbpos hAupper ha hcap hbupper
    exact ⟨ha, by simpa only [hc1, one_pow, mul_one] using h1,
      by simpa only [hc1, one_pow, mul_one] using h2,
      by simpa only [hc1, one_pow, mul_one] using h3⟩

end
end ImbalancedChen.P5Z.OriginalOrdinaryWholeAtomDelta
