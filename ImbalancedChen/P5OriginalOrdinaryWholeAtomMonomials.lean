import ImbalancedChen.P5SelectedRealWholeAtomGroups
import ImbalancedChen.P5OriginalNearCapRealEndpointGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual ORIGINAL ordinary15 near-cap certificate now chooses one
REAL-upper greedy slot partition for the WHOLE prime atom. Its endpoint
products satisfy the original three monomials in the common kappa query
range. No arithmetic representative, per-tuple factorization or Dwell
target is an input. The native run level remains nu-2delta exactly.
This file concerns the prime endpoint products; the common beta endpoint
cost is explicit in SelectedRealWholeAtomGroups.groups_beta_endpoint and
must additionally be paid before a beta-attached analytic licence.
-/
namespace ImbalancedChen.P5Z.OriginalOrdinaryWholeAtomMonomials
noncomputable section
open Classical
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open PresievedRoughSlotAffineGates SelectedRealEndpointSupport SelectedRealWholeAtomGroups
open OriginalNearCapRealEndpointGeometry
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

def endpointFactors {r : ℕ} (N : ℕ) (p : Policy) (u : LogFour) (v : Fin r → ℝ)
    (level A : ℝ) : ℝ × ℝ × ℝ :=
  let out := groups N p u v level A
  ((out.1.map (weight N u v)).prod,
    (out.2.1.map (weight N u v)).prod,
    (out.2.2.map (weight N u v)).prod)

theorem endpointFactors_positive {r N : ℕ} (hN : 1 < N) (p : Policy)
    (u : LogFour) (v : Fin r → ℝ) (level A : ℝ) :
    0 < (endpointFactors N p u v level A).1 ∧
      0 < (endpointFactors N p u v level A).2.1 ∧
      0 < (endpointFactors N p u v level A).2.2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hp (l : List (Fin 4 ⊕ Fin r)) : 0 < (l.map (weight N u v)).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact Real.rpow_pos_of_pos hn _
  exact ⟨hp _, hp _, hp _⟩

/-- The padded endpoints of the literal near-cap box imply every support
input of the REAL-upper action, at the unchanged native run exponent. -/
theorem actual_endpoint_support_inputs (p : Policy) (hp : p.val < 15)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest p B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    {roughWidth : ℝ} (hrw : roughWidth ≤ (delta p B eta : ℝ)) :
    (∀ j : Fin 4, fullSquare j u ≤ (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) ∧
      (∀ j : Fin 4, ¬Selected p j →
        selectedSquare p j u ≤ (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) ∧
      ((∑ i : Fin 4, u i) + ((physicalResidual p B eta : ℝ) + roughWidth) ≤
        (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) := by
  have hd : (0 : ℝ) < (delta p B eta : ℝ) := by
    exact_mod_cast (rational_parameters p B eta hv hw hc heta).2.2.1
  have hs := actual_padded_endpoint_reserves p B eta hv hw hc heta u hlo hhi hrw
  have hselected := hs.2.2.2
  rw [if_pos hp] at hselected
  exact ⟨fun j => by linarith [hs.2.1 j],
    fun j hj => by linarith [hselected j hj], by linarith [hs.2.2.1]⟩

/-- Genuine whole-atom endpoint targets in the ORIGINAL common query
range. Effective theta and proof buffer only re-express nu-2delta;
the algorithm still sees exactly that original run level. -/
theorem actual_ordinary_whole_atom_monomials {r N : ℕ} (hN : 1 < N)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    {roughWidth : ℝ} (hrw : roughWidth ≤ (delta p B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → cube v i < (physicalResidual p B eta : ℝ) + roughWidth)
    {kappa A : ℝ} (hk0 : 0 < kappa) (hk : kappa ≤ (delta p B eta : ℝ) / 64)
    (hAlower : (N : ℝ) ^ kappa ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 - kappa / 2)) :
    let level := (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)
    let abc := endpointFactors N p u v level A
    abc.1 ≤ A ∧
      A ^ 2 * abc.2.1 * abc.2.2 ^ 2 ≤ (N : ℝ) ^ (1 - 3 * kappa / 2) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 3 * kappa / 2) ∧
      (A * abc.2.2 / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - kappa) := by
  let level : ℝ := (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)
  let theta : ℝ := level + kappa
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
  obtain ⟨hnu, hmlower, hmupper⟩ := ordinary_selected_endpoint_critical p hp B eta hv hw hc heta u hlo hhi hk0.le hk
  have hthetaLo : (1 / 2 : ℝ) ≤ theta := by dsimp [theta, level]; linarith
  have hthetaHi : theta ≤ 5 / 8 := by dsimp [theta, level]; linarith
  have hthetaNu : theta ≤ (nu p B eta : ℝ) := by dsimp [theta, level]; linarith
  have hMlower : (N : ℝ) ^ (2 * theta - 1) ≤ middleEndpoint N p u := by
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    dsimp [theta, level]
    linarith
  have hMupper : middleEndpoint N p u ≤ (N : ℝ) ^ actualSelectedSubproductUpper (1 + 3 * kappa) theta := by
    apply Real.rpow_le_rpow_of_exponent_le hn.le
    have hm : selectedMass p u ≤ actualSelectedSubproductUpper (1 + 3 * kappa) (nu p B eta : ℝ) := by linarith
    exact hm.trans (by
      unfold actualSelectedSubproductUpper
      apply min_le_min <;> linarith)
  have hA : 1 ≤ A := (Real.one_le_rpow hn.le hk0.le).trans hAlower
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
  have hlevel : level = theta - 2 * (kappa / 2) := by dsimp [theta]; ring
  by_cases hC : 1 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u)
  · have hb : abc.2.1 = middleEndpoint N p u := by simp only [abc, endpointFactors, groups, if_pos hC]
    have hcb : abc.2.2 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u) := by
      rcases caps.2 with h | h
      · exact h.2
      · exact h.2.le.trans hC
    have hcap : A * abc.2.1 * abc.2.2 ≤ (N : ℝ) ^ (theta - 2 * (kappa / 2)) := by
      rw [hb, ← hlevel]
      calc
        _ = abc.2.2 * (A * middleEndpoint N p u) := by ring
        _ ≤ _ := (le_div_iff₀ (mul_pos hApos (Real.rpow_pos_of_pos hnpos _))).mp hcb
    obtain ⟨h1, h2, h3⟩ := selectedPair_monomials hn hApos hapos hbpos hcpos hcap
      (by simpa only [hb] using hMlower) (by simpa only [hb] using hMupper) ha
    exact ⟨ha, h1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
      h2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)),
      h3.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))⟩
  · have hc1 : abc.2.2 = 1 := by simp only [abc, endpointFactors, groups, if_neg hC, List.map_nil, List.prod_nil]
    have hb : abc.2.1 ≤ (N : ℝ) ^ level / A := by
      rcases caps.2 with h | h
      · have hf : 1 ≤ (N : ℝ) ^ level / (A * middleEndpoint N p u) := by simpa only [hc1] using h.2
        exact False.elim (hC hf)
      · exact h.1
    have hBupper : (N : ℝ) ^ level / A ≤ (N : ℝ) ^ actualSelectedSubproductUpper (1 + 3 * kappa) theta := by
      have hsmall : (N : ℝ) ^ level / A < middleEndpoint N p u := by
        have hh := (div_lt_one (mul_pos hApos (Real.rpow_pos_of_pos hnpos _))).mp (lt_of_not_ge hC)
        exact (div_lt_iff₀ hApos).mpr (by nlinarith)
      exact hsmall.le.trans hMupper
    have hAB : A * ((N : ℝ) ^ level / A) = (N : ℝ) ^ (theta - 2 * (kappa / 2)) := by
      rw [← hlevel]
      field_simp [hApos.ne']
    obtain ⟨h1, h2, h3⟩ := twoFactorRepair_monomials hn (by linarith : kappa / 2 ≤ 1 / 12) hthetaHi
      hApos (div_pos (Real.rpow_pos_of_pos hnpos _) hApos) hapos hbpos hAB
      (hAupper.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))) hBupper ha hb
    refine ⟨ha, ?_, ?_, ?_⟩
    · simpa only [hc1, one_pow, mul_one] using
        h1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith : 1 - 3 * (kappa / 2) ≤ 1 - 3 * kappa / 2))
    · simpa only [hc1, one_pow, mul_one] using
        h2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith : 2 - 4 * (kappa / 2) ≤ 2 - 3 * kappa / 2))
    · simpa only [hc1, one_pow, mul_one] using
        h3.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith : 2 - 39 * (kappa / 2) / 8 ≤ 2 - kappa))

end
end ImbalancedChen.P5Z.OriginalOrdinaryWholeAtomMonomials
