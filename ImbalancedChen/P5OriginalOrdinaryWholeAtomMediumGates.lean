import ImbalancedChen.P5OriginalOrdinaryWholeAtomDelta
import ImbalancedChen.P5OriginalPresievedMediumNumericGates
import ImbalancedChen.Part3ActualWSmallThirdAttachment

/-!
# Computed ordinary WHOLE-atom endpoint groups, including beta: Medium gates
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
This uses the REAL endpoint algorithm's actual fixed occurrence groups.
Its monomials are DERIVED by994b from literal near-cap certificates, never
assumed. The group3 endpoint is multiplied by the full common N^ell.
All four strict Medium NUMERICAL inequalities hold directly for these
WHOLE-box endpoint products at every prescribed HB length. No identification
with tuplewise integer constructor groups from665/b105 is used or needed.
The exact residue remains N^(7/32). W's computed partition is distinct.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryWholeAtomMediumGates
noncomputable section
open Classical Filter
open scoped BigOperators
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (boxPolicy boxPolicy_certificate)
open U1011OriginalSixteenCommonSmallParameters (selectedCells mem_selectedCells)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax)
open OriginalNearCapRealEndpointGeometry
open OriginalOrdinaryWholeAtomMonomials OriginalOrdinaryWholeAtomDelta
open U1011OriginalFifteenMediumNumericGates
open OriginalCommonBetaActualParameters
open ImbalancedChen.Part3.ActualWSameKeyMonomials (Monomials)
open ImbalancedChen.Part3.ActualWSmallThirdAttachment (third_attachment_monomials)
private theorem eventually_whole_power_in_chart {c t a b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (hg : a < (1 - t) * b) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - t) ≤ x → (N : ℝ) ^ a ≤ x ^ b := by
  have hp : 0 < c ^ b := Real.rpow_pos_of_pos hc _
  filter_upwards [eventually_const_mul_rpow_le_rpow (c ^ b)⁻¹ hg] with N hN
  intro x hx
  have hpaid : (N : ℝ) ^ a ≤ c ^ b * (N : ℝ) ^ ((1 - t) * b) := by
    have hm := mul_le_mul_of_nonneg_left hN hp.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] using hm
  calc
    _ ≤ c ^ b * (N : ℝ) ^ ((1 - t) * b) := hpaid
    _ = (c * (N : ℝ) ^ (1 - t)) ^ b := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _),
        ← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ x ^ b := Real.rpow_le_rpow
      (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hx hb

private theorem whole_numeric_of_local_reserves {N : ℕ} {x U z A a b c : ℝ}
    (hN : 0 < (N : ℝ)) (hx : 1 < x) (hz : 0 < z)
    (hU : 0 < U) (hA : A = innerQuery x U z)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (haa : a ≤ A)
    (h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 3 * z))
    (h2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * z))
    (h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * z)) :
    NumericGates N x U a b c (z / 2000) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hAp : 0 < A := by rw [hA, innerQuery]; positivity
  have hL : 0 < Real.log x := Real.log_pos hx
  have hAl : Real.log A = Real.log U - z * Real.log x := by
    rw [hA, innerQuery, Real.log_mul hU.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0]
    ring
  have hla := (Real.log_le_log_iff ha hAp).mpr haa
  have hl1 := (Real.le_rpow_iff_log_le (by positivity : 0 < A ^ 2 * b * c ^ 2) hx0).mp h1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hb.ne'] at hl1
  simp only [Real.log_pow] at hl1
  have hl2 := (Real.le_rpow_iff_log_le
    (by positivity : 0 < (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2) hx0).mp h2
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) ha.ne',
    Real.log_mul (by positivity) hAp.ne', Real.log_rpow hN] at hl2
  simp only [Real.log_pow] at hl2
  have hl3 := (Real.le_rpow_iff_log_le
    (by positivity : 0 < (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2) hx0).mp h3
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) ha.ne',
    Real.log_mul (by positivity) hAp.ne', Real.log_rpow (div_pos (mul_pos hAp hc) hb),
    Real.log_div (mul_ne_zero hAp.ne' hc.ne') hb.ne', Real.log_mul hAp.ne' hc.ne'] at hl3
  simp only [Real.log_pow] at hl3
  have hzL := mul_pos hz hL
  unfold NumericGates
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Real.log_lt_log_iff ha (mul_pos hU (Real.rpow_pos_of_pos hx0 _))).mp
    rw [Real.log_mul hU.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0]
    nlinarith


  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hb.ne', Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) ha.ne',
      Real.log_mul (by positivity) hU.ne', Real.log_rpow hN, Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) ha.ne',
      Real.log_rpow hU, Real.log_rpow hb, Real.log_rpow hc, Real.log_rpow hx0]
    nlinarith


def betaEndpointFactors {r : ℕ} (N : ℕ) (p : Policy) (B : Box) (eta : ℚ)
    (u : LogFour) (v : Fin r → ℝ) (A ell : ℝ) : ℝ × ℝ × ℝ :=
  let abc := endpointFactors N p u v ((nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) A
  (abc.1, abc.2.1, (N : ℝ) ^ ell * abc.2.2)

private theorem endpoints_ge_one {r N : ℕ} (hN : 1 < N) (p : Policy)
    (u : LogFour) (v : Fin r → ℝ) (level A : ℝ)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ i, 0 ≤ v i) :
    1 ≤ (endpointFactors N p u v level A).1 ∧
      1 ≤ (endpointFactors N p u v level A).2.1 ∧
      1 ≤ (endpointFactors N p u v level A).2.2 := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt hN)
  have hw (i : Fin 4 ⊕ Fin r) : 1 ≤ SelectedRealWholeAtomGroups.weight N u v i := by
    cases i with
    | inl i => exact Real.one_le_rpow hn (hu i)
    | inr i => exact Real.one_le_rpow hn (hv i)
  have hp (l : List (Fin 4 ⊕ Fin r)) : 1 ≤ (l.map (SelectedRealWholeAtomGroups.weight N u v)).prod := by
    induction l with
    | nil => simp
    | cons i l ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (by simpa only [one_mul] using
          (mul_le_mul (hw i) ih zero_le_one (zero_le_one.trans (hw i))))
  exact ⟨hp _, hp _, hp _⟩

/-- Existing generic third-group algebra is applied to the ACTUAL computed
REAL groups with the full common beta endpoint. No target monomial input. -/
private theorem actual_whole_beta_reserves {r N : ℕ} (hN : 1 < N)
    (p : Policy) (hp : p.val < 15) (B : Box) (eta : ℚ)
    (hv : B.Valid) (hw : 0 < B.lo 3) (hc : wholeBoxEligibleTest p B = true)
    (heta : 0 < eta) (u : LogFour)
    (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding p B eta)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    {roughWidth : ℝ} (hrw : roughWidth ≤ (delta p B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → PresievedRoughSlotAffineGates.cube v i <
      (physicalResidual p B eta : ℝ) + roughWidth)
    (A : ℝ) (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (ell : ℝ) (hell : ell ≤ (delta p B eta : ℝ) / 8) :
    let abc := betaEndpointFactors N p B eta u v A ell
    abc.1 ≤ A ∧ 0 < abc.1 ∧ 0 < abc.2.1 ∧ 0 < abc.2.2 ∧
      A ^ 2 * abc.2.1 * abc.2.2 ^ 2 ≤ (N : ℝ) ^ (1 - 3 * (delta p B eta : ℝ) / 2) ∧
      (N : ℝ) ^ (7 / 32 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 3 * (delta p B eta : ℝ) / 2) ∧
      (A * abc.2.2 / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
        (N : ℝ) ^ (2 - 117 * (delta p B eta : ℝ) / 64) := by
  let level := (nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)
  let abc := endpointFactors N p u v level A
  let delt := (delta p B eta : ℝ)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hn
  have hAp : 0 < A := zero_lt_one.trans_le hA
  have hd : 0 < delt := by exact_mod_cast (rational_parameters p B eta hv hw hc heta).2.2.1
  obtain ⟨haA, h1, h2, h3⟩ := actual_ordinary_whole_atom_delta (kappa := (0 : ℝ)) hN
    p hp B eta hv hw hc heta u hlo hhi v hv0 hvanti hrw hcubes A hA hAupper (by norm_num) (by linarith)
  obtain ⟨ha, hb, hc'⟩ := endpointFactors_positive hN p u v level A
  have hm : Monomials (N : ℝ) (3 * delt / 4) A abc.1 abc.2.1 abc.2.2 := by
    refine ⟨?_, ?_, ?_⟩
    · calc
        _ ≤ (N : ℝ) ^ (1 - 3 * delt) := h1
        _ = _ := by congr 1; ring
    · have h2' : (N : ℝ) ^ (7 / 32 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤
          (N : ℝ) ^ (2 - 4 * delt) := by simpa only [mul_zero, add_zero, mul_one] using h2
      exact h2'.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    · exact h3.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [delt]; linarith))
  have hatt := third_attachment_monomials hn hAp ha hb hc'
    (Real.rpow_pos_of_pos hNp ell) (le_refl ((N : ℝ) ^ ell))
    (show ell ≤ 3 * delt / 4 by dsimp [delt]; linarith) hm
  refine ⟨haA, ha, hb, mul_pos (Real.rpow_pos_of_pos hNp _) hc', ?_, ?_, ?_⟩
  · exact hatt.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [delt]; linarith))
  · exact hatt.2.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [delt]; linarith))
  · exact hatt.2.2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by dsimp [delt]; linarith))

/-- One threshold precedes every actual selected ordinary box, its padded
real upper vector, rough word, and prescribed HB U. These are the computed
WHOLE-box group lengths, not tuplewise constructor factors from665. -/
theorem exists_actual_ordinary_whole_box_medium_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu0 epsilon : ℝ)
    (hnu : 0 < nu0) (heps : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ sigma n eta / 200)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
      ∀ U : ℝ, x ^ (2 * zeta n eta) ≤ U → U ≤ x ^ (1 / 3 + zeta n eta / 2) →
      ∀ (j : Grid n), j ∈ selectedCells n → (boxPolicy (gridBox n j)).val < 15 →
      ∀ (u : LogFour), (∀ i, ((gridBox n j).lo i : ℝ) ≤ u i) →
        (∀ i, u i ≤ ((gridBox n j).hi i : ℝ) + endpointPadding (boxPolicy (gridBox n j)) (gridBox n j) eta) →
      ∀ {r : ℕ} (v : Fin r → ℝ), (∀ i, 0 ≤ v i) → Antitone v →
      ∀ roughWidth : ℝ, roughWidth ≤ (delta (boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) →
        (∀ i : Fin r, Even i.val → PresievedRoughSlotAffineGates.cube v i <
          (physicalResidual (boxPolicy (gridBox n j)) (gridBox n j) eta : ℝ) + roughWidth) →
      let abc := betaEndpointFactors N (boxPolicy (gridBox n j)) (gridBox n j) eta u v
        (innerQuery x U (zeta n eta)) (nu0 * epsilon)
      1 ≤ abc.1 ∧ 1 ≤ abc.2.1 ∧ 1 ≤ abc.2.2 ∧ NumericGates N x U abc.1 abc.2.1 abc.2.2 (sigma n eta) := by
  obtain ⟨hz0, hzhi, _, _⟩ := analytic_choice_bounds n eta heta
  let z := zeta n eta
  have hz : 0 < z := hz0
  have hzu : z ≤ 1 / 128 := hzhi
  have hkz : kappa ≤ z / 400000 := by dsimp [sigma] at hk; dsimp [z]; linarith
  have hfrac : kappa / (4 * (1 + kappa)) ≤ kappa / 4 :=
    div_le_div_of_nonneg_left hk0.le (by norm_num) (by linarith)
  have htiny : kappa0 < z / 1000000 := by linarith [ht.trans_le hfrac]
  have htprod := mul_pos ht0 hz
  have hg1 : 1 - 4 * z < (1 - kappa0) * (1 - 3 * z) := by nlinarith
  have hg2 : 2 - 4 * z < (1 - kappa0) * (2 - 3 * z) := by nlinarith
  obtain ⟨N1, hN1, hnative⟩ := exists_original15_medium_numeric_threshold n eta heta hc hC hk0 hk ht0 ht
  have hpay1 := eventually_whole_power_in_chart hc (by linarith : 0 ≤ 1 - 3 * z) hg1
  have hpay2 := eventually_whole_power_in_chart hc (by linarith : 0 ≤ 2 - 3 * z) hg2
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpay1.and hpay2)
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N1) ((le_max_left _ _).trans hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨hx, hlo, hhi, hquery⟩ := hnative N ((le_max_left _ _).trans hN) x hlow hupp
  have hpays := hN2 N ((le_max_right _ _).trans hN)
  refine ⟨hx, hlo, hhi, ?_⟩
  intro U hUlo hUhi j hj hp u hulo huhi r v hv0 hvanti roughWidth hrw hcubes
  let p := boxPolicy (gridBox n j)
  let B := gridBox n j
  let A := innerQuery x U z
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _).trans_le hUlo
  obtain ⟨hA1, hAupper, _⟩ := hquery U hUlo hUhi
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hcert := (boxPolicy_certificate B ((mem_selectedCells j).mp hj)).2
  have hcommon : (kappaMax n eta : ℝ) ≤ (delta p B eta : ℝ) / 64 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell eta j hj
  have hzdelta : 1024 * z ≤ (delta p B eta : ℝ) := by dsimp [z, zeta]; linarith
  have hellMin : (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta : ℝ) ≤ (delta p B eta : ℝ) / 2 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.ellMax_le_cell eta j hj
  have heEll : epsilon ≤ (U1011OriginalSixteenNearCapCommonSmallParameters.ellMax n eta : ℝ) / (4 * nu0) :=
    heBudget.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hell : nu0 * epsilon ≤ (delta p B eta : ℝ) / 8 := by
    have hm := (le_div_iff₀ (by positivity : 0 < 4 * nu0)).mp heEll
    nlinarith
  have hd := actual_whole_beta_reserves hNN p hp B eta (gridBox_valid n j)
    (gridBox_lower_positive n j 3) hcert heta u hulo huhi v hv0 hvanti hrw hcubes A hA1 hAupper (nu0 * epsilon) hell
  let abc := betaEndpointFactors N p B eta u v A (nu0 * epsilon)
  have hm1 : A ^ 2 * abc.2.1 * abc.2.2 ^ 2 ≤ x ^ (1 - 3 * z) :=
    (hd.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans (hpays.1 x hlow)
  have hm2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hd.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans (hpays.2 x hlow)
  have hm3 : (A * abc.2.2 / abc.2.1) ^ (7 / 16 : ℝ) * A * abc.1 * abc.2.1 ^ 5 * abc.2.2 ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hd.2.2.2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans (hpays.2 x hlow)
  have hu0 : ∀ i, 0 ≤ u i := by
    intro i
    have hh : (0 : ℝ) < (B.lo i : ℝ) := by exact_mod_cast gridBox_lower_positive n j i
    exact hh.le.trans (hulo i)
  obtain ⟨ha1, hb1, hc1⟩ := endpoints_ge_one hNN p u v ((nu p B eta : ℝ) - 2 * (delta p B eta : ℝ)) A hu0 hv0
  have hbeta1 : (1 : ℝ) ≤ (N : ℝ) ^ (nu0 * epsilon) := Real.one_le_rpow hNr.le (mul_pos hnu heps).le
  have hlast1 : 1 ≤ abc.2.2 := by
    exact (by simpa only [one_mul] using mul_le_mul hbeta1 hc1 zero_le_one (zero_le_one.trans hbeta1))
  exact ⟨ha1, hb1, hlast1, whole_numeric_of_local_reserves hNp hx hz hUp rfl
    hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.1 hm1 hm2 hm3⟩

end
end ImbalancedChen.P5Z.OriginalOrdinaryWholeAtomMediumGates
