import ImbalancedChen.P5ZU1011OriginalFifteenMediumNumericGates
import ImbalancedChen.P5OriginalPresievedActiveDeltaFactors
import ImbalancedChen.P5OriginalCommonBetaActualParameters

/-!
# Actual common-beta presieved ORIGINAL15 coefficient: all Medium numeric gates

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
This explicitly uses the NEW presievedSigma, not the old all-prime sigma.
The same actual active coefficient supplies its own tuple, small e and rough
native d; the actual e attaches only to group3. The physical product is the
new coefficient's q exactly. Its proved post-beta delta reserves supply all
four strict Medium numerical gates at EVERY prescribed HB length.
The common beta epsilon is fixed within the actual selected-cutoff budget
before N/E; that budget derives w<=nativeZ and ell<=nativeDelta/8.
No old-sigma equality, assumed factor reserves, atomwise fixed convolution,
auxiliary SW, or signed Medium/PP estimate is asserted.
-/

namespace ImbalancedChen.P5Z.OriginalPresievedMediumNumericGates
noncomputable section
open Classical Filter
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open U1011OriginalSixteenStaticNativeCompiler (ownerBox selectedPolicy)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax)
open U1011OriginalFifteenMediumNumericGates
open U1011OriginalFifteenJointSmallBeta (attachedFactors)
open OriginalCommonBetaActualParameters
private theorem eventually_presieved_power_in_chart {c t a b : ℝ}
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

private theorem presieved_numeric_of_local_reserves {N : ℕ} {x U z A a b c : ℝ}
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

/-- Every nonzero actual NEW common-beta presieved coefficient has an
actual product-q decomposition obeying ALL FOUR strict Medium numeric
gates. Eta, common beta epsilon, zeta/sigma and kappa precede the threshold;
N,x,HB U,E,q and their actual t/e/d witnesses follow it. -/
theorem exists_actual_presieved_medium_numeric_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu0 epsilon : ℝ)
    (hnu : 0 < nu0) (hepsilon : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ sigma n eta / 200)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
      ∀ U : ℝ, x ^ (2 * zeta n eta) ≤ U → U ≤ x ^ (1 / 3 + zeta n eta / 2) →
      ∀ (E : ℕ × ℕ → Prop) (q : ℕ),
      OriginalOrdinaryPresievedSigma.presievedSigma n N eta
        ((N : ℝ) ^ (nu0 * epsilon ^ 2)) ((N : ℝ) ^ (nu0 * epsilon)) E q ≠ 0 →
      ∃ t ∈ OriginalOrdinaryPresievedSigma.tuples n N E, ∃ e d : ℕ,
        q = fullPrefix t * (e * d) ∧
        let A := innerQuery x U (zeta n eta)
        let abc := attachedFactors (selectedPolicy n N t) (ownerBox n N t) eta N A t d e
        abc.1 * abc.2.1 * abc.2.2 = q ∧
          NumericGates N x U (abc.1 : ℝ) (abc.2.1 : ℝ) (abc.2.2 : ℝ) (sigma n eta) := by
  obtain ⟨hz0, hzhi, _, _⟩ := analytic_choice_bounds n eta heta
  let z := zeta n eta
  have hz : 0 < z := hz0
  have hzu : z ≤ 1 / 128 := hzhi
  have hkz : kappa ≤ z / 400000 := by
    dsimp [sigma] at hk
    dsimp [z]
    linarith
  have hkmax : kappa ≤ (kappaMax n eta : ℝ) := by dsimp [z, zeta] at hkz; linarith
  have hfrac : kappa / (4 * (1 + kappa)) ≤ kappa / 4 :=
    div_le_div_of_nonneg_left hk0.le (by norm_num) (by linarith)
  have htiny : kappa0 < z / 1000000 := by linarith [ht.trans_le hfrac]
  have htprod := mul_pos ht0 hz
  have hg1 : 1 - 4 * z < (1 - kappa0) * (1 - 3 * z) := by nlinarith
  have hg2 : 2 - 4 * z < (1 - kappa0) * (2 - 3 * z) := by nlinarith
  obtain ⟨N1, hN1, hnative⟩ := exists_original15_medium_numeric_threshold n eta heta
    hc hC hk0 hk ht0 ht
  have hpay1 := eventually_presieved_power_in_chart hc (by linarith : 0 ≤ 1 - 3 * z) hg1
  have hpay2 := eventually_presieved_power_in_chart hc (by linarith : 0 ≤ 2 - 3 * z) hg2
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpay1.and hpay2)
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N1) ((le_max_left _ _).trans hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨hx, hlo, hhi, hquery⟩ := hnative N ((le_max_left _ _).trans hN) x hlow hupp
  have hpays := hN2 N ((le_max_right _ _).trans hN)
  refine ⟨hx, hlo, hhi, ?_⟩
  intro U hUlo hUhi E q hq
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _).trans_le hUlo
  let A := innerQuery x U z
  obtain ⟨hA1, hAupper, _⟩ := hquery U hUlo hUhi
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hw : ∀ t ∈ OriginalOrdinaryPresievedSigma.tuples n N E,
      (N : ℝ) ^ (nu0 * epsilon ^ 2) ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t := by
    intro t ht
    exact (parameters_on_original_tuple hNN heta hnu hepsilon heBudget ht).2.2.1
  have hell : ∀ t ∈ OriginalOrdinaryPresievedSigma.tuples n N E,
      nu0 * epsilon ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta
        (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) / 8 := by
    intro t ht
    exact (parameters_on_original_tuple hNN heta hnu hepsilon heBudget ht).2.2.2.2
  obtain ⟨t, ht, e, he, d, hd, heB, hqeq, hdNative, hfactors⟩ :=
    OriginalPresievedActiveDeltaFactors.active_original_presieved_delta_factors
      hNN heta E nu0 epsilon hw hell hq
  have htOrd := (Finset.mem_filter.mp ht).1
  have htag := (Finset.mem_filter.mp htOrd).2
  let p := selectedPolicy n N t
  let B := ownerBox n N t
  have hcommon : (kappaMax n eta : ℝ) ≤
      (U1011OriginalSixteenNearCapBoxProfiles.delta p B eta : ℝ) / 64 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell
      eta _ (owner_mem_selected htag)
  have hzdelta : 1024 * z ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta p B eta : ℝ) := by
    dsimp [z, zeta]
    linarith
  have hdata := hfactors A hA1 hAupper kappa hk0.le (hkmax.trans hcommon)
  let abc := attachedFactors p B eta N A t d e
  have ha : (0 : ℝ) < abc.1 := by exact_mod_cast hdata.2.1
  have hb : (0 : ℝ) < abc.2.1 := by exact_mod_cast hdata.2.2.1
  have hc' : (0 : ℝ) < abc.2.2 := by exact_mod_cast hdata.2.2.2.1
  have hm1 : A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - 3 * z) :=
    (hdata.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.1 x hlow)
  have hm2big : (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
      (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hdata.2.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.2 x hlow)
  have hm2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
      (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * z) := by
    have hspectral := Real.rpow_le_rpow_of_exponent_le hNr.le
      (by linarith : (7 / 32 : ℝ) ≤ 7 * (1 + 3 * kappa) / 32)
    have hh := mul_le_mul_of_nonneg_right hspectral
      (by positivity : 0 ≤ A * (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2)
    have hsmall : (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
        (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤
        (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
          (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact hsmall.trans hm2big
  have hm3 : (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
      (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hdata.2.2.2.2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.2 x hlow)
  exact ⟨t, ht, e, d, hqeq, hdata.1,
    presieved_numeric_of_local_reserves hNp hx hz hUp rfl ha hb hc'
      hdata.2.2.2.2.1 hm1 hm2 hm3⟩

end
end ImbalancedChen.P5Z.OriginalPresievedMediumNumericGates

