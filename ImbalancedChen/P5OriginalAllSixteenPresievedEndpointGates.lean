import ImbalancedChen.P5OriginalAllSixteenPresievedMediumNumericGates

/-!
# Actual ALL16 presieved factors tolerate frozen group-endpoint inflation
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Tau=zeta/1000 is selected from the actual eta-dependent finite delta bank.
The coefficient itself supplies actual positive factors and unweakened
physical reserves through the ordinary15 or distinct W constructor.
Fixed group endpoints may lie between each actual factor and 2*N^tau times
that factor. A single threshold absorbs the fixed2 before N/x/U/E/q and
pays all four strict Medium NUMERICAL gates for those ENDPOINT lengths.
Endpoint costs are1,3,8,8; no Medium-eligibility/factorability conclusion
is an input. PrimeBox still owns assigning one fixed group partition on
an entire atom. This module does not assert that assignment, coefficient
SW, exact separated convolution, or signed Medium/PP.
-/

namespace ImbalancedChen.P5Z.OriginalAllSixteenPresievedEndpointGates
noncomputable section
open Classical Filter
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox)
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax)
open OriginalCommonBetaActualParameters OriginalJointCommonBetaModel
open OriginalOrdinaryPresievedSigma OriginalJointPresievedCompiler
open OriginalPresievedRoughPrimeSlots (canonicalSlots)
open U1011OriginalFifteenMediumNumericGates

def endpointTau (n : ℕ) (eta : ℚ) : ℝ := zeta n eta / 1000

private theorem zeta_cell_reserve {n N : ℕ} (eta : ℚ)
    {E : ℕ × ℕ → Prop} {t : Four}
    (ht : t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E) :
    1024 * zeta n eta ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta
      (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) := by
  have htag := (Finset.mem_filter.mp ht).2
  have hm : (kappaMax n eta : ℝ) ≤
      (U1011OriginalSixteenNearCapBoxProfiles.delta
        (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) / 64 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell
      eta _ (owner_mem_selected htag)
  dsimp [zeta]
  linarith

/-- The active coefficient, rather than a supplied factorization or Medium
license, supplies these COMMON zeta reserves before any endpoint inflation. -/
private theorem actual_all16_reserved_factors
    {n N q : ℕ} {eta : ℚ} (hN : 1 < N) (heta : 0 < eta)
    (nu0 epsilon : ℝ) (hnu : 0 < nu0) (hepsilon : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0) (E : ℕ × ℕ → Prop)
    {kappa A : ℝ} (hk0 : 0 ≤ kappa) (hk : kappa ≤ (kappaMax n eta : ℝ))
    (hA : 1 ≤ A) (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hq : jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
      ((N : ℝ) ^ (nu0 * epsilon)) E q ≠ 0) :
    ∃ a b c : ℕ, a * b * c = q ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ (a : ℝ) ≤ A ∧
      A ^ 2 * (b : ℝ) * (c : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 - 4 * zeta n eta) ∧
      (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (a : ℝ) *
        (b : ℝ) ^ 5 * (c : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - 4 * zeta n eta) ∧
      (A * (c : ℝ) / (b : ℝ)) ^ (7 / 16 : ℝ) * A *
        (a : ℝ) * (b : ℝ) ^ 5 * (c : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 - 4 * zeta n eta) := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hz : 0 < zeta n eta := (analytic_choice_bounds n eta heta).1
  have hmem : q ∈ jointSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E := by
    by_contra hn
    exact hq (jointSigma_zero_off_support n N eta
      ((N : ℝ) ^ (nu0 * epsilon ^ 2)) ((N : ℝ) ^ (nu0 * epsilon)) E hn)
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  obtain ⟨htuple, hrow⟩ := Finset.mem_sigma.mp hm
  have hwJoint : ∀ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      (N : ℝ) ^ (nu0 * epsilon ^ 2) ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t := by
    intro t htup
    exact (parameters_on_joint_row hN heta hnu hepsilon heBudget htup).1
  by_cases hp : (selectedPolicy n N m.1).val < 15
  · have hmOrd : m ∈ marks n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) E :=
      Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨htuple, hp⟩, hrow⟩
    have hwOrd : ∀ t ∈ tuples n N E,
        (N : ℝ) ^ (nu0 * epsilon ^ 2) ≤ U1011OriginalSixteenJointNearCapCompiler.Z n N eta t :=
      fun t htup => hwJoint t (Finset.mem_filter.mp htup).1
    have hOrdNonzero : presievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E (modulus m) ≠ 0 := by
      rw [presievedSigma_eq_row hN heta hwOrd hmOrd,
        ← jointSigma_eq_row hN heta hwJoint hm]
      exact hq
    have hell : ∀ t ∈ tuples n N E, nu0 * epsilon ≤
        (U1011OriginalSixteenNearCapBoxProfiles.delta
          (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) / 8 := by
      intro t htup
      exact (parameters_on_original_tuple hN heta hnu hepsilon heBudget htup).2.2.2.2
    obtain ⟨t, htup, e, he, d, hd, heB, hqeq, hdNative, hfac⟩ :=
      OriginalPresievedActiveDeltaFactors.active_original_presieved_delta_factors
        hN heta E nu0 epsilon hwOrd hell hOrdNonzero
    have htOrd := (Finset.mem_filter.mp htup).1
    have hzdelta := zeta_cell_reserve eta htOrd
    have hcommon : (kappaMax n eta : ℝ) ≤
        (U1011OriginalSixteenNearCapBoxProfiles.delta
          (selectedPolicy n N t) (ownerBox n N t) eta : ℝ) / 64 := by
      exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell
        eta _ (owner_mem_selected (Finset.mem_filter.mp htOrd).2)
    have hd := hfac A hA hAupper kappa hk0 (hk.trans hcommon)
    let abc := U1011OriginalFifteenJointSmallBeta.attachedFactors
      (selectedPolicy n N t) (ownerBox n N t) eta N A t d e
    refine ⟨abc.1, abc.2.1, abc.2.2, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, ?_, ?_, ?_⟩
    · exact hd.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    · exact hd.2.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    · exact hd.2.2.2.2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
  · have hW : selectedPolicy n N m.1 = wPolicy := by
      apply Fin.ext
      have hlt := (selectedPolicy n N m.1).isLt
      dsimp [wPolicy]
      omega
    obtain ⟨e, he, d, hd, her, heActive, hdpos, hwell, htailprod, hfactor⟩ :=
      OriginalJointPresievedWFactors.active_joint_W_mark_factors
        hN heta hnu hepsilon heBudget E htuple hW hrow hq
    let B := ownerBox n N m.1
    let delt := (U1011OriginalW16NearCapNative.delta B eta : ℝ)
    have hdelta : (U1011OriginalSixteenNearCapBoxProfiles.delta
        (selectedPolicy n N m.1) B eta : ℝ) = delt := by
      rw [hW]
      simp only [delt, U1011OriginalSixteenNearCapBoxProfiles.delta,
        U1011OriginalSixteenNearCapBoxProfiles.G, U1011OriginalW16NearCapNative.delta,
        wPolicy, show ¬ (15 : ℕ) < 15 by omega, if_false]
    have hzdelta : 1024 * zeta n eta ≤ delt := by
      rw [← hdelta]
      exact zeta_cell_reserve eta htuple
    have hcommon : (kappaMax n eta : ℝ) ≤ delt / 64 := by
      rw [← hdelta]
      exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell
        eta _ (owner_mem_selected (Finset.mem_filter.mp htuple).2)
    have hkdelta : kappa ≤ delt := by linarith
    let tail := canonicalSlots N
      (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1))
      ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta m.1) d
    let abc := U1011OriginalW16JointSmallBeta.attachedFactors B eta N m.1 A tail e
    have hd := hfactor A hA hAupper
    have hmon := hd.2.2.2.2.2 kappa hk0 hkdelta
    refine ⟨abc.1, abc.2.1, abc.2.2, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, hd.2.2.2.2.1, ?_, ?_, ?_⟩
    · exact hmon.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    · exact hmon.2.1.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    · exact hmon.2.2.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
private theorem eventually_endpoint_power_in_chart {c t a b : ℝ}
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


private theorem endpoint_gates_of_reserves {N : ℕ} {x U z A a b c Q1 Q2 Q3 : ℝ}
    (hN : 0 < (N : ℝ)) (hx : 1 < x) (hz : 0 < z) (hU : 0 < U)
    (hA : A = innerQuery x U z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hQ1 : 0 < Q1) (hQ2 : 0 < Q2) (hQ3 : 0 < Q3)
    (hqa : Q1 ≤ x ^ (z / 100) * a) (hqb : Q2 ≤ x ^ (z / 100) * b)
    (hqc : Q3 ≤ x ^ (z / 100) * c) (haa : a ≤ A)
    (h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 3 * z))
    (h2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * z))
    (h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * z)) :
    NumericGates N x U Q1 Q2 Q3 (z / 2000) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hAp : 0 < A := by rw [hA, innerQuery]; positivity
  have hL : 0 < Real.log x := Real.log_pos hx
  have hAl : Real.log A = Real.log U - z * Real.log x := by
    rw [hA, innerQuery, Real.log_mul hU.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0]
    ring
  have hla := (Real.log_le_log_iff ha hAp).mpr haa
  have hl1 := (Real.le_rpow_iff_log_le (by positivity : 0 < A ^ 2 * b * c ^ 2) hx0).mp h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hb.ne'] at hl1
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
  have endpointLog {Q v : ℝ} (hQ : 0 < Q) (hv : 0 < v)
      (hbound : Q ≤ x ^ (z / 100) * v) :
      Real.log Q ≤ (z / 100) * Real.log x + Real.log v := by
    have hh := (Real.log_le_log_iff hQ (mul_pos (Real.rpow_pos_of_pos hx0 _) hv)).mpr hbound
    rwa [Real.log_mul (Real.rpow_pos_of_pos hx0 _).ne' hv.ne', Real.log_rpow hx0] at hh
  have hq1 := endpointLog hQ1 ha hqa
  have hq2 := endpointLog hQ2 hb hqb
  have hq3 := endpointLog hQ3 hc hqc
  have hzL := mul_pos hz hL
  unfold NumericGates
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Real.log_lt_log_iff hQ1 (mul_pos hU (Real.rpow_pos_of_pos hx0 _))).mp
    rw [Real.log_mul hU.ne' (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hQ2.ne', Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hQ1.ne',
      Real.log_mul (by positivity) hU.ne', Real.log_rpow hN, Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hQ1.ne',
      Real.log_rpow hU, Real.log_rpow hQ2, Real.log_rpow hQ3, Real.log_rpow hx0]
    nlinarith

/-- Actual constructor reserves pay a fixed whole-finebox endpoint budget.
The only remaining endpoint premises are geometric support bounds to be
supplied by a fixed group assignment. Medium gates are conclusions. -/
theorem exists_actual_all16_endpoint_medium_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) (nu0 epsilon : ℝ)
    (hnu : 0 < nu0) (hepsilon : 0 < epsilon)
    (heBudget : epsilon < epsilonBudget n eta nu0)
    {c C kappa kappa0 : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hk0 : 0 < kappa) (hk : kappa ≤ sigma n eta / 200)
    (ht0 : 0 < kappa0) (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    0 < endpointTau n eta ∧
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
      ∀ U : ℝ, x ^ (2 * zeta n eta) ≤ U → U ≤ x ^ (1 / 3 + zeta n eta / 2) →
      ∀ (E : ℕ × ℕ → Prop) (q : ℕ),
      jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E q ≠ 0 →
      ∃ a b c : ℕ, a * b * c = q ∧
        ∀ Q1 Q2 Q3 : ℝ,
          (a : ℝ) ≤ Q1 → Q1 ≤ 2 * (N : ℝ) ^ (endpointTau n eta) * a →
          (b : ℝ) ≤ Q2 → Q2 ≤ 2 * (N : ℝ) ^ (endpointTau n eta) * b →
          (c : ℝ) ≤ Q3 → Q3 ≤ 2 * (N : ℝ) ^ (endpointTau n eta) * c →
          1 ≤ Q1 ∧ 1 ≤ Q2 ∧ 1 ≤ Q3 ∧ NumericGates N x U Q1 Q2 Q3 (sigma n eta) := by
  obtain ⟨hz0, hzhi, _, _⟩ := analytic_choice_bounds n eta heta
  let z := zeta n eta
  have hz : 0 < z := hz0
  have hzu : z ≤ 1 / 128 := hzhi
  have htau : 0 < endpointTau n eta := by dsimp [endpointTau]; positivity
  refine ⟨htau, ?_⟩
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
  have hpay1 := eventually_endpoint_power_in_chart hc (by linarith : 0 ≤ 1 - 3 * z) hg1
  have hpay2 := eventually_endpoint_power_in_chart hc (by linarith : 0 ≤ 2 - 3 * z) hg2
  have htwo := eventually_const_mul_rpow_le_rpow 2 (by linarith :
    endpointTau n eta < 2 * endpointTau n eta)
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpay1.and (hpay2.and htwo))
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
  obtain ⟨a, b, c, hprod, haN, hbN, hcN, haA, h1, h2, h3⟩ :=
    actual_all16_reserved_factors hNN heta nu0 epsilon hnu hepsilon heBudget E
      hk0.le hkmax hA1 hAupper hq
  have ha : (0 : ℝ) < a := by exact_mod_cast haN
  have hb : (0 : ℝ) < b := by exact_mod_cast hbN
  have hc' : (0 : ℝ) < c := by exact_mod_cast hcN
  have hm1 := h1.trans (hpays.1 x hlow)
  have hm2big := h2.trans (hpays.2.1 x hlow)
  have hm2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * (a : ℝ) * (b : ℝ) ^ 5 * (c : ℝ) ^ 2 ≤
      x ^ (2 - 3 * z) := by
    have hspectral := Real.rpow_le_rpow_of_exponent_le hNr.le
      (by linarith : (7 / 32 : ℝ) ≤ 7 * (1 + 3 * kappa) / 32)
    have hh := mul_le_mul_of_nonneg_right hspectral
      (by positivity : 0 ≤ A * (a : ℝ) * (b : ℝ) ^ 5 * (c : ℝ) ^ 2)
    have hsmall : (N : ℝ) ^ (7 / 32 : ℝ) * A * (a : ℝ) * (b : ℝ) ^ 5 * (c : ℝ) ^ 2 ≤
        (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (a : ℝ) * (b : ℝ) ^ 5 * (c : ℝ) ^ 2 := by
      simpa only [mul_assoc] using hh
    exact hsmall.trans hm2big
  have hm3 := h3.trans (hpays.2.1 x hlow)
  have hksmall : kappa ≤ 1 / 8 := by linarith
  have hkzproduct := mul_le_mul_of_nonneg_right hksmall hz.le
  have hinflate : 2 * (N : ℝ) ^ (endpointTau n eta) ≤ x ^ (z / 100) := by
    calc
      _ ≤ (N : ℝ) ^ (2 * endpointTau n eta) := hpays.2.2
      _ ≤ (x ^ (1 + kappa)) ^ (2 * endpointTau n eta) :=
        Real.rpow_le_rpow hNp.le hhi (by positivity)
      _ = x ^ ((1 + kappa) * (2 * endpointTau n eta)) :=
        (Real.rpow_mul (zero_lt_one.trans hx).le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx.le (by
        dsimp [endpointTau]
        change (1 + kappa) * (2 * (z / 1000)) ≤ z / 100
        nlinarith)
  refine ⟨a, b, c, hprod, ?_⟩
  intro Q1 Q2 Q3 hQ1lo hQ1hi hQ2lo hQ2hi hQ3lo hQ3hi
  have hQ1 : 0 < Q1 := ha.trans_le hQ1lo
  have hQ2 : 0 < Q2 := hb.trans_le hQ2lo
  have hQ3 : 0 < Q3 := hc'.trans_le hQ3lo
  have hqa := hQ1hi.trans (mul_le_mul_of_nonneg_right hinflate ha.le)
  have hqb := hQ2hi.trans (mul_le_mul_of_nonneg_right hinflate hb.le)
  have hqc := hQ3hi.trans (mul_le_mul_of_nonneg_right hinflate hc'.le)
  have hQa : (1 : ℝ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hQb : (1 : ℝ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hQc : (1 : ℝ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
  exact ⟨hQa.trans hQ1lo, hQb.trans hQ2lo, hQc.trans hQ3lo,
    endpoint_gates_of_reserves hNp hx hz hUp rfl ha hb hc' hQ1 hQ2 hQ3
      hqa hqb hqc haA hm1 hm2 hm3⟩

end
end ImbalancedChen.P5Z.OriginalAllSixteenPresievedEndpointGates
