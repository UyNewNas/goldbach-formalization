import ImbalancedChen.P5OriginalPresievedMediumNumericGates
import ImbalancedChen.P5OriginalJointPresievedWFactors

/-!
# The distinct W marks of the actual ALL16 presieved coefficient: Medium gates
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The actual nonzero W mark supplies its own small e, rough d and canonical
original rough tail through the explicit ALL16 common-beta compiler.
Existing W completed factors, with e only in group3, pay ALL FOUR strict
Medium NUMERICAL gates throughout the ORIGINAL prescribed HB window.
The exact physical modulus and residue N^(7/32) are retained. Zeta is the
same eta-dependent finite-bank choice as for ordinary15. No old-sigma
identification, whole-atom partition, auxiliary SW or PP is claimed.
-/

namespace ImbalancedChen.P5Z.OriginalJointPresievedWMediumNumericGates
noncomputable section
open Classical Filter
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox)
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax)
open U1011OriginalFifteenMediumNumericGates
open OriginalCommonBetaActualParameters
open OriginalOrdinaryPresievedSigma
open OriginalJointPresievedCompiler
open OriginalPresievedRoughPrimeSlots (canonicalSlots)
private theorem eventually_W_power_in_chart {c t a b : ℝ}
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

private theorem W_numeric_of_local_reserves {N : ℕ} {x U z A a b c : ℝ}
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


/-- Actual distinct-W coefficient eligibility at every original HB length.
The supplied mark membership and nonzero coefficient concern the actual
ALL16 presievedSigma; no factor-size conclusion is assumed. -/
theorem exists_W_medium_numeric_threshold
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
      ∀ (E : ℕ × ℕ → Prop) (t : Four) (r : ℕ),
      t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E →
      selectedPolicy n N t = wPolicy →
      r ∈ rowSupport n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2)) t →
      jointPresievedSigma n N eta ((N : ℝ) ^ (nu0 * epsilon ^ 2))
        ((N : ℝ) ^ (nu0 * epsilon)) E (fullPrefix t * r) ≠ 0 →
      ∃ a b c : ℕ, a * b * c = fullPrefix t * r ∧
        NumericGates N x U (a : ℝ) (b : ℝ) (c : ℝ) (sigma n eta) := by
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
  have hpay1 := eventually_W_power_in_chart hc (by linarith : 0 ≤ 1 - 3 * z) hg1
  have hpay2 := eventually_W_power_in_chart hc (by linarith : 0 ≤ 2 - 3 * z) hg2
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpay1.and hpay2)
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N1) ((le_max_left _ _).trans hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨hx, hlo, hhi, hquery⟩ := hnative N ((le_max_left _ _).trans hN) x hlow hupp
  have hpays := hN2 N ((le_max_right _ _).trans hN)
  refine ⟨hx, hlo, hhi, ?_⟩
  intro U hUlo hUhi E t r htup hW hr hq
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _).trans_le hUlo
  let A := innerQuery x U z
  obtain ⟨hA1, hAupper, _⟩ := hquery U hUlo hUhi
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  obtain ⟨e, he, d, hd, her, heActive, hdpos, hwell, htailprod, hfactor⟩ :=
    OriginalJointPresievedWFactors.active_joint_W_mark_factors
      hNN heta hnu hepsilon heBudget E htup hW hr hq
  let B := ownerBox n N t
  let delt := (U1011OriginalW16NearCapNative.delta B eta : ℝ)
  have hdelta : (U1011OriginalSixteenNearCapBoxProfiles.delta
      (selectedPolicy n N t) B eta : ℝ) = delt := by
    rw [hW]
    simp only [delt, U1011OriginalSixteenNearCapBoxProfiles.delta,
      U1011OriginalSixteenNearCapBoxProfiles.G, U1011OriginalW16NearCapNative.delta,
      wPolicy, show ¬ (15 : ℕ) < 15 by omega, if_false]
  have htag := (Finset.mem_filter.mp htup).2
  have hcommon : (kappaMax n eta : ℝ) ≤ delt / 64 := by
    rw [← hdelta]
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell
      eta _ (owner_mem_selected htag)
  have hzdelta : 1024 * z ≤ delt := by dsimp [z, zeta]; linarith
  have hkdelta : kappa ≤ delt := by linarith
  let tail := canonicalSlots N
    (Nat.ceil (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t))
    ((N : ℝ) ^ (nu0 * epsilon ^ 2)) (U1011OriginalSixteenJointNearCapCompiler.Z n N eta t) d
  let abc := U1011OriginalW16JointSmallBeta.attachedFactors B eta N t A tail e
  have hdata := hfactor A hA1 hAupper
  have hmon := hdata.2.2.2.2.2 kappa hk0.le hkdelta
  have ha : (0 : ℝ) < abc.1 := by exact_mod_cast hdata.2.1
  have hb : (0 : ℝ) < abc.2.1 := by exact_mod_cast hdata.2.2.1
  have hc' : (0 : ℝ) < abc.2.2 := by exact_mod_cast hdata.2.2.2.1
  have hm1 : A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - 3 * z) :=
    (hmon.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.1 x hlow)
  have hm2big : (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
      (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hmon.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
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
    (hmon.2.2.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.2 x hlow)
  exact ⟨abc.1, abc.2.1, abc.2.2, hdata.1,
    W_numeric_of_local_reserves hNp hx hz hUp rfl ha hb hc'
      hdata.2.2.2.2.1 hm1 hm2 hm3⟩

end
end ImbalancedChen.P5Z.OriginalJointPresievedWMediumNumericGates
