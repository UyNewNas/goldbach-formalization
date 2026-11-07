import ImbalancedChen.P5ZU1011OriginalFifteenDeltaMonomials
import ImbalancedChen.P5ZU1011SameRhoCompleteScaleSupport

/-!
# All four Medium numerical gates for actual ORIGINAL15 native factors

SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Fix eta, then choose zeta from the ACTUAL finite eta-native delta bank;
sigma=zeta/2000, and kappa is subsequently in the ORIGINAL analytic range
0<kappa<=sigma/200. For EVERY prescribed HB length in the original local
window x^(2*zeta)<=U<=x^(1/3+zeta/2), query A=U*x^(-zeta).
One threshold precedes N,x,U,outer masks and native marks. The existing
deterministic ORIGINAL15 factors prove ALL FOUR strict Medium numerical
inequalities, with the exact residue N^(7/32), together with the original
complete-product moving-residue range. No factor-size inequality is an
input to the public native-mark theorem.

This is not MediumAdmissible: atomwise fixed sequences, coefficient/SW
conditions, and the analytic estimate remain separate. No independent beta
is silently inserted into the native coefficient or its physical modulus.
-/

namespace ImbalancedChen.P5Z.U1011OriginalFifteenMediumNumericGates

noncomputable section
open Classical Filter
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenArithmeticProducts P5U1011JointOverlap
open U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (ownerBox selectedPolicy boxPolicy_certificate)
open U1011OriginalSixteenCommonSmallParameters (owner_mem_selected)
open U1011OriginalSixteenNearCapCommonSmallParameters (kappaMax cellDelta)
open U1011OriginalSixteenJointNearCapCompiler
open U1011OriginalSixteenJointNearCapModulusConvolution
open U1011OriginalFifteenJointSelectedCompletion (factors)

def zeta (n : ℕ) (eta : ℚ) : ℝ := (kappaMax n eta : ℝ) / 16
def sigma (n : ℕ) (eta : ℚ) : ℝ := zeta n eta / 2000
def innerQuery (x U z : ℝ) : ℝ := U * x ^ (-z)

def NumericGates (N : ℕ) (x U a b c s : ℝ) : Prop :=
  a < U * x ^ (-s) ∧ U ^ 2 * b * c ^ 2 < x ^ (1 - 8 * s) ∧
    (N : ℝ) ^ (7 / 32 : ℝ) * U * a * b ^ 5 * c ^ 2 < x ^ (2 - 15 * s) ∧
    U ^ (23 / 16 : ℝ) * a * b ^ (73 / 16 : ℝ) * c ^ (39 / 16 : ℝ) <
      x ^ (2 - 15 * s)

theorem analytic_choice_bounds (n : ℕ) (eta : ℚ) (heta : 0 < eta) :
    0 < zeta n eta ∧ zeta n eta ≤ 1 / 128 ∧
      0 < sigma n eta ∧ sigma n eta < 1 / 100 := by
  have hp : (0 : ℝ) < (kappaMax n eta : ℝ) := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_pos n eta heta
  have hu : (kappaMax n eta : ℝ) ≤ 1 / 8 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_eighth n eta
  dsimp [zeta, sigma]
  constructor
  · positivity
  constructor
  · linarith
  constructor <;> linarith

private theorem eventually_power_in_chart {c t a b : ℝ}
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

private theorem inner_query_range {x U z : ℝ} (hx : 1 < x) (hz : 0 < z)
    (hlo : x ^ (2 * z) ≤ U) (hhi : U ≤ x ^ (1 / 3 + z / 2)) :
    1 ≤ innerQuery x U z ∧ innerQuery x U z ≤ x ^ (1 / 3 - z / 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hp : 0 ≤ x ^ (-z) := Real.rpow_nonneg hx0.le _
  have hl : x ^ z ≤ innerQuery x U z := by
    have h := mul_le_mul_of_nonneg_right hlo hp
    simpa only [innerQuery, ← Real.rpow_add hx0,
      show 2 * z + -z = z by ring] using h
  have hu : innerQuery x U z ≤ x ^ (1 / 3 - z / 2) := by
    have h := mul_le_mul_of_nonneg_right hhi hp
    simpa only [innerQuery, ← Real.rpow_add hx0,
      show 1 / 3 + z / 2 + -z = 1 / 3 - z / 2 by ring] using h
  exact ⟨(Real.one_le_rpow hx.le hz.le).trans hl, hu⟩

private theorem numeric_of_local_reserves {N : ℕ} {x U z A a b c : ℝ}
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

/-- All original prescribed HB lengths have one native legal inner query
and all four strict Medium numerical gates. Same native physical modulus;
no independent small-prime factor is added to sigma. -/
theorem exists_original15_medium_numeric_threshold
    (n : ℕ) (eta : ℚ) (heta : 0 < eta) {c C kappa kappa0 : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hk0 : 0 < kappa)
    (hk : kappa ≤ sigma n eta / 200) (ht0 : 0 < kappa0)
    (ht : kappa0 < kappa / (4 * (1 + kappa))) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x → x ≤ C * N →
      1 < x ∧ C⁻¹ * x ≤ N ∧ (N : ℝ) ≤ x ^ (1 + kappa) ∧
      ∀ U : ℝ, x ^ (2 * zeta n eta) ≤ U → U ≤ x ^ (1 / 3 + zeta n eta / 2) →
      let A := innerQuery x U (zeta n eta)
      1 ≤ A ∧ A ≤ (N : ℝ) ^ (1 / 3 : ℝ) ∧
      ∀ (E : ℕ × ℕ → Prop) (m : Mark), m ∈ marks n N eta E →
      (selectedPolicy n N m.1).val < 15 →
      let abc := factors (selectedPolicy n N m.1) (ownerBox n N m.1) eta N A m.1 m.2
      abc.1 * abc.2.1 * abc.2.2 = modulus m ∧
        NumericGates N x U (abc.1 : ℝ) (abc.2.1 : ℝ) (abc.2.2 : ℝ) (sigma n eta) := by
  obtain ⟨hz0, hzhi, hs0, hshi⟩ := analytic_choice_bounds n eta heta
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
  obtain ⟨_, N1, hN1, hscale⟩ := exists_manuscript_restrictedResidueScale_threshold hc hC hk0 ht
  have hpay1 := eventually_power_in_chart hc (by linarith : 0 ≤ 1 - 3 * z) hg1
  have hpay2 := eventually_power_in_chart hc (by linarith : 0 ≤ 2 - 3 * z) hg2
  have hAend := eventually_const_mul_rpow_le_rpow (C ^ (1 / 3 - z / 2))
    (by linarith : 1 / 3 - z / 2 < (1 / 3 : ℝ))
  obtain ⟨N2, hN2⟩ := Filter.eventually_atTop.mp (hpay1.and (hpay2.and hAend))
  refine ⟨max N1 N2, hN1.trans (le_max_left _ _), ?_⟩
  intro N hN x hlow hupp
  have hNN : 1 < N := lt_of_lt_of_le (by omega : 1 < N1) ((le_max_left _ _).trans hN)
  have hNr : (1 : ℝ) < N := by exact_mod_cast hNN
  have hNp : (0 : ℝ) < N := zero_lt_one.trans hNr
  obtain ⟨hx, hlo, hhi⟩ := hscale N ((le_max_left _ _).trans hN) x hlow hupp
  have hpays := hN2 N ((le_max_right _ _).trans hN)
  refine ⟨hx, hlo, hhi, ?_⟩
  intro U hUlo hUhi
  have hUp : 0 < U := (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _).trans_le hUlo
  let A := innerQuery x U z
  obtain ⟨hA1, hAx⟩ := inner_query_range hx hz hUlo hUhi
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  have hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    calc
      _ ≤ x ^ (1 / 3 - z / 2) := hAx
      _ ≤ (C * (N : ℝ)) ^ (1 / 3 - z / 2) :=
        Real.rpow_le_rpow (zero_lt_one.trans hx).le hupp (by linarith)
      _ = C ^ (1 / 3 - z / 2) * (N : ℝ) ^ (1 / 3 - z / 2) := Real.mul_rpow hC.le hNp.le
      _ ≤ _ := hpays.2.2
  refine ⟨hA1, hAupper, ?_⟩
  intro E m hm hpolicy
  obtain ⟨htuple, hrow⟩ := Finset.mem_sigma.mp hm
  obtain ⟨_, hd⟩ := Finset.mem_filter.mp hrow
  obtain ⟨hsource, htag⟩ := Finset.mem_filter.mp htuple
  let p := selectedPolicy n N m.1
  let B := ownerBox n N m.1
  have hcert := (boxPolicy_certificate B htag).2
  have hgeom := owner_mem n (U1011OriginalFifteenJointNativeRows.joint_coordinates_cube hNN hsource)
  have hbox : coordinates N m.1 ∈ B.region := cell_subset_closed_box n _ hgeom
  have hcommon : (kappaMax n eta : ℝ) ≤
      (U1011OriginalSixteenNearCapBoxProfiles.delta p B eta : ℝ) / 64 := by
    exact_mod_cast U1011OriginalSixteenNearCapCommonSmallParameters.kappaMax_le_cell
      eta _ (owner_mem_selected htag)
  have hzdelta : 1024 * z ≤ (U1011OriginalSixteenNearCapBoxProfiles.delta p B eta : ℝ) := by
    dsimp [z, zeta]
    linarith
  have hdata := U1011OriginalFifteenDeltaMonomials.actual_fixed_factors_delta_monomials
    hNN hsource p hpolicy B eta heta (gridBox_valid n _) (gridBox_lower_positive n _ 3)
    hcert hbox hd A hA1 hAupper hk0.le (hkmax.trans hcommon)
  let abc := factors p B eta N A m.1 m.2
  have ha : (0 : ℝ) < abc.1 := by exact_mod_cast hdata.2.1
  have hb : (0 : ℝ) < abc.2.1 := by exact_mod_cast hdata.2.2.1
  have hc' : (0 : ℝ) < abc.2.2 := by exact_mod_cast hdata.2.2.2.1
  have hmono1 : A ^ 2 * (abc.2.1 : ℝ) * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (1 - 3 * z) :=
    (hdata.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.1 x hlow)
  have hmono2big : (N : ℝ) ^ (7 * (1 + 3 * kappa) / 32) * A * (abc.1 : ℝ) *
      (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hdata.2.2.2.2.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.2.1 x hlow)
  have hmono2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * (abc.1 : ℝ) *
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
    exact hsmall.trans hmono2big
  have hmono3 : (A * (abc.2.2 : ℝ) / (abc.2.1 : ℝ)) ^ (7 / 16 : ℝ) * A *
      (abc.1 : ℝ) * (abc.2.1 : ℝ) ^ 5 * (abc.2.2 : ℝ) ^ 2 ≤ x ^ (2 - 3 * z) :=
    (hdata.2.2.2.2.2.2.2.trans (Real.rpow_le_rpow_of_exponent_le hNr.le (by linarith))).trans
      (hpays.2.1 x hlow)
  exact ⟨hdata.1, numeric_of_local_reserves hNp hx hz hUp rfl ha hb hc'
    hdata.2.2.2.2.1 hmono1 hmono2 hmono3⟩

end
end ImbalancedChen.P5Z.U1011OriginalFifteenMediumNumericGates
