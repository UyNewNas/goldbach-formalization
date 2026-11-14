import ImbalancedChen.P5OriginalWWholeBoxRealRun
import ImbalancedChen.P5ZU1011OriginalW16FactorMonomials
import ImbalancedChen.Part3ActualWSmallThirdAttachment
import ImbalancedChen.P5ZU1011OriginalFifteenMediumNumericGates

-- SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
-- This uses the ACTUAL fixed W real-endpoint run, not the existing
-- tuple-specific natural completedBins. Success and first overflow are
-- both genuine outputs of the same endpoint trace.
namespace ImbalancedChen.P5Z.OriginalWWholeBoxEndpointMonomials
noncomputable section
open Classical
open U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenNearCapBoxProfiles
open OriginalNearCapRealEndpointGeometry OriginalWRealEndpointCapacities
open OriginalWWholeBoxRealRun
open Part3.ActualWThreeCapacityRun Part3.ActualWResidualCompletion
open Part3.ActualWSameKeyMonomials (Monomials monomials_downward)
open Part3.ActualWSmallThirdAttachment (third_attachment_monomials)
open U1011OriginalW16FactorMonomials (W_success_monomials)
open U1011OriginalFifteenMediumNumericGates (NumericGates innerQuery)
open Filter

/-- The fixed upper endpoint groups obey the three original W monomials
through BOTH actual outcomes of the endpoint completion. No M monomial is
assumed: the input is the computed run's trace and capacity disjunction. -/
theorem W_fixed_endpoint_monomials {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0)
    (v : Fin r → ℝ) (A : ℝ) (hA : 1 ≤ A)
    (hAupper : A ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (htrace : Trace (wSeed N u v A) (wInput r) (wGroups N B eta u v A))
    (hcases : Bounded (wWeight N u v) A (middleCapacity B eta N)
        (rightCapacity B eta N A) (wGroups N B eta u v A) ∨
      (middleCapacity B eta N < wp (wWeight N u v) (wGroups N B eta u v A).middle ∧
        wp (wWeight N u v) (wGroups N B eta u v A).middle ≤
          middleCapacity B eta N * (N : ℝ) ^ (u 2) ∧
        wp (wWeight N u v) (wGroups N B eta u v A).left ≤ A ∧
        wp (wWeight N u v) (wGroups N B eta u v A).right ≤
          runCapacity B eta N /
            (A * wp (wWeight N u v) (wGroups N B eta u v A).middle))) :
    let out := wGroups N B eta u v A
    Monomials (N : ℝ) (delta wPolicy B eta : ℝ) A
      (wp (wWeight N u v) out.left)
      (wp (wWeight N u v) out.middle)
      (wp (wWeight N u v) out.right) := by
  let out := wGroups N B eta u v A
  let w := wWeight N u v
  let a := wp w out.left
  let b := wp w out.middle
  let c := wp w out.right
  let d := (delta wPolicy B eta : ℝ)
  let nuW := (nu wPolicy B eta : ℝ)
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hp : (0 : ℝ) < N := zero_lt_one.trans hn
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hslot : ∀ q ∈ wInput r, 0 < w q := by
    intro q _
    exact Real.rpow_pos_of_pos hp _
  have hpositive := trace_positive w htrace
    (wSeed_positive hN u v A) hslot
  have ha : 0 < a := hpositive.1
  have hb : 0 < b := hpositive.2.1
  have hc' : 0 < c := hpositive.2.2
  have hd : 0 < d := by
    exact_mod_cast (rational_parameters wPolicy B eta hv hw hc heta).2.2.1
  have hdκ : (0 : ℝ) ≤ d / 64 := by linarith
  have hnu : nuW ≤ (153 / 256 : ℝ) :=
    (W_endpoint_initialization B eta hv hw hc heta u hlo hhi hu2 hu10
      (by norm_num : (0 : ℝ) ≤ 0) hdκ).1
  obtain ⟨_,_,_,_,_,hcritical⟩ := actual_W_real_capacity_inputs hN B eta
    hv hw hc heta u hlo hhi hu2 hu10 A hA hAupper
    (by norm_num : (0 : ℝ) ≤ 0) hdκ
  rcases hcases with hbounded | ⟨hlower,hupper,hleft,hright⟩
  · have haa : a ≤ A := hbounded.1
    have hbb : b ≤ (N : ℝ) ^ (2 * nuW - 1) := by
      simpa only [b,middleCapacity,nuW] using hbounded.2.1
    have hcc : c ≤ (N : ℝ) ^ (1 - nuW - 2 * d) / A := by
      simpa only [c,rightCapacity,d,nuW] using hbounded.2.2
    exact W_success_monomials hn hApos ha hb hc' hnu haa hbb hcc
  · have hupper' : b ≤ (N : ℝ) ^ actualSelectedSubproductUpper 1 nuW := by
      have hq := (hcritical (u 2) le_rfl)
      have hh : b ≤ (N : ℝ) ^ (actualSelectedSubproductUpper 1 nuW - d) := by
        exact hupper.trans (by simpa [middleCapacity,nuW,d] using hq)
      exact hh.trans (Real.rpow_le_rpow_of_exponent_le hn.le (by linarith))
    have hcap : A * b * c ≤ (N : ℝ) ^ (nuW - 2 * d) := by
      have hh := (le_div_iff₀ (mul_pos hApos hb)).mp hright
      simpa only [runCapacity,nuW,d] using (by nlinarith only [hh] :
        A * b * c ≤ runCapacity B eta N)
    have hblower : (N : ℝ) ^ (2 * nuW - 1) ≤ b := by
      simpa only [middleCapacity,nuW] using hlower.le
    exact selectedPair_monomials (α := (1 : ℝ)) hn hApos ha hb hc' hcap
      hblower hupper' hleft

/-- Attach the SAME common small beta bound only to the fixed third group.
The returned monomials have a positive half-delta reserve for local scaling. -/
theorem W_fixed_endpoint_beta_monomials {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (u : LogFour) (v : Fin r → ℝ) (A ell : ℝ)
    (hA : 0 < A) (hell : ell ≤ (delta wPolicy B eta : ℝ))
    (hmono : let out := wGroups N B eta u v A
      Monomials (N : ℝ) (delta wPolicy B eta : ℝ) A
        (wp (wWeight N u v) out.left)
        (wp (wWeight N u v) out.middle)
        (wp (wWeight N u v) out.right)) :
    let out := wGroups N B eta u v A
    Monomials (N : ℝ) ((delta wPolicy B eta : ℝ) / 2) A
      (wp (wWeight N u v) out.left)
      (wp (wWeight N u v) out.middle)
      ((N : ℝ) ^ ell * wp (wWeight N u v) out.right) := by
  let out := wGroups N B eta u v A
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hp : (0 : ℝ) < N := zero_lt_one.trans hn
  have hpos (l : List (Occ r)) : 0 < wp (wWeight N u v) l := by
    unfold wp
    apply List.prod_pos
    intro q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
    exact Real.rpow_pos_of_pos hp _
  exact third_attachment_monomials hn hA (hpos out.left) (hpos out.middle)
    (hpos out.right) (Real.rpow_pos_of_pos hp ell) le_rfl hell hmono

-- This conversion preserves the exact fourth M exponent. The third W
-- monomial has b in the denominator, but its net b exponent is 73/16.
theorem W_local_M_of_three_reserves {N : ℕ} {x U z A a b c : ℝ}
    (hN : 0 < (N : ℝ)) (hx : 1 < x) (hz : 0 < z)
    (hU : 0 < U) (hA : A = innerQuery x U z)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (haa : a ≤ A)
    (h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 3 * z))
    (h2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * z))
    (h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤ x ^ (2 - 3 * z)) :
    NumericGates N x U a b c (z / 2000) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hAp : 0 < A := by rw [hA,innerQuery]; positivity
  have hL : 0 < Real.log x := Real.log_pos hx
  have hAl : Real.log A = Real.log U - z * Real.log x := by
    rw [hA,innerQuery,Real.log_mul hU.ne' (Real.rpow_pos_of_pos hx0 _).ne',Real.log_rpow hx0]
    ring
  have hla := (Real.log_le_log_iff ha hAp).mpr haa
  have hl1 := (Real.le_rpow_iff_log_le (by positivity : 0 < A ^ 2 * b * c ^ 2) hx0).mp h1
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) hb.ne'] at hl1
  simp only [Real.log_pow] at hl1
  have hl2 := (Real.le_rpow_iff_log_le
    (by positivity : 0 < (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2) hx0).mp h2
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) ha.ne',
    Real.log_mul (by positivity) hAp.ne',Real.log_rpow hN] at hl2
  simp only [Real.log_pow] at hl2
  have hl3 := (Real.le_rpow_iff_log_le
    (by positivity : 0 < (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2) hx0).mp h3
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) ha.ne',
    Real.log_mul (by positivity) hAp.ne',Real.log_rpow (div_pos (mul_pos hAp hc) hb),
    Real.log_div (mul_ne_zero hAp.ne' hc.ne') hb.ne',Real.log_mul hAp.ne' hc.ne'] at hl3
  simp only [Real.log_pow] at hl3
  have hzL := mul_pos hz hL
  unfold NumericGates
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (Real.log_lt_log_iff ha (mul_pos hU (Real.rpow_pos_of_pos hx0 _))).mp
    rw [Real.log_mul hU.ne' (Real.rpow_pos_of_pos hx0 _).ne',Real.log_rpow hx0]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) hb.ne',Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) ha.ne',
      Real.log_mul (by positivity) hU.ne',Real.log_rpow hN,Real.log_rpow hx0]
    simp only [Real.log_pow]
    nlinarith
  · apply (Real.log_lt_log_iff (by positivity) (Real.rpow_pos_of_pos hx0 _)).mp
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) ha.ne',
      Real.log_rpow hU,Real.log_rpow hb,Real.log_rpow hc,Real.log_rpow hx0]
    nlinarith

/-- The SAME endpoint bins give every arithmetic tuple the attached W
monomials, with exact product and positive integer group lengths. -/
theorem W_fixed_actual_tuple_monomials {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (u : LogFour) (v : Fin r → ℝ) (A ell : ℝ)
    (hA : 0 < A) (hell : ell ≤ (delta wPolicy B eta : ℝ))
    (htrace : Trace (wSeed N u v A) (wInput r)
      (wGroups N B eta u v A))
    (hmono : let out := wGroups N B eta u v A
      Monomials (N : ℝ) ((delta wPolicy B eta : ℝ) / 2) A
        (wp (wWeight N u v) out.left)
        (wp (wWeight N u v) out.middle)
        ((N : ℝ) ^ ell * wp (wWeight N u v) out.right))
    (hleft : wp (wWeight N u v) (wGroups N B eta u v A).left ≤ A)
    (actual : Occ r → ℕ) (hactualPos : ∀ i, 0 < actual i)
    (hsize : ∀ i, (actual i : ℝ) ≤ wWeight N u v i)
    (e : ℕ) (hepos : 0 < e) (he : (e : ℝ) ≤ (N : ℝ) ^ ell) :
    let out := wGroups N B eta u v A
    let a := (out.left.map actual).prod
    let b := (out.middle.map actual).prod
    let c := e * (out.right.map actual).prod
    1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
      a * b * c = e * ((wholeLabels r).map actual).prod ∧
      (a : ℝ) ≤ A ∧
      Monomials (N : ℝ) ((delta wPolicy B eta : ℝ) / 2) A
        (a : ℝ) (b : ℝ) (c : ℝ) := by
  let out := wGroups N B eta u v A
  let a := (out.left.map actual).prod
  let b := (out.middle.map actual).prod
  let c := e * (out.right.map actual).prod
  let aa := wp (wWeight N u v) out.left
  let bb := wp (wWeight N u v) out.middle
  let cc := (N : ℝ) ^ ell * wp (wWeight N u v) out.right
  obtain ⟨haPos,hbPos,hcPos,hprod,haLe,hbLe,hcLe⟩ :=
    fixed_W_real_groups_all_tuples B eta u v A htrace actual hactualPos hsize e hepos
  have hn : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have hupos (l : List (Occ r)) : 0 < wp (wWeight N u v) l := by
    unfold wp
    apply List.prod_pos
    intro q hq
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
    exact Real.rpow_pos_of_pos hn _
  have haa : 0 < aa := hupos out.left
  have hbb : 0 < bb := hupos out.middle
  have hcc : 0 < cc := mul_pos (Real.rpow_pos_of_pos hn _) (hupos out.right)
  have hcUpper : (c : ℝ) ≤ cc := by
    exact hcLe.trans (mul_le_mul_of_nonneg_right he (hupos out.right).le)
  have hmain := monomials_downward hn hA
    (by exact_mod_cast (show 0 < a by omega))
    (by exact_mod_cast (show 0 < b by omega))
    (by exact_mod_cast (show 0 < c by omega))
    haa hbb hcc haLe hbLe hcUpper hmono
  exact ⟨haPos,hbPos,hcPos,hprod,haLe.trans hleft,hmain⟩

private theorem eventually_W_power_in_chart {c t a b : ℝ}
    (hc : 0 < c) (hb : 0 ≤ b) (hg : a < (1 - t) * b) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - t) ≤ x → (N : ℝ) ^ a ≤ x ^ b := by
  have hp : 0 < c ^ b := Real.rpow_pos_of_pos hc _
  filter_upwards [eventually_const_mul_rpow_le_rpow (c ^ b)⁻¹ hg] with N hN
  intro x hx
  have hpaid : (N : ℝ) ^ a ≤ c ^ b * (N : ℝ) ^ ((1 - t) * b) := by
    have hm := mul_le_mul_of_nonneg_left hN hp.le
    simpa only [← mul_assoc,mul_inv_cancel₀ hp.ne',one_mul] using hm
  calc
    _ ≤ c ^ b * (N : ℝ) ^ ((1 - t) * b) := hpaid
    _ = (c * (N : ℝ) ^ (1 - t)) ^ b := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _),
        ← Real.rpow_mul (Nat.cast_nonneg N)]
    _ ≤ x ^ b := Real.rpow_le_rpow
      (mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)) hx hb

/-- Fixed parameter order yields ONE threshold before N, local x, HB U,
the arithmetic tuple, beta integer and signed error are chosen. -/
theorem W_eventual_local_scale_payments {c d z kappa0 : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hz : 0 < z) (hzu : z ≤ 1 / 128)
    (hreserve : 1024 * z ≤ d) (hk0 : 0 ≤ kappa0) (hk : kappa0 ≤ z) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ x : ℝ,
      c * (N : ℝ) ^ (1 - kappa0) ≤ x →
      (N : ℝ) ^ (1 - 2 * d) ≤ x ^ (1 - 3 * z) ∧
      (N : ℝ) ^ (2 - 2 * d) ≤ x ^ (2 - 3 * z) ∧
      (N : ℝ) ^ (2 - 39 * d / 16) ≤ x ^ (2 - 3 * z) := by
  have hb1 : 0 ≤ 1 - 3 * z := by linarith
  have hb2 : 0 ≤ 2 - 3 * z := by linarith
  have hg1 : 1 - 2 * d < (1 - kappa0) * (1 - 3 * z) := by
    nlinarith [mul_nonneg hk0 hz.le]
  have hg2 : 2 - 2 * d < (1 - kappa0) * (2 - 3 * z) := by
    nlinarith [mul_nonneg hk0 hz.le]
  have hg3 : 2 - 39 * d / 16 < (1 - kappa0) * (2 - 3 * z) := by
    nlinarith [mul_nonneg hk0 hz.le]
  have h1 := eventually_W_power_in_chart hc hb1 hg1
  have h2 := eventually_W_power_in_chart hc hb2 hg2
  have h3 := eventually_W_power_in_chart hc hb2 hg3
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.mp ((h1.and h2).and h3)
  refine ⟨N0,?_⟩
  intro N hN x hx
  have hh := hN0 N hN
  exact ⟨hh.1.1 x hx,hh.1.2 x hx,hh.2 x hx⟩

/-- The three fixed W monomials plus the derived chart payments imply the
four strict M inequalities for every actual tuple, at the original zeta/
sigma hierarchy. The positive lengths and left bound are retained. -/
theorem W_actual_tuple_four_strict_M {N : ℕ} {x U z d A a b c : ℝ}
    (hN : 0 < (N : ℝ)) (hx : 1 < x) (hz : 0 < z) (hU : 0 < U)
    (hA : A = innerQuery x U z) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (haa : a ≤ A)
    (hmono : Monomials (N : ℝ) (d / 2) A a b c)
    (hpay1 : (N : ℝ) ^ (1 - 2 * d) ≤ x ^ (1 - 3 * z))
    (hpay2 : (N : ℝ) ^ (2 - 2 * d) ≤ x ^ (2 - 3 * z))
    (hpay3 : (N : ℝ) ^ (2 - 39 * d / 16) ≤ x ^ (2 - 3 * z)) :
    NumericGates N x U a b c (z / 2000) := by
  have h1 : A ^ 2 * b * c ^ 2 ≤ x ^ (1 - 3 * z) := by
    have hh : A ^ 2 * b * c ^ 2 ≤ (N : ℝ) ^ (1 - 2 * d) := by
      simpa only [Monomials,show 1 - 4 * (d / 2) = 1 - 2 * d by ring] using hmono.1
    exact hh.trans hpay1
  have h2 : (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
      x ^ (2 - 3 * z) := by
    have hh : (N : ℝ) ^ (7 / 32 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
        (N : ℝ) ^ (2 - 2 * d) := by
      simpa only [Monomials,show 2 - 4 * (d / 2) = 2 - 2 * d by ring] using hmono.2.1
    exact hh.trans hpay2
  have h3 : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
      x ^ (2 - 3 * z) := by
    have hh : (A * c / b) ^ (7 / 16 : ℝ) * A * a * b ^ 5 * c ^ 2 ≤
        (N : ℝ) ^ (2 - 39 * d / 16) := by
      simpa only [Monomials,show 2 - 39 * (d / 2) / 8 = 2 - 39 * d / 16 by ring]
        using hmono.2.2
    exact hh.trans hpay3
  exact W_local_M_of_three_reserves hN hx hz hU hA ha hb hc haa h1 h2 h3

/-- One W partition is fixed by the WHOLE padded box and HB length. Every
positive tuple below those endpoint labels receives the SAME three lists,
exact modulus product and all four strict local medium gates. -/
theorem W_fixed_box_every_tuple_M {r N : ℕ} (hN : 1 < N)
    (B : Box) (eta : ℚ) (hv : B.Valid) (hw : 0 < B.lo 3)
    (hc : wholeBoxEligibleTest wPolicy B = true) (heta : 0 < eta)
    (u : LogFour) (hlo : ∀ i, (B.lo i : ℝ) ≤ u i)
    (hhi : ∀ i, u i ≤ (B.hi i : ℝ) + endpointPadding wPolicy B eta)
    (hu2 : 0 ≤ u 2) (hu10 : u 1 ≤ u 0) (hu32 : u 3 ≤ u 2)
    (v : Fin r → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hvanti : Antitone v)
    (hvlate : ∀ i, v i ≤ u 2) (roughWidth : ℝ)
    (hrw : roughWidth ≤ (delta wPolicy B eta : ℝ))
    (hcubes : ∀ i : Fin r, Even i.val → PresievedRoughSlotAffineGates.cube v i <
      (physicalResidual wPolicy B eta : ℝ) + roughWidth)
    {x U z ell : ℝ} (hx : 1 < x) (hz : 0 < z) (hU : 0 < U)
    (hA1 : 1 ≤ innerQuery x U z)
    (hAupper : innerQuery x U z ≤ (N : ℝ) ^ (1 / 3 : ℝ))
    (hell : ell ≤ (delta wPolicy B eta : ℝ))
    (hpay1 : (N : ℝ) ^ (1 - 2 * (delta wPolicy B eta : ℝ)) ≤ x ^ (1 - 3 * z))
    (hpay2 : (N : ℝ) ^ (2 - 2 * (delta wPolicy B eta : ℝ)) ≤ x ^ (2 - 3 * z))
    (hpay3 : (N : ℝ) ^ (2 - 39 * (delta wPolicy B eta : ℝ) / 16) ≤ x ^ (2 - 3 * z))
    (actual : Occ r → ℕ) (hactualPos : ∀ i, 0 < actual i)
    (hsize : ∀ i, (actual i : ℝ) ≤ wWeight N u v i)
    (e : ℕ) (hepos : 0 < e) (he : (e : ℝ) ≤ (N : ℝ) ^ ell) :
    let A := innerQuery x U z
    let out := wGroups N B eta u v A
    let a := (out.left.map actual).prod
    let b := (out.middle.map actual).prod
    let c := e * (out.right.map actual).prod
    1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧
      a * b * c = e * ((wholeLabels r).map actual).prod ∧
      NumericGates N x U (a : ℝ) (b : ℝ) (c : ℝ) (z / 2000) := by
  let A := innerQuery x U z
  let out := wGroups N B eta u v A
  let a := (out.left.map actual).prod
  let b := (out.middle.map actual).prod
  let c := e * (out.right.map actual).prod
  let d := (delta wPolicy B eta : ℝ)
  have hAp : 0 < A := zero_lt_one.trans_le hA1
  obtain ⟨htrace,_,hcases⟩ := fixed_W_real_endpoint_run hN B eta hv hw hc heta
    u hlo hhi hu2 hu10 hu32 v hv0 hvanti hvlate roughWidth hrw hcubes
    A hA1 hAupper
  have hleft : wp (wWeight N u v) out.left ≤ A := by
    rcases hcases with hbounded | hstop
    · exact hbounded.1
    · exact hstop.2.2.1
  have hW := W_fixed_endpoint_monomials hN B eta hv hw hc heta u hlo hhi
    hu2 hu10 v A hA1 hAupper htrace hcases
  have hbeta := W_fixed_endpoint_beta_monomials hN B eta u v A ell hAp hell hW
  obtain ⟨haPos,hbPos,hcPos,hprod,haa,hmono⟩ := W_fixed_actual_tuple_monomials
    hN B eta u v A ell hAp hell htrace hbeta hleft actual hactualPos hsize e hepos he
  have hNr : (0 : ℝ) < N := by exact_mod_cast (zero_lt_one.trans hN)
  have ha : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hc' : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  exact ⟨haPos,hbPos,hcPos,hprod,
    W_actual_tuple_four_strict_M hNr hx hz hU rfl ha hb hc' haa hmono
      hpay1 hpay2 hpay3⟩

end
end ImbalancedChen.P5Z.OriginalWWholeBoxEndpointMonomials
