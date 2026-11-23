import ImbalancedChen.P3OriginalProperPowerChartPayment
import ImbalancedChen.P4BOriginalUpperFourierTailPaid

/-! The whole proper-power correction on the actual two original groups.
The threshold precedes every permitted physical width, policy, cap,
pre-HB order, and trim exponent. -/
namespace ImbalancedChen.P4BOriginalAllWidthProperPowers

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P4BOuterRampRoughness (baseline)
open P4BArbitraryWidthUpperPairProfile (licence nonzero_data legal_width_le_one)
open P4BActualUpperTrimPayment (actual_listExtension_bounds)
open P4BActualSmoothHyperbolaCorrection (actualActiveUpperCap)
open P5Z.ExactOriginalSmoothDyadicPartition (cutoffIndex chartBank)
open P5Z.OriginalDyadicRankUnion (words_card)
open P5Z.LicensedOriginalIntegerProfile (listExtension integerExtension listExtension_ofFn)
open P5Z.OriginalPrimeAllGroupHBDiscrepancy (properPowerReserve)
open P5Z.ProperPowerSignedMeanHBTransport (signedRow)
open P5Z.ProperPowerSignedModulusPayment (meanBudget rowBudget norm_signedRow_le)
open P5Z.ProperPowerPhysicalPolynomialPayment
open Part3.OriginalProperPowerActualChart (integerWords wordVector ofFn_wordVector)

/-- The prime floor and upper product wall also hold on positive
composite replacement words. -/
theorem integer_floor_and_product {b kappa nu r width : ℝ} (hb : 0 < b)
    (hk : 0 < kappa) (hnu : 0 < nu) (hr : 0 < r) (hw : 0 < width)
    (hg : 2*width ≤ baseline b kappa - nu*r) {N : ℕ}
    {ps : List ℕ} (hps : ps ∈ integerWords N 2)
    (ha : listExtension (licence hb hnu hr hw hg N) ps ≠ 0) :
    (∀ n ∈ ps, (N : ℝ)^(nu*r) ≤ (n : ℝ)) ∧ (ps.prod : ℝ) ≤ Real.exp 1 * N := by
  have hlen := (P5Z.ExactOriginalSmoothDyadicPartition.words_spec _ _ _ hps).1
  let u := wordVector 2 ps
  have heu : List.ofFn u = ps := ofFn_wordVector hlen
  have hact : P4BArbitraryWidthUpperPairProfile.profile b kappa width N
      (fun i => (u i : ℝ)) ≠ 0 := by
    change integerExtension (licence hb hnu hr hw hg N) u ≠ 0
    rw [← listExtension_ofFn, heu]
    exact ha
  have hs := nonzero_data hb hnu hr hw hg hact
  constructor
  · intro n hn
    have hm : n ∈ List.ofFn u := by simpa only [heu] using hn
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    simpa only [hi] using (hs.2.2.1 i).le
  · have he : (∏ i : Fin 2, (u i : ℝ)) = (ps.prod : ℝ) := by
      have hh := congrArg (fun xs : List ℕ => (xs.prod : ℝ)) heu
      simpa only [Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn] using hh
    rw [← he, Fin.prod_univ_two]
    exact hs.2.2.2.2.le.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (legal_width_le_one hb hk hnu hr hg)) (Nat.cast_nonneg _))

private def labelConstant : ℝ := 3 + 1 / Real.log 2

private theorem labelConstant_pos : 0 < labelConstant := by
  unfold labelConstant
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

private theorem original_labels {N : ℕ} (hN : 1 ≤ N) (hl : 1 ≤ Real.log (N : ℝ)) :
    ((cutoffIndex N + 2 : ℕ) : ℝ) ≤ labelConstant * Real.log (N : ℝ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn : N ≠ 0 := by omega
  have hpow : (2 : ℝ) ^ Nat.log2 N ≤ (N : ℝ) := by exact_mod_cast Nat.log2_self_le hn
  have h := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) _) hpow
  rw [Real.log_pow] at h
  have hj := (le_div_iff₀ h2).mpr h
  simp only [cutoffIndex, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, labelConstant]
  linarith only [hl, hj]

/-- After summing the norms over the actual chart bank, the entire
proper-power correction has arbitrary logarithmic accuracy. The unpooled
AP count and its exact coprime mean use the same attached coefficient. -/
theorem eventually_all_width_properPower_sum_norm
    (nu r theta : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (ht : 0 ≤ theta) (ht1 : theta < 1) (p : ℕ) (tolerance : ℝ)
    (htol : 0 < tolerance) :
    ∀ᶠ N : ℕ in atTop, ∀ (b kappa width : ℝ) (hb : 0 < b) (hk : 0 < kappa)
      (hw : 0 < width) (hg : 2*width ≤ baseline b kappa - nu*r)
      (K : ℕ) (t beta : ℝ) (f : ℕ → List ℕ → Bool) (cap : ℕ → ℕ),
      (actualActiveUpperCap nu r beta f cap N : ℝ) ≤ (N : ℝ)^theta →
      (∑ js ∈ chartBank N 2,
        ‖properPowerReserve (licence hb hnu hr hw hg N) K N N t
          (attachedUpperModuli nu r beta f cap N) (physicalRho nu r beta f cap N) js‖) ≤
        tolerance * (N : ℝ) / (Real.log (N : ℝ)) ^ p := by
  let a := nu*r
  let e := min (a/4) ((1-theta)/2)
  have ha : 0 < a := mul_pos hnu hr
  have he : 0 < e := lt_min (by positivity) (by linarith)
  have he1 : e ≤ a/4 := min_le_left _ _
  have he2 : e ≤ (1-theta)/2 := min_le_right _ _
  have hpow1 : 1-a/2+e < 1 := by linarith only [ha, he1]
  have hpow2 : theta+e < 1 := by linarith only [ht1, he2]
  obtain ⟨C, hC, hoff⟩ := physical_noncollision_signedRow_subpower he
  obtain ⟨D, hD, hdiag⟩ := physical_collision_factor_polynomial 2 ht he
  let U := Real.exp 1
  let E := C * (U+2)^e + 4*(1+theta/e)
  let F := 4 * (5 : ℝ)^2 * U * E
  have hU : 0 < U := Real.exp_pos _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℕ), eventually_one_le_nat_log,
    eventually_powerLog_le_logAccuracy (F * labelConstant^3) (1-a/2+e) 3 p hpow1
      (tolerance/2) (by positivity),
    eventually_powerLog_le_logAccuracy ((2*D) * labelConstant^2) (theta+e) 2 p hpow2
      (tolerance/2) (by positivity)] with N hN hl hpayO hpayD
  intro b kappa width hb hk hw hg K t beta f cap hcap
  let Q := attachedUpperModuli nu r beta f cap N
  let rho := physicalRho nu r beta f cap N
  let L := licence hb hnu hr hw hg N
  let J := ((cutoffIndex N + 2 : ℕ) : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hJ : J ≤ labelConstant * Real.log (N : ℝ) := original_labels hN hl
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  have hne : N ≠ 0 := by omega
  have hlow : (1 : ℝ) ≤ (N : ℝ)^e := Real.one_le_rpow hN1 he.le
  have hmean : 1+theta*Real.log (N : ℝ) ≤ (1+theta/e)*(N : ℝ)^e := by
    calc
      _ ≤ (N : ℝ)^e + theta*((N : ℝ)^e/e) := add_le_add hlow
        (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hN0.le he) ht)
      _ = _ := by ring
  have hrow (n : ℕ) (hn : 1 ≤ n) (hu : (n : ℝ) ≤ U * N) (hne' : n ≠ N) :
      ‖signedRow Q rho N n‖ ≤ E*(N : ℝ)^e := by
    have hp := hoff U hU theta nu r beta ht f cap N hN hcap n hn
      (by exact_mod_cast hu.trans (Nat.le_ceil _)) hne'
    calc
      _ ≤ (C*(U+2)^e)*(N : ℝ)^e + 4*(1+theta*Real.log (N : ℝ)) := hp
      _ ≤ (C*(U+2)^e)*(N : ℝ)^e + 4*((1+theta/e)*(N : ℝ)^e) := by linarith only [hmean]
      _ = _ := by dsimp [E]; ring
  have hdiag0 : ((N.divisors.card ^ 2 : ℕ) : ℝ) * ‖signedRow Q rho N N‖ ≤
      D * (N : ℝ)^(theta+e) := by
    have hh := norm_signedRow_le (physicalQ nu r beta f cap N) rho 1 zero_le_one
      (fun q _ => physicalRho_norm_le_one nu r beta f cap N q) N N
    have hd : ‖signedRow Q rho N N‖ ≤ ((physicalQ nu r beta f cap N).card : ℝ) +
        meanBudget (physicalQ nu r beta f cap N) rho := by
      rw [show signedRow Q rho N N = signedRow (physicalQ nu r beta f cap N) rho N N from
        physical_signedRow_eq_active nu r beta f cap N N]
      simpa only [rowBudget, if_pos rfl, one_mul] using hh
    exact (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg _)).trans
      (hdiag nu r beta f cap N 2 hN le_rfl hcap)
  have hsqrt : (N : ℝ) / Real.sqrt ((N : ℝ)^a) = (N : ℝ)^(1-a/2) := by
    simpa using Part3.AllKFamilyProperPowerSaving.physical_scale_power_identity
      (T := (N : ℝ)) (lower := 1) (a := a) hN0 zero_lt_one
  have hchart (js : List ℕ) (hjs : js ∈ chartBank N 2) :
      ‖properPowerReserve L K N N t Q rho js‖ ≤
        F*(N : ℝ)^(1-a/2+e)*J + (2*D)*(N : ℝ)^(theta+e) := by
    have hh := P3OriginalProperPowerChartPayment.actual_reserve_le hne L K t hjs Q rho
      (A := (N : ℝ)^a) (U := U) (M := 1) (H := E*(N : ℝ)^e)
      (Real.rpow_pos_of_pos hN0 _) hU.le zero_le_one (by positivity)
      (fun _ hps hact => integer_floor_and_product hb hk hnu hr hw hg hps hact)
      (fun ps => by
        have hwgt := actual_listExtension_bounds hb hnu hr hw hg N ps
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwgt.1] using hwgt.2)
      hrow
    calc
      _ ≤ _ := hh
      _ = F*((N : ℝ)/Real.sqrt ((N : ℝ)^a) * (N : ℝ)^e)*J +
          2*(((N.divisors.card ^ 2 : ℕ) : ℝ) * ‖signedRow Q rho N N‖) := by
        dsimp only [F, J]
        norm_num only [Nat.cast_ofNat, one_mul]
        ring
      _ ≤ F*(N : ℝ)^(1-a/2+e)*J + 2*(D*(N : ℝ)^(theta+e)) := by
        rw [hsqrt, ← Real.rpow_add hN0]
        linarith only [hdiag0]
      _ = _ := by ring
  have hc : ((chartBank N 2).card : ℝ) ≤ J^2 := by
    simp only [chartBank, words_card, Finset.card_range, Nat.cast_pow]
    apply pow_le_pow_left₀ (Nat.cast_nonneg _) _ 2
    exact_mod_cast (show cutoffIndex N+1 ≤ cutoffIndex N+2 by omega)
  have hraw : 0 ≤ F*(N : ℝ)^(1-a/2+e)*J + (2*D)*(N : ℝ)^(theta+e) := by positivity
  calc
    _ ≤ ∑ _js ∈ chartBank N 2,
        (F*(N : ℝ)^(1-a/2+e)*J + (2*D)*(N : ℝ)^(theta+e)) :=
      Finset.sum_le_sum hchart
    _ ≤ J^2 * (F*(N : ℝ)^(1-a/2+e)*J + (2*D)*(N : ℝ)^(theta+e)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hc hraw
    _ = F*(N : ℝ)^(1-a/2+e)*J^3 + (2*D)*(N : ℝ)^(theta+e)*J^2 := by ring
    _ ≤ F*(N : ℝ)^(1-a/2+e)*(labelConstant*Real.log (N : ℝ))^3 +
        (2*D)*(N : ℝ)^(theta+e)*(labelConstant*Real.log (N : ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hJ0 hJ 3) (by positivity))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hJ0 hJ 2) (by positivity))
    _ = (F*labelConstant^3)*(N : ℝ)^(1-a/2+e)*(Real.log (N : ℝ))^3 +
        ((2*D)*labelConstant^2)*(N : ℝ)^(theta+e)*(Real.log (N : ℝ))^2 := by ring
    _ ≤ _ := by linarith only [hpayO, hpayD]

end
end ImbalancedChen.P4BOriginalAllWidthProperPowers
