import ImbalancedChen.P5U7ComponentLeadingIntegrals
import ImbalancedChen.P5U7TerminalPrimeInterior

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT.
The actual terminal-window supplier is consumed on the same marked strict
selector. A genuine prime-box test and exact denominator correction prove
the separate prime mean. Subtraction from the actual full interior mean
then proves the ordered-semiprime mean; neither component mean is assumed.
All arithmetic limits fix positive eta before taking N to infinity.
-/
namespace ImbalancedChen
noncomputable section
open Filter Topology Set MeasureTheory
open scoped BigOperators
open Classical

def p5U7PrimeLeadingTest (x : Fin 2 → ℝ) : ℝ :=
  1 / max (59/250 : ℝ) (1 - x 0 - x 1)

def p5U7PrimeLeadingIntegral (eta : ℝ) : ℝ :=
  ∫ x in p5U7EtaDomain eta, p5U7ComponentPrimeKernel (x 0) (x 1)

def p5U7SemiprimeLeadingIntegral (eta : ℝ) : ℝ :=
  ∫ x in p5U7EtaDomain eta, p5U7ComponentSemiprimeKernel (x 0) (x 1)

def p5U7PrimeLeadingShiftedSum (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    (1/((t.1 : ℝ)-1)) * (1/((t.2 : ℝ)-1)) *
      p5U7PrimeLeadingTest (actualPrimeTupleLog N ![t.1,t.2])

def p5U7PrimeLeadingRawSum (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    (1/((t.1 : ℝ)*(t.2 : ℝ))) *
      p5U7PrimeLeadingTest (actualPrimeTupleLog N ![t.1,t.2])

def p5U7PrimeLeadingMain (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ t ∈ p5U7InteriorSelector N eta,
    ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) / Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ))

theorem continuous_p5U7PrimeLeadingTest : Continuous p5U7PrimeLeadingTest := by
  apply continuous_const.div
    (continuous_const.max ((continuous_const.sub (continuous_apply 0)).sub (continuous_apply 1)))
  intro x
  exact (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _)).ne'

theorem p5U7PrimeLeadingTest_nonneg (x : Fin 2 → ℝ) : 0 ≤ p5U7PrimeLeadingTest x := by
  exact one_div_nonneg.mpr ((by norm_num : (0 : ℝ) ≤ 59/250).trans (le_max_left _ _))

theorem p5U7PrimeLeading_domain_geometry {eta : ℝ} (heta : 0 ≤ eta)
    {x : Fin 2 → ℝ} (hx : x ∈ p5U7EtaDomain eta) :
    p5U7OmegaClosedSupport (x 0) (x 1) ∧ (59/250 : ℝ) ≤ 1 - x 0 - x 1 := by
  have hs := p5U7Interior_subset_original heta hx.1 hx.2
  refine ⟨⟨hs.1,hs.2.1,hs.2.2.le⟩, ?_⟩
  have hu := (mem_logPrimeBox.mp hx.1) 1
  linarith only [hu.1,hs.2.2]

theorem p5U7PrimeLeadingTest_eq {eta : ℝ} (heta : 0 ≤ eta)
    {x : Fin 2 → ℝ} (hx : x ∈ p5U7EtaDomain eta) :
    p5U7PrimeLeadingTest x = 1/(1-x 0-x 1) := by
  rw [p5U7PrimeLeadingTest,max_eq_right (p5U7PrimeLeading_domain_geometry heta hx).2]

theorem p5U7PrimeLeading_density_integral (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ x in p5U7EtaDomain eta, p5U7PrimeLeadingTest x * ∏ i, 1/x i) =
      p5U7PrimeLeadingIntegral eta := by
  unfold p5U7PrimeLeadingIntegral
  apply setIntegral_congr_fun (measurableSet_p5U7EtaDomain eta)
  intro x hx
  rw [p5U7PrimeLeadingTest_eq heta hx]
  simp only [Fin.prod_univ_two,p5U7ComponentPrimeKernel,div_eq_mul_inv,mul_inv_rev]
  ring

/-- Actual box transport for the prime leading test, independent of any
terminal-window asymptotic. -/
theorem tendsto_p5U7PrimeLeadingShiftedSum (eta : ℝ) (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => p5U7PrimeLeadingShiftedSum N eta) atTop
      (𝓝 (p5U7PrimeLeadingIntegral eta)) := by
  let B := fun N : ℕ => actualPrimeBoxTestSum N
    (fun _ : Fin 2 => (59/250 : ℝ)) (fun _ => (1/2 : ℝ))
      ((p5U7InteriorRegion eta).indicator p5U7PrimeLeadingTest)
  have hB : Tendsto B atTop (𝓝 (p5U7PrimeLeadingIntegral eta)) := by
    rw [← p5U7PrimeLeading_density_integral eta heta]
    exact tendsto_actualPrimeBoxTestSum_cube_affineGates (by norm_num) (by norm_num)
      (p5U7InteriorForms eta) p5U7InteriorBounds (p5U7InteriorForms_ne_zero eta)
      p5U7PrimeLeadingTest continuous_p5U7PrimeLeadingTest.continuousOn
  apply hB.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  let T := (actualPrimeBoxTuples N
    (fun _ : Fin 2 => (59/250 : ℝ)) (fun _ => (1/2 : ℝ))).filter
      (fun p => actualPrimeTupleLog N p ∈ p5U7InteriorRegion eta)
  have hsum : p5U7PrimeLeadingShiftedSum N eta =
      ∑ p ∈ T, (∏ i, 1/((p i : ℝ)-1)) * p5U7PrimeLeadingTest (actualPrimeTupleLog N p) := by
    unfold p5U7PrimeLeadingShiftedSum
    refine Finset.sum_bij (fun t _ => ![t.1,t.2]) ?_ ?_ ?_ ?_
    · intro t ht
      exact (p5U7Interior_selector_iff_box hN heta ![t.1,t.2]).mp ht
    · intro t _ u _ htu
      apply Prod.ext
      · simpa using congrFun htu 0
      · simpa using congrFun htu 1
    · intro p hp
      refine ⟨(p 0,p 1),(p5U7Interior_selector_iff_box hN heta p).mpr hp,?_⟩
      funext i
      fin_cases i <;> rfl
    · intro t _
      simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
      ring
  rw [hsum]
  dsimp only [B,actualPrimeBoxTestSum,T]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : actualPrimeTupleLog N p ∈ p5U7InteriorRegion eta
  · rw [if_pos hp,indicator_of_mem hp]
  · rw [if_neg hp,indicator_of_notMem hp,mul_zero]

/-- Actual finite shifted-to-raw correction for the prime leading test. -/
theorem p5U7PrimeLeading_shifted_raw_bound {N : ℕ} (hN : 2 ≤ N) (eta : ℝ) :
    0 ≤ p5U7PrimeLeadingShiftedSum N eta - p5U7PrimeLeadingRawSum N eta ∧
      p5U7PrimeLeadingShiftedSum N eta - p5U7PrimeLeadingRawSum N eta ≤
        (2/(N : ℝ)^(59/250 : ℝ)) * p5U7PrimeLeadingShiftedSum N eta := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hD := Real.rpow_pos_of_pos hNR (59/250 : ℝ)
  have hrow (t : ℕ × ℕ) (ht : t ∈ p5U7InteriorSelector N eta) :
      let A := (1/((t.1 : ℝ)-1))*(1/((t.2 : ℝ)-1))
      let R := 1/((t.1 : ℝ)*(t.2 : ℝ))
      let H := p5U7PrimeLeadingTest (actualPrimeTupleLog N ![t.1,t.2])
      0 ≤ A*H-R*H ∧ A*H-R*H ≤ (2/(N : ℝ)^(59/250 : ℝ))*(A*H) := by
    obtain ⟨hsel,_⟩ := Finset.mem_filter.mp ht
    obtain ⟨hc,hDa,ho,_⟩ := Finset.mem_filter.mp hsel
    obtain ⟨hc1,hc2⟩ := Finset.mem_product.mp hc
    have hp := (mem_chenAdditivePrimeCarrier.mp hc1).2.1
    have hq := (mem_chenAdditivePrimeCarrier.mp hc2).2.1
    have hDb : (N : ℝ)^(59/250 : ℝ) ≤ t.2 := hDa.trans (by exact_mod_cast ho.le)
    have hw := p5U7_pair_weight_correction_bound hD
      (by exact_mod_cast hp.one_lt) (by exact_mod_cast hq.one_lt) hDa hDb
    have hH := p5U7PrimeLeadingTest_nonneg (actualPrimeTupleLog N ![t.1,t.2])
    dsimp only
    constructor
    · nlinarith [mul_nonneg hw.1 hH]
    · have hm := mul_le_mul_of_nonneg_right hw.2 hH
      nlinarith only [hm]
  unfold p5U7PrimeLeadingShiftedSum p5U7PrimeLeadingRawSum
  rw [← Finset.sum_sub_distrib]
  exact ⟨Finset.sum_nonneg (fun t ht => (hrow t ht).1), by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun t ht => (hrow t ht).2)⟩

theorem tendsto_p5U7PrimeLeadingRawSum (eta : ℝ) (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => p5U7PrimeLeadingRawSum N eta) atTop
      (𝓝 (p5U7PrimeLeadingIntegral eta)) := by
  have hp : Tendsto (fun N : ℕ => 2/(N : ℝ)^(59/250 : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_nat_log_pow_div_rpow 0 (by norm_num : (0 : ℝ) < 59/250)).const_mul (2 : ℝ)
    simpa only [pow_zero,mul_div_assoc,mul_one,mul_zero] using h
  have hs := tendsto_p5U7PrimeLeadingShiftedSum eta heta
  have he : Tendsto (fun N : ℕ => p5U7PrimeLeadingShiftedSum N eta -
      p5U7PrimeLeadingRawSum N eta) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (by simpa only [zero_mul] using hp.mul hs)
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      exact (p5U7PrimeLeading_shifted_raw_bound hN eta).1
    · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
      exact (p5U7PrimeLeading_shifted_raw_bound hN eta).2
  simpa only [sub_sub_cancel,sub_zero] using hs.sub he

/-- Exact original logarithmic normalization of the prime leading main. -/
theorem p5U7PrimeLeadingMain_normalized {N : ℕ} (hN : 2 ≤ N) (eta : ℝ)
    (heta : 0 ≤ eta) :
    (Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta =
      p5U7PrimeLeadingRawSum N eta := by
  unfold p5U7PrimeLeadingMain p5U7PrimeLeadingRawSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  have hb := (p5U7Interior_selector_iff_box hN heta ![t.1,t.2]).mp ht
  obtain ⟨hb,hi⟩ := Finset.mem_filter.mp hb
  have hlogbox := ((mem_actualPrimeBoxTuples_log_iff (show 1 < N by omega) _ _ ![t.1,t.2]).mp hb).2
  rw [p5U7PrimeLeadingTest_eq heta ⟨hlogbox,hi⟩]
  have hg := p5U7Mass_outer_geometry (Finset.mem_filter.mp ht).1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  obtain ⟨hp,hq⟩ := Finset.mem_product.mp hc
  have hp0 : (0 : ℝ) < t.1 := by exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq0 : (0 : ℝ) < t.2 := by exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  have hpq0 : (0 : ℝ) < ((t.1*t.2 : ℕ) : ℝ) := by exact_mod_cast hg.1
  have hx1 : (1 : ℝ) < (N : ℝ)/((t.1*t.2 : ℕ) : ℝ) :=
    (by exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hq).2.1.one_lt).trans hg.2.2.1
  have hLX : Real.log ((N : ℝ)/((t.1*t.2 : ℕ) : ℝ)) ≠ 0 := (Real.log_pos hx1).ne'
  have hGap0 := (p5U7PrimeLeading_domain_geometry heta ⟨hlogbox,hi⟩).2
  change (59/250 : ℝ) ≤ 1 - Real.log (t.1 : ℝ)/Real.log (N : ℝ) -
    Real.log (t.2 : ℝ)/Real.log (N : ℝ) at hGap0
  have hGap : 1 - Real.log (t.1 : ℝ)/Real.log (N : ℝ) -
      Real.log (t.2 : ℝ)/Real.log (N : ℝ) ≠ 0 := by linarith only [hGap0]
  simp only [actualPrimeTupleLog,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [Nat.cast_mul,Real.log_div hNR.ne' (mul_ne_zero hp0.ne' hq0.ne'),Real.log_mul hp0.ne' hq0.ne'] at hLX ⊢
  field_simp [hNR.ne',hp0.ne',hq0.ne',hLN,hLX,hGap]
  <;> ring

theorem tendsto_p5U7PrimeLeadingMain_normalized (eta : ℝ) (heta : 0 ≤ eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta)
      atTop (𝓝 (p5U7PrimeLeadingIntegral eta)) := by
  apply (tendsto_p5U7PrimeLeadingRawSum eta heta).congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  exact (p5U7PrimeLeadingMain_normalized hN eta heta).symm

/-- The actual terminal supplier, not an assumed prime mean, is now
summed and normalized. Eta is positive and fixed before the N threshold. -/
theorem tendsto_p5U7ActualInteriorThree_normalized (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ActualInteriorThree N eta).card : ℝ)) atTop
        (𝓝 (p5U7PrimeLeadingIntegral eta)) := by
  have hB := tendsto_p5U7PrimeLeadingMain_normalized eta heta.le
  apply Metric.tendsto_nhds.2
  intro epsilon he
  let C : ℝ := |p5U7PrimeLeadingIntegral eta| + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let delta : ℝ := epsilon/(4*C)
  have hd : 0 < delta := div_pos he (by positivity)
  have hbnd := hB.eventually (Iio_mem_nhds (show p5U7PrimeLeadingIntegral eta < C by
    dsimp only [C]; linarith only [le_abs_self (p5U7PrimeLeadingIntegral eta)]))
  have hnear := Metric.tendsto_nhds.mp hB (epsilon/2) (by positivity)
  filter_upwards [p5U7TerminalPrime_eventually_subfamily_error eta delta heta hd,
    hbnd,hnear,eventually_ge_atTop (2 : ℕ)] with N hw hb hn hN
  have hw := hw _ (p5U7InteriorSelector_subset_band hN eta)
  have hnorm : 0 ≤ Real.log (N : ℝ)/(N : ℝ) :=
    div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have hh := mul_le_mul_of_nonneg_left hw hnorm
  have hcard : ((p5U7ActualInteriorThree N eta).card : ℝ) =
      ∑ t ∈ p5U7InteriorSelector N eta,
        ((p5U7MassPrimeFibre N (t.1*t.2) t.2).card : ℝ) := by
    simp only [p5U7ActualInteriorThree,Finset.card_sigma,Nat.cast_sum]
  have herr : |(Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualInteriorThree N eta).card : ℝ) -
      (Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta| ≤
        delta*((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta) := by
    rw [hcard,p5U7PrimeLeadingMain]
    rw [← mul_sub,abs_mul,abs_of_nonneg hnorm]
    nlinarith only [hh]
  have hsmall : delta*((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta) < epsilon/4 := by
    have hm := mul_lt_mul_of_pos_left hb hd
    have heq : delta*C = epsilon/4 := by dsimp only [delta]; field_simp [hC.ne']; ring
    exact hm.trans_eq heq
  rw [Real.dist_eq] at hn ⊢
  have htri0 := abs_add_le
    ((Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualInteriorThree N eta).card : ℝ) -
      (Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta)
    ((Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta - p5U7PrimeLeadingIntegral eta)
  have htri : |(Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualInteriorThree N eta).card : ℝ) -
      p5U7PrimeLeadingIntegral eta| ≤
      |(Real.log (N : ℝ)/(N : ℝ))*((p5U7ActualInteriorThree N eta).card : ℝ) -
        (Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta| +
      |(Real.log (N : ℝ)/(N : ℝ))*p5U7PrimeLeadingMain N eta - p5U7PrimeLeadingIntegral eta| := by
    convert htri0 using 1 <;> congr 1 <;> ring
  linarith only [herr,hsmall,hn,htri]

/-- The ordered-semiprime branch has its OWN fixed-interior leading
limit, obtained by subtracting the actual prime mass on the same selector. -/
theorem tendsto_p5U7ActualInteriorFour_normalized_sub (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ActualInteriorFour N eta).card : ℝ)) atTop
        (𝓝 (p5U7InteriorOmegaIntegral eta-p5U7PrimeLeadingIntegral eta)) := by
  have h := (tendsto_p5U7ActualInteriorSourceMass_normalized eta heta).sub
    (tendsto_p5U7ActualInteriorThree_normalized eta heta)
  convert h using 1
  funext N
  rw [← p5U7ActualInterior_label_mass_eq_rows]
  ring

/-- Proved integrability identifies the subtraction constant with the
literal ordered-semiprime kernel, rather than renaming the full source. -/
theorem p5U7SemiprimeLeadingIntegral_eq_sub (eta : ℝ) (heta : 0 ≤ eta) :
    p5U7SemiprimeLeadingIntegral eta =
      p5U7InteriorOmegaIntegral eta-p5U7PrimeLeadingIntegral eta := by
  let C : Set (Fin 2 → ℝ) := Icc (fun _ => (59/250 : ℝ)) (fun _ => (1/2 : ℝ))
  let P : (Fin 2 → ℝ) → ℝ := fun x =>
    1/(max (59/250) (x 0)*max (59/250) (x 1)*max (59/250) (1-x 0-x 1))
  have hPc : Continuous P := by
    apply continuous_const.div
      (((continuous_const.max (continuous_apply 0)).mul
        (continuous_const.max (continuous_apply 1))).mul
          (continuous_const.max ((continuous_const.sub (continuous_apply 0)).sub (continuous_apply 1))))
    intro x
    exact (mul_pos (mul_pos
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _))
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _)))
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 59/250) (le_max_left _ _))).ne'
  have hsub : p5U7EtaDomain eta ⊆ C := by
    intro x hx
    exact ⟨fun i => ((mem_logPrimeBox.mp hx.1) i).1,
      fun i => ((mem_logPrimeBox.mp hx.1) i).2.le⟩
  have hpEq : ∀ x ∈ p5U7EtaDomain eta, P x = p5U7ComponentPrimeKernel (x 0) (x 1) := by
    intro x hx
    have h0 := ((mem_logPrimeBox.mp hx.1) 0).1
    have h1 := ((mem_logPrimeBox.mp hx.1) 1).1
    dsimp only [P,p5U7ComponentPrimeKernel]
    rw [max_eq_right h0,max_eq_right h1,max_eq_right (p5U7PrimeLeading_domain_geometry heta hx).2]
  have hp : IntegrableOn (fun x => p5U7ComponentPrimeKernel (x 0) (x 1))
      (p5U7EtaDomain eta) :=
    ((hPc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub).congr_fun
      (fun x hx => hpEq x hx) (measurableSet_p5U7EtaDomain eta)
  have hf : IntegrableOn (fun x => p5U7OmegaKernel 1 (x 0) (x 1)) (p5U7EtaDomain eta) :=
    ((continuous_p5U7EtaExtension.continuousOn.integrableOn_compact isCompact_Icc).mono_set hsub).congr_fun
      (fun x hx => p5U7Eta_extension_eq hx.1) (measurableSet_p5U7EtaDomain eta)
  have hs : IntegrableOn (fun x => p5U7ComponentSemiprimeKernel (x 0) (x 1))
      (p5U7EtaDomain eta) := by
    apply (hf.sub hp).congr_fun _ (measurableSet_p5U7EtaDomain eta)
    intro x hx
    have hh := p5U7Component_kernel_split (p5U7PrimeLeading_domain_geometry heta hx).1
    linarith only [hh]
  have hsplit : p5U7InteriorOmegaIntegral eta =
      p5U7PrimeLeadingIntegral eta+p5U7SemiprimeLeadingIntegral eta := by
    unfold p5U7InteriorOmegaIntegral p5U7PrimeLeadingIntegral p5U7SemiprimeLeadingIntegral
    rw [← integral_add hp hs]
    apply setIntegral_congr_fun (measurableSet_p5U7EtaDomain eta)
    intro x hx
    exact p5U7Component_kernel_split (p5U7PrimeLeading_domain_geometry heta hx).1
  linarith only [hsplit]

/-- Separate ACTUAL ordered-semiprime leading integral and limit.
The repeated terminal-factor wall and every marked outer pair survive. -/
theorem tendsto_p5U7ActualInteriorFour_normalized (eta : ℝ) (heta : 0 < eta) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ)/(N : ℝ))*
      ((p5U7ActualInteriorFour N eta).card : ℝ)) atTop
        (𝓝 (p5U7SemiprimeLeadingIntegral eta)) := by
  rw [p5U7SemiprimeLeadingIntegral_eq_sub eta heta.le]
  exact tendsto_p5U7ActualInteriorFour_normalized_sub eta heta

end
end ImbalancedChen
