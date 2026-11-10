import ImbalancedChen.Part5OriginalH430OwnedRootCounts
import ImbalancedChen.P2OriginalBankThetaMassLimits
import ImbalancedChen.P2MarkedThetaLiNormalization
import ImbalancedChen.CurrentChenInitialSource
import ImbalancedChen.CurrentChenTrueLiNormalization
import ImbalancedChen.ActualPrimeBoxTestFunctions
import ImbalancedChen.Part5OriginalH430FullRootAmplitude

/-! The genuine outer Θ mass on a half-open interval of root primes.
The arithmetic weights keep p∤N, φ(p), C(pN), literal li and the
positive log(Q/p). On the original positive-width U3 clamp they
give the full frozen A(2)−H430(2) contribution at every fine
preassigned n and τ. -/

namespace ImbalancedChen.Part5OriginalH430RootIntervalTheta

noncomputable section
open MeasureTheory Set Filter Topology
open scoped Classical BigOperators
open Wu2008DoubleSieve
open P2OriginalChildPhysicalNormalization (thetaAtom localPrimeFactor)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5UpperTables Part5UpperTables.OriginalU34
open Part5OriginalUpsilon5CausalDictionary (a floorValue)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenTableRootMass Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430TaggedArithmeticReceivers
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)

def primeBand (N : ℕ) (b c : ℝ) : Finset ℕ :=
  chenSinglePrimeSelector N ((N : ℝ)^b) ((N : ℝ)^c)

private theorem tuple_mem {N : ℕ} (hN : 1 < N) {b c : ℝ} (hc : c < 1)
    (p : Fin 1 → ℕ) :
    p 0 ∈ primeBand N b c ↔ p ∈ actualPrimeBoxTuples N (fun _ => b) (fun _ => c) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast hN
  have hcap : (N : ℝ)^c < N := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hNr hc
  constructor
  · intro hp
    obtain ⟨hcar, hlo, hhi⟩ := Finset.mem_filter.mp hp
    have hd := mem_chenAdditivePrimeCarrier.mp hcar
    apply mem_actualPrimeBoxTuples_iff.mpr
    intro i
    fin_cases i
    exact ⟨hd.2.1, hd.2.1.coprime_iff_not_dvd.mp hd.2.2, hlo, hhi⟩
  · intro hp
    have hi := mem_actualPrimeBoxTuples_iff.mp hp 0
    refine Finset.mem_filter.mpr ⟨mem_chenAdditivePrimeCarrier.mpr ?_, hi.2.2⟩
    exact ⟨by exact_mod_cast hi.2.2.2.trans hcap, hi.1, hi.1.coprime_iff_not_dvd.mpr hi.2.1⟩

private theorem log_mem {N p : ℕ} {b c : ℝ} (hN : 1 < N) (hc : c < 1)
    (hp : p ∈ primeBand N b c) : physicalPrime N p ∈ Ico b c := by
  have hz := ((mem_actualPrimeBoxTuples_log_iff hN _ _ ![p]).mp
    ((tuple_mem hN hc ![p]).mp hp)).2
  have h := mem_logPrimeBox.mp hz (0 : Fin 1)
  exact h

def intervalProfile (L t : ℝ) : ℝ := 4 / (L-t)

def reciprocalMass (N : ℕ) (b c L : ℝ) : ℝ :=
  ∑ p ∈ primeBand N b c, (1 / ((p : ℝ)-1)) * intervalProfile L (physicalPrime N p)

def correctedMass (N : ℕ) (b c L : ℝ) : ℝ :=
  ∑ p ∈ primeBand N b c, localPrimeFactor 1 p * intervalProfile L (physicalPrime N p)

def intervalMass (b c L : ℝ) : ℝ :=
  ∫ x in Ico b c, intervalProfile L x * (1/x)

private theorem reciprocal_reindex {N : ℕ} {b c L : ℝ} (hN : 1 < N) (hc : c < 1) :
    reciprocalMass N b c L =
      actualPrimeBoxTestSum N (fun _ : Fin 1 => b) (fun _ => c)
        (fun x => intervalProfile L (x 0)) := by
  unfold reciprocalMass actualPrimeBoxTestSum
  refine Finset.sum_bij (fun p _ => ![p]) ?_ ?_ ?_ ?_
  · intro p hp
    exact (tuple_mem hN hc ![p]).mp hp
  · intro p _ q _ h
    simpa using congrFun h 0
  · intro p hp
    refine ⟨p 0, (tuple_mem hN hc p).mpr hp, ?_⟩
    funext i
    fin_cases i
    rfl
  · intro p _
    simp only [Fin.prod_univ_one, Matrix.cons_val_zero, actualPrimeTupleLog, physicalPrime]

private theorem reciprocal_integral (b c L : ℝ) :
    (∫ x in logPrimeBox (fun _ : Fin 1 => b) (fun _ => c),
      intervalProfile L (x 0) * ∏ i, 1/x i) = intervalMass b c L := by
  let F := fun x : Fin 1 → ℝ => intervalProfile L (x 0) * ∏ i, 1/x i
  have h := ((volume_preserving_funUnique (Fin 1) ℝ).symm
    (MeasurableEquiv.funUnique (Fin 1) ℝ)).setIntegral_preimage_emb
    (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.measurableEmbedding
    F (logPrimeBox (fun _ : Fin 1 => b) (fun _ => c))
  change (∫ x in logPrimeBox _ _, F x) = _
  erw [← h]
  have hd : (MeasurableEquiv.funUnique (Fin 1) ℝ).symm ⁻¹'
      logPrimeBox (fun _ : Fin 1 => b) (fun _ => c) = Ico b c := by
    ext x
    simp [mem_logPrimeBox, Fin.forall_fin_one]
  rw [hd]
  change (∫ x in Ico b c, intervalProfile L x * ∏ _ : Fin 1, 1/x) = _
  simp only [Fin.prod_univ_one, intervalMass]

theorem reciprocal_mass_limit {b c L : ℝ} (hb : 0 < b) (hbc : b < c)
    (hc : c < 1) (hL : c < L) :
    Tendsto (fun N => reciprocalMass N b c L) atTop (𝓝 (intervalMass b c L)) := by
  have hcont : ContinuousOn (fun x : Fin 1 → ℝ => intervalProfile L (x 0))
      (univ.pi (fun _ => Icc b c)) := by
    apply continuousOn_const.div (continuousOn_const.sub (continuous_apply 0).continuousOn)
    intro x hx
    exact (sub_pos.mpr (((hx 0 (mem_univ _)).2).trans_lt hL)).ne'
  have h := tendsto_actualPrimeBoxTestSum_cube (k := 1) hb hbc _ hcont
  rw [reciprocal_integral] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  exact (reciprocal_reindex hN hc).symm

/-- The arithmetic change from 1/(p-1) to 1/(p-2) on a fresh
root is made after retaining its exact local prime factor. -/
private theorem corrected_difference {N : ℕ} {b c L : ℝ}
    (hN : 1 < N) (hc : c < 1) (hL : c < L) (hpow : 4 ≤ (N : ℝ)^b) :
    |correctedMass N b c L - reciprocalMass N b c L| ≤
      (2 / (N : ℝ)^b) * reciprocalMass N b c L := by
  unfold correctedMass reciprocalMass
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  have hx := log_mem hN hc hp
  have hz : 0 ≤ intervalProfile L (physicalPrime N p) :=
    div_nonneg (by norm_num) (sub_pos.mpr (hx.2.trans hL)).le
  have hw := P2OriginalBankThetaMassLimits.local_error (d := 1) hpow
    (Finset.mem_filter.mp hp).2.1
  rw [← sub_mul, abs_mul, abs_of_nonneg hz, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hw hz

private theorem corrected_mass_limit {b c L : ℝ} (hb : 0 < b) (hbc : b < c)
    (hc : c < 1) (hL : c < L) :
    Tendsto (fun N => correctedMass N b c L) atTop (𝓝 (intervalMass b c L)) := by
  have hbase := reciprocal_mass_limit hb hbc hc hL
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => (2/(N : ℝ)^b)*reciprocalMass N b c L)
      atTop (𝓝 0) := by simpa using (hpow.const_div_atTop (2 : ℝ)).mul hbase
  have hdiff : Tendsto (fun N => correctedMass N b c L-reciprocalMass N b c L)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hsmall.neg) hsmall
    · filter_upwards [eventually_gt_atTop (1 : ℕ), hpow.eventually_ge_atTop 4] with N hN h4
      exact (abs_le.mp (corrected_difference hN hc hL h4)).1
    · filter_upwards [eventually_gt_atTop (1 : ℕ), hpow.eventually_ge_atTop 4] with N hN h4
      exact (abs_le.mp (corrected_difference hN hc hL h4)).2
  simpa only [sub_add_cancel, zero_add] using hdiff.add hbase

def literalScale (N : ℕ) : ℝ := logarithmicIntegral N * Real.log N / (N : ℝ)

private theorem literalScale_limit : Tendsto literalScale atTop (𝓝 1) := by
  have hz : Tendsto (fun N : ℕ => Real.log (N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one, Function.comp_def] using
      h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh : Tendsto (fun N : ℕ =>
      MathlibNt.SieveTheory.BombieriVinogradov.trueLogarithmicIntegral N * Real.log N / (N : ℝ) -
      (2/Real.log 2)*(Real.log N / (N : ℝ))) atTop (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using
      tendsto_currentChen_trueLi_normalized.sub (hz.const_mul (2/Real.log 2))
  apply hh.congr'
  apply Eventually.of_forall
  intro N
  rw [P2MarkedThetaLiNormalization.trueLi_eq_literalLi_add]
  unfold literalScale
  ring

/-- The original singular normalization cancels the parent singular
series only. The full inserted-prime correction survives. -/
theorem normalized_root_atom {N p : ℕ} {L : ℝ} (hN : 1 < N) (hp : p.Prime)
    (hp2 : 2 < p) (hpN : p.Coprime N) (hL : physicalPrime N p < L) :
    thetaAtom N ((N : ℝ)^L) p / singularNormalization N =
      literalScale N * (localPrimeFactor 1 p * intervalProfile L (physicalPrime N p)) := by
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN0
  have hpr : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have har : wuSingularSeries (p*N) / (Nat.totient p : ℝ) =
      singularSeries N * localPrimeFactor 1 p := by
    have hh := wu_inserted_arithmetic_weight hN0 (show 0 < (1 : ℕ) by decide) hp hp2 hpN
    simpa only [one_mul, Nat.totient_one, Nat.cast_one, div_one, localPrimeFactor,
      wuSingularSeries_eq_liu N hN0, ← currentChen_singularSeries_eq_liuSingularSeries N] using hh
  have hlev : Real.log ((N : ℝ)^L / (p : ℝ)) =
      (L-physicalPrime N p)*Real.log N := by
    rw [Real.log_div (Real.rpow_pos_of_pos hNr L).ne' hpr.ne', Real.log_rpow hNr]
    unfold physicalPrime
    field_simp [hlog.ne'] <;> ring
  unfold thetaAtom
  rw [← div_div, har, hlev]
  unfold singularNormalization literalScale intervalProfile
  field_simp [hNr.ne', hlog.ne', (singularSeries_pos N).ne', (sub_pos.mpr hL).ne'] <;> ring

/-- Fixed exponent and fixed half-open prime interval, chosen before N.
The right side is the manuscript's true one-dimensional outer mass. -/
theorem actual_interval_theta_limit {b c L : ℝ} (hb : 0 < b) (hbc : b < c)
    (hc : c < 1) (hL : c < L) :
    Tendsto (fun N : ℕ =>
      (∑ p ∈ primeBand N b c, thetaAtom N ((N : ℝ)^L) p) / singularNormalization N)
      atTop (𝓝 (intervalMass b c L)) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ)^b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp tendsto_natCast_atTop_atTop
  have hh := literalScale_limit.mul (corrected_mass_limit hb hbc hc hL)
  simp only [one_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ), hpow.eventually_ge_atTop 4] with N hN h4
  rw [Finset.sum_div, correctedMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hcar := mem_chenAdditivePrimeCarrier.mp (Finset.mem_filter.mp hp).1
  have hlo := (Finset.mem_filter.mp hp).2.1
  have hp2 : 2 < p := by
    have h : (2 : ℝ) < p := by linarith
    exact_mod_cast h
  exact (normalized_root_atom hN hcar.2.1 hp2 hcar.2.2 ((log_mem hN hc hp).2.trans hL)).symm

def clampLevel (n : ℕ) (tau : ℝ) := frozenLevel n (1/2-tau)

def clampPrimes (N : ℕ) : Finset ℕ :=
  (originalBand N .U3).filter (fun p => (N : ℝ)^clampStart ≤ p)

private theorem clamp_primes_eq {N : ℕ} (hN : 1 ≤ N) :
    clampPrimes N = primeBand N clampStart (1/3) := by
  have ha : (N : ℝ)^a ≤ (N : ℝ)^clampStart := Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast hN) (by norm_num [a, clampStart])
  ext p
  change (p ∈ (chenSinglePrimeSelector N _ _).filter _) ↔ p ∈ chenSinglePrimeSelector N _ _
  simp only [chenSinglePrimeSelector, Finset.mem_filter]
  exact ⟨fun ⟨⟨hcar, _, hhi⟩, hlo⟩ => ⟨hcar, hlo, hhi⟩,
    fun ⟨hcar, hlo, hhi⟩ => ⟨⟨hcar, ha.trans hlo, hhi⟩, hlo⟩⟩

theorem clamp_physical_level {N n p : ℕ} {tau : ℝ} (hN : 1 < N) (ht : 0 ≤ tau)
    (ht' : tau ≤ 1/12) (hp : p ∈ clampPrimes N) :
    rootQ N n .U3 tau p = (N : ℝ)^(clampLevel n tau) ∧
      frozenQuery n .U3 tau (physicalPrime N p) = 2 := by
  have horig := (Finset.mem_filter.mp hp).1
  have hband := original_band_geometry (by omega : 2 ≤ N) horig
  have hp' := hp
  rw [clamp_primes_eq (by omega : 1 ≤ N)] at hp'
  have hx := (log_mem hN (by norm_num : (1/3 : ℝ) < 1) hp').1
  have htail : ¬ physicalPrime N p < tailCutoff :=
    not_lt.mpr ((by norm_num [tailCutoff, clampStart] : tailCutoff ≤ clampStart).trans hx)
  constructor
  · have hsum : (sourceRoot .U3 tau (physicalPrime N p)).physical.total = 1/2-tau := by
      simp only [sourceRoot, sourceResidual, U3Residual, if_neg htail, tailResidual]
      ring
    simp only [rootQ, rootLevel, hsum, clampLevel]
  · exact ideal_clamp_preserved ht ht' hband (actual_U3_clamp hx).1

private theorem clamp_level_gt {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n : ℝ)+1) ≤ 11/384) : (1/3 : ℝ) < clampLevel n tau := by
  have h := (frozenLevel_bounds (show 1/2-tau ∈ Icc (0 : ℝ) 1 from
    ⟨by linarith, by linarith⟩) n).2
  unfold clampLevel
  linarith only [h, hn, ht']

def clampMass (N n : ℕ) (tau : ℝ) : ℝ :=
  ∑ p ∈ clampPrimes N, thetaAtom N (rootQ N n .U3 tau p) p

theorem actual_clamp_theta_limit {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau)
    (ht' : tau ≤ 1/12) (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    Tendsto (fun N => clampMass N n tau / singularNormalization N) atTop
      (𝓝 (intervalMass clampStart (1/3) (clampLevel n tau))) := by
  apply (actual_interval_theta_limit (by norm_num [clampStart] : 0 < clampStart)
    (by norm_num [clampStart] : clampStart < 1/3) (by norm_num) (clamp_level_gt ht ht' hn)).congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  congr 1
  unfold clampMass
  rw [← clamp_primes_eq (by omega : 1 ≤ N)]
  exact Finset.sum_congr rfl (fun p hp => by rw [(clamp_physical_level hN ht ht' hp).1])

/-- The positive-width clamp keeps both adjacent old entries, its actual
A(2), every target-coprime prime and its own same-Q arithmetic Θ. -/
theorem actual_clamp_full_coefficient_limit {n : ℕ} {tau : ℝ} (ht : 0 ≤ tau)
    (ht' : tau ≤ 1/12) (hn : 1/((n : ℝ)+1) ≤ 11/384) :
    Tendsto (fun N : ℕ => (∑ p ∈ clampPrimes N,
      (upperAmplitude (frozenQuery n .U3 tau (physicalPrime N p)) -
        H430 (frozenQuery n .U3 tau (physicalPrime N p))) *
          thetaAtom N (rootQ N n .U3 tau p) p) / singularNormalization N) atTop
      (𝓝 ((upperAmplitude 2 - min (floorValue H430Numerators 49)
        (floorValue H430Numerators 50)) * intervalMass clampStart (1/3) (clampLevel n tau))) := by
  apply ((actual_clamp_theta_limit ht ht' hn).const_mul
    (upperAmplitude 2-min (floorValue H430Numerators 49) (floorValue H430Numerators 50))).congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with N hN
  rw [← mul_div_assoc, clampMass, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [(clamp_physical_level hN ht ht' hp).2, H430_two_eq_adjacent_min]


/-- Exact continuous mass at every admissible frozen level. -/
def intervalFormula (b c L : ℝ) : ℝ :=
  (4/L)*(Real.log (c/b) + Real.log ((L-b)/(L-c)))

theorem intervalMass_formula {b c L : ℝ} (hb : 0 < b) (hbc : b < c) (hL : c < L) :
    intervalMass b c L = intervalFormula b c L := by
  have hL0 := (hb.trans hbc).trans hL
  have hc := hb.trans hbc
  have hcont : ContinuousOn (fun x : ℝ => intervalProfile L x * (1/x)) (Icc b c) := by
    apply (continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun x hx => (sub_pos.mpr (hx.2.trans_lt hL)).ne')).mul
    exact continuousOn_const.div continuousOn_id (fun x hx => (hb.trans_le hx.1).ne')
  have hd : ∀ x ∈ uIcc b c,
      HasDerivAt (fun t : ℝ => (4/L)*(Real.log t - Real.log (L-t)))
        (intervalProfile L x * (1/x)) x := by
    intro x hx
    rw [uIcc_of_le hbc.le] at hx
    have hx0 := hb.trans_le hx.1
    have hdiff := sub_pos.mpr (hx.2.trans_lt hL)
    have hlog := ((hasDerivAt_id x).const_sub L).log hdiff.ne'
    apply (((Real.hasDerivAt_log hx0.ne').sub hlog).const_mul (4/L)).congr_deriv
    unfold intervalProfile
    field_simp [hx0.ne', hdiff.ne', hL0.ne'] <;> ring
  rw [intervalMass, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable_of_Icc hbc.le)]
  dsimp only
  unfold intervalFormula
  rw [Real.log_div hc.ne' hb.ne', Real.log_div (sub_pos.mpr (hbc.trans hL)).ne'
    (sub_pos.mpr hL).ne']
  ring

theorem intervalMass_positive {b c L : ℝ} (hb : 0 < b) (hbc : b < c) (hL : c < L) :
    0 < intervalMass b c L := by
  rw [intervalMass_formula hb hbc hL, intervalFormula]
  have h1 : 1 < c/b := (one_lt_div hb).mpr hbc
  have h2 : 1 < (L-b)/(L-c) := (one_lt_div (sub_pos.mpr hL)).mpr (by linarith)
  exact mul_pos (div_pos (by norm_num) ((hb.trans hbc).trans hL))
    (add_pos (Real.log_pos h1) (Real.log_pos h2))

open Part5OriginalH430FrozenPerturbation (meshError)
open Part5OriginalH430FrozenRootMass (finiteTau finiteTau_pos finiteTau_le)
open Part5OriginalH430FullRootAmplitude (eventually_fine_mesh)

private theorem clamp_level_limit :
    Tendsto (fun n => clampLevel n (finiteTau n)) atTop (𝓝 (1/2 : ℝ)) := by
  have hm : Tendsto meshError atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have ht : Tendsto finiteTau atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (finiteTau_pos n).le) (fun n => min_le_right _ _) hm
  have hl : Tendsto (fun n => (1/2 : ℝ)-finiteTau n-meshError n) atTop (𝓝 (1/2)) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub ht).sub hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
  · apply Eventually.of_forall
    intro n
    have hf := finiteTau_pos n
    have hu := finiteTau_le n
    have hh := (frozenLevel_bounds (show 1/2-finiteTau n ∈ Icc (0 : ℝ) 1 from
      ⟨by linarith, by linarith⟩) n).2
    change 1/2-finiteTau n-1/((n : ℝ)+1) ≤ frozenLevel n (1/2-finiteTau n)
    linarith only [hh]
  · apply Eventually.of_forall
    intro n
    have hf := finiteTau_pos n
    have hu := finiteTau_le n
    have hh := (frozenLevel_bounds (show 1/2-finiteTau n ∈ Icc (0 : ℝ) 1 from
      ⟨by linarith, by linarith⟩) n).1
    exact hh.trans (sub_le_self _ hf.le)

theorem ideal_clamp_mass :
    intervalMass clampStart (1/3) (1/2) = 8*Real.log (834/833 : ℝ) := by
  calc
    intervalMass clampStart (1/3) (1/2) =
        ∫ t in Ico clampStart (1/3 : ℝ), branchWeight tailResidual t := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t _
      simp only [intervalProfile, branchWeight, tailResidual, div_eq_mul_inv, mul_inv_rev,
        one_mul]
      ring
    _ = _ := integral_clamp_tailWeight

theorem clamp_mass_precision_limit :
    Tendsto (fun n => intervalMass clampStart (1/3) (clampLevel n (finiteTau n)))
      atTop (𝓝 (8*Real.log (834/833 : ℝ))) := by
  have hc : ContinuousAt (intervalFormula clampStart (1/3)) (1/2) := by
    unfold intervalFormula
    fun_prop (disch := norm_num [clampStart])
  have h := hc.tendsto.comp clamp_level_limit
  rw [← intervalMass_formula (by norm_num [clampStart] : 0 < clampStart)
    (by norm_num [clampStart] : clampStart < 1/3) (by norm_num : (1/3 : ℝ) < 1/2),
    ideal_clamp_mass] at h
  apply h.congr'
  filter_upwards [eventually_fine_mesh] with n hn
  exact (intervalMass_formula (by norm_num [clampStart]) (by norm_num [clampStart])
    (clamp_level_gt (finiteTau_pos n).le (finiteTau_le n) hn)).symm

/-- A single finite n and positive reserve are chosen before the target N.
The full original clamp has positive width 1/7500 and its true limiting
mass is 8 log(834/833). Both adjacent H430 entries remain in its signed
coefficient. -/
theorem actual_original_clamp_integral (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ n : ℕ, 0 < finiteTau n ∧ finiteTau n ≤ 1/12 ∧ meshError n ≤ 11/384 ∧
      ∀ᶠ N : ℕ in atTop,
      |(∑ p ∈ clampPrimes N,
        (upperAmplitude (frozenQuery n .U3 (finiteTau n) (physicalPrime N p)) -
          H430 (frozenQuery n .U3 (finiteTau n) (physicalPrime N p))) *
            thetaAtom N (rootQ N n .U3 (finiteTau n) p) p) / singularNormalization N -
        ∫ t in Ico clampStart (1/3 : ℝ), U3H430Coefficient t| < epsilon := by
  let K := upperAmplitude 2-min (floorValue H430Numerators 49) (floorValue H430Numerators 50)
  have hfinal := clamp_mass_precision_limit.const_mul K
  have hnear := (Metric.tendsto_nhds.mp hfinal) (epsilon/2) (half_pos he)
  obtain ⟨n, hn, hclose⟩ := (eventually_fine_mesh.and hnear).exists
  refine ⟨n, finiteTau_pos n, finiteTau_le n, hn, ?_⟩
  have hphysical := actual_clamp_full_coefficient_limit
    (finiteTau_pos n).le (finiteTau_le n) hn
  filter_upwards [(Metric.tendsto_nhds.mp hphysical) (epsilon/2) (half_pos he)] with N hN
  rw [integral_U3H430_clamp_exact, ← Real.dist_eq]
  exact (dist_triangle _ (K*intervalMass clampStart (1/3) (clampLevel n (finiteTau n))) _).trans_lt
    (by linarith only [hN, hclose])

end
end ImbalancedChen.Part5OriginalH430RootIntervalTheta
