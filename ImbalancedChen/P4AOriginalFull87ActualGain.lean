import ImbalancedChen.P4AOriginalFull87OrdinarySignedGain
import ImbalancedChen.P4AOriginalFull87SourcePrimeTests
import ImbalancedChen.P1ActualUpperClosedParameterUniformity

/-! The complete ordinary tree is compared before taking the positive
presieve on its successor. All original strict sources use one schedule. -/
namespace ImbalancedChen.P4AOriginalFull87ActualGain
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P4AOriginalFull87SevenCubeAdmission (point pre pre_length pre_ofFn tuple_pre)
open P4AOriginalFull87OrdinarySignedGain P4AOriginalFull87SourcePrimeTests
open P4AOriginalFull87EighthKernelControl
open P4AOriginalFull87EighthKernelIntegration (actualParent actual_eighth_kernel_transport)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87FiniteEighthPolicy
  (selectedCap selectedCap_some_spec selectedCap_of_trim point8_at_eight)
open P4AOriginalFull87LicensedSixthPolicy (policy sixthPolicy frontier_eq_new_sixth)
open P4AOriginalVariableFifthPhysicalLedger (raw)
open P5OriginalCommonPositivePresieve (normalize)

abbrev tuples (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 8 => cutoff) (fun _ => mu)
abbrev mass (N : ℕ) := actualPrimeBoxMass N (fun _ : Fin 8 => cutoff) (fun _ => mu)

private theorem pre_positive {p : Fin 8 → ℕ} (hp : ∀ i, 0 < p i) :
    ∀ x ∈ pre p, 0 < x := by
  intro x hx
  rw [pre_ofFn] at hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hx)
  exact hp i

theorem tupleResidual_off (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ)
    (p : Fin 8 → ℕ) (ho : ∀ c : Cell, actualPrimeTupleLog N p ∉ trim c (width r)) :
    tupleResidual r n e q om N cap p = 0 := by
  have hnone : selectedCap (width r) n (N : ℝ) (pre p) = none := by
    cases h : selectedCap (width r) n (N : ℝ) (pre p) with
    | none => rfl
    | some a =>
      obtain ⟨c, _, ht, _⟩ := selectedCap_some_spec _ _ _ _ _ h
      rw [point8_at_eight _ _ (pre_length p)] at ht
      exact False.elim (ho c (by rw [← point_eq_tuple_log]; exact ht))
  simp only [tupleResidual, nextExponent, hnone, actualPrimeTupleInitialSaving,
    sub_self, zero_mul, zero_div]

private theorem admitted_iff_box_on_trim
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N cap : ℕ) (z : ℝ)
    (he : 0 ≤ e) (hN : 1 < N) (hz : (N : ℝ)^mu ≤ z) (hcap : z ≤ cap)
    (hh : HistoryOnTrim r e q om) (p : Fin 8 → ℕ)
    (c : Cell) (ht : actualPrimeTupleLog N p ∈ trim c (width r)) :
    p ∈ admitted n e q om N cap z ↔ p ∈ tuples N := by
  have hNr : 1 < (N : ℝ) := by exact_mod_cast hN
  rw [mem_actualPrimeBoxTuples_log_iff hN]
  constructor
  · intro ha
    have hd := (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 8
      (sixthPolicy n e q om (N : ℝ)) N cap 0 z hcap p).mp ha
    exact ⟨fun i => ⟨(hd.2.1 i).1, (hd.2.1 i).2.1⟩,
      source_subset_box c (trim_subset_source c (width_pos r) ht)⟩
  · rintro ⟨hp, _⟩
    rw [← point_eq_tuple_log] at ht
    have hr := hh N hNr (pre p) (pre_length p)
      (pre_positive (fun i => (hp i).1.pos)) c ht
    let s := P4AOriginalFull87ActualSourceMembership.canonicalState N cap 0 weight p
    have hs := P4AOriginalFull87LicensedSixthRealization.canonical_mem_states_of_history
      (width r) (width_pos r) n e q om N cap he hNr 0 z
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) hz hcap weight p
      (fun i => (hp i).1) (fun i => (hp i).2) c ht hr
    have hf := (List.mem_filter.mp hs).1
    rw [frontier_eq_new_sixth] at hf
    have hm : p ∈ ((firstExitDepthFrontier 8 (sixthPolicy n e q om (N : ℝ))
        weight [] true 1 (roughPrimeUniverse N cap 0 z)).map
        (fun s => primeHistoryTuple 8 s.selectedPrefix)) :=
      List.mem_map.mpr ⟨s, hf, tuple_pre p⟩
    exact List.mem_toFinset.mpr ((firstExitRootFrontier_admitted_tuple_perm
      8 (sixthPolicy n e q om (N : ℝ)) weight (roughPrimeUniverse N cap 0 z)).mem_iff.mp hm)

/-- Genuine target-deleted prime integral on the entire cube. Outside
all retained trims the two exponents agree, even for unadmitted tuples. -/
theorem original_raw_difference_eq_box (r n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (z : ℝ) (he : 0 ≤ e) (hN : 1 < N)
    (hz : (N : ℝ)^mu ≤ z) (hcap : z ≤ cap)
    (hn : 4 * width n < width r) (hh : HistoryOnTrim r e q om) :
    normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z -
      raw (policy (width r) n e q om (N : ℝ)) N cap 0 z) =
      ∑ p ∈ tuples N, (∏ i, weight (p i)) * tupleResidual r n e q om N cap p := by
  let active := fun p : Fin 8 → ℕ => ∃ c : Cell, actualPrimeTupleLog N p ∈ trim c (width r)
  let f := fun p : Fin 8 → ℕ => (∏ i, weight (p i)) * tupleResidual r n e q om N cap p
  have hnz (p) (hp : ¬active p) : f p = 0 := by
    rw [show f p = _ * tupleResidual r n e q om N cap p from rfl,
      tupleResidual_off r n e q om N cap p (fun c hc => hp ⟨c, hc⟩), mul_zero]
  have hf (B : Finset (Fin 8 → ℕ)) : (∑ p ∈ B.filter active, f p) = ∑ p ∈ B, f p := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : active p <;> simp [hp, hnz]
  have hset : (admitted n e q om N cap z).filter active = (tuples N).filter active := by
    ext p
    simp only [Finset.mem_filter]
    by_cases hp : active p
    · obtain ⟨c, hc⟩ := hp
      rw [admitted_iff_box_on_trim r n e q om N cap z he hN hz hcap hh p c hc]
    · simp [hp]
  rw [original_raw_difference_eq_admitted r n e q om N cap z hn (by exact_mod_cast hN) hh]
  exact (hf _).symm.trans ((congrArg (fun B : Finset (Fin 8 → ℕ) => ∑ p ∈ B, f p) hset).trans (hf _))

private def window : Set (ℝ × ℝ) :=
  (Icc cutoff (3 * mu) ×ˢ Icc cutoff mu) ∩ {q | q.1 ≤ 3 * q.2}

/-- A single ordinary Rosser threshold precedes every target, word,
rounded policy and selected cap. -/
private theorem quotient_window (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (p : Fin 8 → ℕ), (∀ i, 0 < p i) → ∀ L : ℝ,
      let t := actualPrimeTupleLog N p
      cutoff ≤ t 7 → t 7 ≤ mu → t 7 ≤ L - total t → L - total t ≤ 3 * t 7 →
      ∀ cap : ℕ, p 7 ≤ cap →
        |actualSmallRosserPlusDensity N cap (p 7 : ℝ) ((N : ℝ)^L / (∏ i, p i : ℕ)) *
          Real.log (N : ℝ) / singularSeries N - 4 / (L - total t)| < eta := by
  have compact : IsCompact window := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst (continuous_const.mul continuous_snd))
  obtain ⟨N0,hN0,h⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold window compact
      (fun q hq => ⟨cutoff_pos.trans_le hq.1.2.1, cutoff_pos.trans_le hq.1.1.1, hq.2⟩) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp L
  dsimp only
  intro hcut hupper hlo hhi cap hcap
  let t := actualPrimeTupleLog N p
  have hpar : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 7 : ℝ) L =
      (L - total t, t 7) := by
    change (L - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ), actualPrimeTupleLog N p 7) =
      (L - ∑ i, actualPrimeTupleLog N p i, actualPrimeTupleLog N p 7)
    rw [actualPrimeTupleLog_sum_prod p hp]
  obtain ⟨hl,hc⟩ := actualRosserQuotientParameters_exact (N : ℝ) (∏ i, p i : ℕ) (p 7 : ℝ) L
    (by exact_mod_cast (show 1 < N by omega))
    (by exact_mod_cast Finset.prod_pos (fun i (_ : i ∈ (Finset.univ : Finset (Fin 8))) => hp i))
    (by exact_mod_cast hp 7)
  rw [hpar] at hl hc
  have hwin : (L - total t, t 7) ∈ window :=
    ⟨⟨⟨hcut.trans hlo, hhi.trans (by change _ ≤ 3 * mu; linarith)⟩, hcut, hupper⟩, hhi⟩
  have hcap' : (p 7 : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hcap
  have hh := h N hN hEven (L - total t, t 7) hwin cap (by simpa only [hc] using hcap')
  simpa only [hl,hc] using hh

/-- One signed sum includes every retained finite word, including words
on which the finite ordinary Rosser difference is negative. The error
is paid against the full cube's nonnegative prime mass once. -/
theorem exists_actual_test_lower (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ), 0 ≤ e →
      4 * width n < width r → HistoryOnTrim r e q om →
      ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
      (∑ c : Cell, testSum N r c) ≤
        normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z -
          raw (policy (width r) n e q om (N : ℝ)) N cap 0 z) +
          (roundingConstant * width n + 2 * eta) * mass N := by
  obtain ⟨N0, hN0, hw⟩ := quotient_window eta heta
  refine ⟨N0,hN0,?_⟩
  intro N hN hEven r n e q om he hn hh cap z hz hcap
  have hNn : 1 < N := by omega
  have hNr : 1 < (N : ℝ) := by exact_mod_cast hNn
  let E := roundingConstant * width n + 2 * eta
  have hE : 0 ≤ E := add_nonneg (mul_nonneg roundingConstant_pos.le (width_pos n).le)
    (mul_nonneg (by norm_num) heta.le)
  have hpoint (p : Fin 8 → ℕ) (hp : p ∈ tuples N) :
      (∑ c : Cell, test r c (actualPrimeTupleLog N p)) ≤ tupleResidual r n e q om N cap p + E := by
    obtain ⟨hpr, hb⟩ := (mem_actualPrimeBoxTuples_log_iff hNn _ _ p).mp hp
    let t := actualPrimeTupleLog N p
    by_cases active : ∃ c, t ∈ trim c (width r)
    · obtain ⟨c, ht⟩ := active
      have hs := trim_subset_source c (width_pos r) ht
      have hsum : (∑ d : Cell, test r d t) = test r c t :=
        Finset.sum_eq_single_of_mem c (Finset.mem_univ _) (fun d _ hdc =>
          test_off_trim r d hb (fun hd => hdc (trim_owner_unique (width_pos r) hd ht)))
      change (∑ d : Cell, test r d t) ≤ _
      rw [hsum]
      have hpt : point (N : ℝ) p = t := point_eq_tuple_log N p
      have ht' : point (N : ℝ) p ∈ trim c (width r) := hpt.symm ▸ ht
      have hpos : ∀ i, 0 < p i := fun i => (hpr i).1.pos
      have hr := hh N hNr (pre p) (pre_length p) (pre_positive hpos) c ht'
      have hk := actual_eighth_kernel_transport r n hn e q om (N : ℝ) _ (pre_length p) c ht' hr
      -- Rewrite the policy point directly, preserving its original coordinates.
      have hgeom : cutoff < t 7 ∧ t 7 < actualParent n e q om (N : ℝ) (pre p) - total t ∧
          actualParent n e q om (N : ℝ) (pre p) ≤ comparison c t ∧
          comparison c t < (finiteCap n c t : ℝ) ∧ (finiteCap n c t : ℝ) - total t < 3 * t 7 ∧
          kernel c t ≤ residual (total t) (product t) (actualParent n e q om (N : ℝ) (pre p))
            (finiteCap n c t) + roundingConstant * width n := by
        rw [← hpt]
        exact hk
      obtain ⟨ha, hP, hPR, hRM, hM, hker⟩ := hgeom
      let P := actualParent n e q om (N : ℝ) (pre p)
      let L := (finiteCap n c t : ℝ)
      have hlast : p 7 ≤ cap := by
        have hlastR : (p 7 : ℝ) ≤ (cap : ℝ) := calc
          _ = (N : ℝ) ^ actualPrimeTupleLog N p 7 := (actualPrimeTupleLog_rpow hNn p hpos 7).symm
          _ ≤ (N : ℝ)^mu := Real.rpow_le_rpow_of_exponent_le hNr.le (mem_logPrimeBox.mp hb 7).2.le
          _ ≤ _ := hz.trans hcap
        exact_mod_cast hlastR
      have hold := hw N hN hEven p hpos P ha.le (mem_logPrimeBox.mp hb 7).2.le hP.le
        (by change _ ≤ 3 * t 7; linarith) cap hlast
      have hnew := hw N hN hEven p hpos L ha.le (mem_logPrimeBox.mp hb 7).2.le
        (by change _ ≤ L - total t; dsimp [L]; linarith) hM.le cap hlast
      have hj := (source_product_lower hs).2
      have hj1 : product t ≤ 1 := Finset.prod_le_one
        (fun i _ => (cutoff_pos.trans (source_coordinate_lower hs i)).le)
        (fun i _ => ((mem_logPrimeBox.mp hb i).2.le).trans (by norm_num [mu]))
      have hprof : profile c t = kernel c t * product t := by
        have hd := profile_density hs
        simp only [one_div, Finset.prod_inv_distrib, ← product] at hd
        rw [← hd]
        field_simp [hj.ne']
      have hprod := mul_le_mul_of_nonneg_right hker hj.le
      have hPL : 0 < P - total t := cutoff_pos.trans (ha.trans hP)
      have hLL : 0 < L - total t := by dsimp [L]; linarith
      have hres : residual (total t) (product t) P L * product t =
          4 / (P - total t) - 4 / (L - total t) := by
        rw [residual_eq_reciprocal _ _ _ _ hPL.ne' hLL.ne' hj.ne']
        field_simp [hPL.ne',hLL.ne',hj.ne'] <;> ring
      change kernel c t * product t ≤
        (residual (total t) (product t) P L + roundingConstant * width n) * product t at hprod
      rw [add_mul, hres, ← hprof] at hprod
      have hround := mul_le_mul_of_nonneg_left hj1 (mul_nonneg roundingConstant_pos.le (width_pos n).le)
      rw [mul_one] at hround
      have ha' := selectedCap_of_trim (width r) (width_pos r) n (N : ℝ) (pre p) (pre_length p) c ht'
      change selectedCap _ _ _ _ = some (finiteCap n c (point (N : ℝ) p)) at ha'
      rw [hpt] at ha'
      change test r c t ≤ tupleResidual r n e q om N cap p + E
      simp only [tupleResidual, nextExponent, ha', actualPrimeTupleInitialSaving, sub_mul, sub_div]
      change test r c t ≤
        actualSmallRosserPlusDensity N cap (p 7 : ℝ) ((N : ℝ)^P / (∏ i, p i : ℕ)) *
          Real.log (N : ℝ) / singularSeries N -
        actualSmallRosserPlusDensity N cap (p 7 : ℝ) ((N : ℝ)^L / (∏ i, p i : ℕ)) *
          Real.log (N : ℝ) / singularSeries N + E
      dsimp only [E]
      linarith only [(test_bounds r c t).2, hprod, hround, (abs_lt.mp hold).1, (abs_lt.mp hnew).2]
    · have off : ∀ c, t ∉ trim c (width r) := fun c hc => active ⟨c,hc⟩
      have hzero (c : Cell) : test r c (actualPrimeTupleLog N p) = 0 := test_off_trim r c hb (off c)
      simp only [hzero, Finset.sum_const_zero,
        tupleResidual_off r n e q om N cap p off, zero_add]
      exact hE
  rw [original_raw_difference_eq_box r n e q om N cap z he hNn hz hcap hn hh]
  simp only [testSum, actualPrimeBoxTestSum]
  rw [Finset.sum_comm]
  change (∑ p ∈ tuples N, ∑ c : Cell, (∏ i, weight (p i)) * test r c (actualPrimeTupleLog N p)) ≤ _
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ tuples N, (∏ i, weight (p i)) * (tupleResidual r n e q om N cap p + E) :=
      Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hpoint p hp) (actualPrimeBoxWeight_nonneg hp)
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, mass, actualPrimeBoxMass]; ring

/-- The entire sum of the original positive source integrals is earned
by the actual ordinary sixth-to-eighth splice. Every threshold precedes
the target. The trim, cap resolution and common mesh choices are cofinal. -/
theorem exists_ordinary_source_gain (eps : ℝ) (heps : 0 < eps) :
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ (cap : ℕ) (z : ℝ), (N : ℝ)^mu ≤ z → z ≤ cap →
      (∑ c : Cell, cellIntegral c) - eps <
        normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z -
          raw (policy (width r) n e q om (N : ℝ)) N cap 0 z) := by
  have hab : cutoff < mu := by norm_num [cutoff,mu]
  let B := ∏ _i : Fin 8, Real.log (mu / cutoff)
  have hB : 0 ≤ B := Finset.prod_nonneg (fun _ _ =>
    Real.log_nonneg ((one_le_div cutoff_pos).mpr hab.le))
  have hB1 : 0 < B + 1 := by linarith
  let eta := eps / (8 * (B + 1))
  have heta : 0 < eta := div_pos heps (mul_pos (by norm_num) hB1)
  have hbudget : eta * (B + 1) = eps / 8 := by
    dsimp only [eta]
    field_simp [hB1.ne'] <;> ring
  have hInt : Tendsto (fun r => ∑ c : Cell, testIntegral r c) atTop
      (𝓝 (∑ c : Cell, cellIntegral c)) :=
    tendsto_finsetSum Finset.univ (fun c _ => testIntegral_tendsto c)
  obtain ⟨r0,hr0⟩ := eventually_atTop.1 (hInt.eventually
    (lt_mem_nhds (show (∑ c : Cell, cellIntegral c) - eps / 4 < _ by linarith)))
  obtain ⟨Na, hNa, ha⟩ := exists_actual_test_lower eta heta
  have hm : ∀ᶠ N : ℕ in atTop, mass N < B + 1 :=
    (tendsto_actualPrimeBoxMass _ _ (fun _ => cutoff_pos) (fun _ => hab)).eventually
      (gt_mem_nhds (lt_add_one B))
  obtain ⟨Nm,hNm⟩ := eventually_atTop.1 hm
  have hrnd : ∀ᶠ n : ℕ in atTop, roundingConstant * width n < eta := by
    have h := (tendsto_const_nhds (x := roundingConstant)).mul width_tendsto
    rw [mul_zero] at h
    exact h.eventually (gt_mem_nhds heta)
  obtain ⟨nr,hnr⟩ := eventually_atTop.1 hrnd
  refine ⟨r0,?_⟩
  intro r hr
  obtain ⟨nc,hnc⟩ := P4AOriginalFull87FiniteEighthCap.exists_uniform_cap_resolution (width r) (width_pos r)
  have hprime : Tendsto (fun N => ∑ c : Cell, testSum N r c) atTop (𝓝 (∑ c : Cell, testIntegral r c)) :=
    tendsto_finsetSum Finset.univ (fun c _ => testSum_tendsto r c)
  obtain ⟨Np,hNp⟩ := eventually_atTop.1 (hprime.eventually
    (lt_mem_nhds (show (∑ c : Cell, testIntegral r c) - eps / 4 < _ by linarith)))
  refine ⟨max nr nc,?_⟩
  intro n hn
  obtain ⟨e0,he0,hh⟩ := common_history_on_trim r
  refine ⟨e0, he0, ?_⟩
  intro e he hee
  obtain ⟨q0,hq0,h⟩ := hh e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hq om hom
  refine ⟨max Na (max Nm Np),hNa.trans (le_max_left _ _),?_⟩
  intro N hN hEven cap z hz hcap
  have hNaN : Na ≤ N := (le_max_left _ _).trans hN
  have hmN := hNm N ((le_max_left Nm Np).trans ((le_max_right _ _).trans hN))
  have hpN := hNp N ((le_max_right Nm Np).trans ((le_max_right _ _).trans hN))
  have hcost := ha N hNaN hEven r n e q om he.le (hnc n ((le_max_right _ _).trans hn))
    (h q hq om hom) cap z hz hcap
  have hm0 : 0 ≤ mass N :=
    Finset.sum_nonneg (fun p hp => actualPrimeBoxWeight_nonneg hp)
  have hround := hnr n ((le_max_left _ _).trans hn)
  have hmul : (roundingConstant * width n + 2 * eta) * mass N ≤ (3 * eta) * (B + 1) :=
    mul_le_mul (by linarith) hmN.le hm0 (by positivity)
  linarith only [hr0 r hr, hpN, hcost, hmul, hbudget, heps]

/-- Positive presieve on the whole new tree with the manuscript's
w ≤ z, and a single beta projection against its own ordinary density. -/
theorem exists_positive_presieve_source_gain (nu eps betaMax : ℝ)
    (hnu : 0 < nu) (heps : 0 < eps) (hMax : 0 < betaMax) :
    ∃ beta : ℝ, 0 < beta ∧ beta < 1 / 8 ∧ beta < betaMax ∧
      beta^2 ≤ (19/96 : ℝ)/nu ∧
    ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n →
    ∃ e0 : ℝ, 0 < e0 ∧ ∀ e : ℚ, 0 < e → (e : ℝ) < e0 →
    ∃ q0 : ℕ, 0 < q0 ∧ ∀ q : ℕ, q0 ≤ q → ∀ om : ℝ, om ≤ 1 / 100 →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
    ∀ cap : ℕ, (N : ℝ)^(19/96 : ℝ) ≤ cap →
      let w := (N : ℝ)^(nu * beta^2)
      let z := (N : ℝ)^(19/96 : ℝ)
      let L := (N : ℝ)^(nu * beta)
      1 < w ∧ w ≤ z ∧
      normalize N (P4AOriginalVariableFifthPhysicalLedger.physical
        (policy (width r) n e q om (N : ℝ)) N cap w z L) <
        normalize N (raw (sixthPolicy n e q om (N : ℝ)) N cap 0 z) -
          (∑ c : Cell, cellIntegral c) + eps := by
  have hnr : nu * ((19 / 96 : ℝ) / nu) = (19 / 96 : ℝ) := by field_simp [hnu.ne'] <;> ring
  obtain ⟨beta,hb,hb8,hbMax,hbr,Nb,_hNb,hbeta⟩ :=
    exists_actualSmallRoughRho_density_le_full_reserve nu ((19 / 96 : ℝ)/nu)
      (eps/2) betaMax hnu (div_pos (by norm_num) hnu) (half_pos heps) hMax
  obtain ⟨r0,hr0⟩ := exists_ordinary_source_gain (eps/2) (half_pos heps)
  refine ⟨beta,hb,hb8,hbMax,hbr,r0,?_⟩
  intro r hr
  obtain ⟨n0,hn0⟩ := hr0 r hr
  refine ⟨n0,?_⟩
  intro n hn
  obtain ⟨e0,he0,h⟩ := hn0 n hn
  refine ⟨e0,he0,?_⟩
  intro e he hee
  obtain ⟨q0,hq0,hq⟩ := h e he hee
  refine ⟨q0,hq0,?_⟩
  intro q hqq om hom
  obtain ⟨Na,hNa,ha⟩ := hq q hqq om hom
  refine ⟨max Na Nb, hNa.trans (le_max_left _ _),?_⟩
  intro N hN hEven cap hcap
  have h2 : 2 ≤ N := hNa.trans ((le_max_left _ _).trans hN)
  have hNr : 1 < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
  have hz := Real.rpow_le_rpow_of_exponent_le hNr.le (show mu ≤ (19/96 : ℝ) by norm_num [mu])
  have hraw := ha N ((le_max_left _ _).trans hN) hEven cap _ hz hcap
  rw [P5OriginalCommonPositivePresieve.normalize_sub] at hraw
  have hbetaN := hbeta N ((le_max_right _ _).trans hN) hEven cap
    (by simpa only [hnr] using hcap) (policy (width r) n e q om (N : ℝ) false)
  dsimp only at hbetaN
  simp only [hnr] at hbetaN
  change P4AOriginalVariableFifthPhysicalLedger.physical (policy (width r) n e q om (N : ℝ)) N cap
      ((N : ℝ)^(nu * beta^2)) ((N : ℝ)^(19/96 : ℝ)) ((N : ℝ)^(nu * beta)) ≤
    raw (policy (width r) n e q om (N : ℝ)) N cap 0 ((N : ℝ)^(19/96 : ℝ)) +
      (eps/2) * singularSeries N / Real.log (N : ℝ) at hbetaN
  have hnorm := P5OriginalCommonPositivePresieve.normalize_mono N h2 hbetaN
  rw [P5OriginalCommonPositivePresieve.normalize_add,P5OriginalCommonPositivePresieve.normalize_reserve N h2] at hnorm
  refine ⟨Real.one_lt_rpow hNr (mul_pos hnu (sq_pos_of_pos hb)), ?_, ?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hNr.le
    simpa only [hnr] using mul_le_mul_of_nonneg_left hbr hnu.le
  · linarith only [hnorm,hraw]

end
end ImbalancedChen.P4AOriginalFull87ActualGain
