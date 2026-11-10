import ImbalancedChen.P4AOriginalSavedSixthOccurrence
import ImbalancedChen.P1ActualUpperClosedParameterUniformity

/-! On the actual rank-six frontier a single compact ordinary quotient
estimate covers every saved row, target and old/new cap. The rounding
loss is paid against the whole six-prime mass once. -/
namespace ImbalancedChen.P4AOriginalSavedSixthActualGain
noncomputable section
open Filter Set MeasureTheory VariableEnvelope
open scoped Classical BigOperators Topology
open P4AOriginalSavedSixthHistoricalOwner (bank actual_owner)
open P4AOriginalSavedSixthPrimeMean (primes profile combined primeSum combined_eq bounds eventually_slot positive_owner)
open P4AOriginalSavedSixthIntegral (rowTest_le_actual_ordinary)
open P4AOriginalSavedSixthSourceGates (source_iff)
open P4AOriginalSavedSixthArchive (Row Source endpoint oldUpper)
open P4AOriginalSavedSixthOwnCaps (on_positive)
open P4AOriginalSavedSixthOccurrence (off_source original_raw_difference_eq_box)
open P4AOriginalSavedSixthSigned (pre old tupleResidual)
open P4AOriginalSavedSixthStage (level before)
open P4AOriginalNewFifthCoverage (Schedule)
open P4AOriginalFull87OrdinarySignedGain (weight)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P5OriginalCommonPositivePresieve (normalize)
open P1OriginalFifthGrid400RefinedFullBoxCover

abbrev low : ℝ := 1/50
abbrev high : ℝ := 1/5
theorem low_pos : 0<low := by norm_num
abbrev mass (N : ℕ) := actualPrimeBoxMass N (fun _ : Fin 6 => low) (fun _ => high)

private def window : Set (ℝ × ℝ) :=
  (Icc low (3 * high) ×ˢ Icc low high) ∩ {q | q.1 ≤ 3 * q.2}

/-- A single ordinary Rosser threshold precedes every target, word,
rounded policy and selected cap. -/
private theorem quotient_window (eta : ℝ) (heta : 0 < eta) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
      ∀ (p : Fin 6 → ℕ), (∀ i, 0 < p i) → ∀ L : ℝ,
      let t := actualPrimeTupleLog N p
      low ≤ t 5 → t 5 ≤ high → t 5 ≤ L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t → L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t ≤ 3 * t 5 →
      ∀ cap : ℕ, p 5 ≤ cap →
        |actualSmallRosserPlusDensity N cap (p 5 : ℝ) ((N : ℝ)^L / (∏ i, p i : ℕ)) *
          Real.log (N : ℝ) / singularSeries N - 4 / (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t)| < eta := by
  have compact : IsCompact window := (isCompact_Icc.prod isCompact_Icc).inter_right
    (isClosed_le continuous_fst (continuous_const.mul continuous_snd))
  obtain ⟨N0,hN0,h⟩ :=
    exists_p1_actualSmallRosserPlusDensity_cube_compact_normalized_threshold window compact
      (fun q hq => ⟨low_pos.trans_le hq.1.2.1, low_pos.trans_le hq.1.1.1, hq.2⟩) eta heta
  refine ⟨N0, hN0, ?_⟩
  intro N hN hEven p hp L
  dsimp only
  intro hcut hupper hlo hhi cap hcap
  let t := actualPrimeTupleLog N p
  have hpar : actualRosserQuotientParameters (N : ℝ) (∏ i, p i : ℕ) (p 5 : ℝ) L =
      (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t, t 5) := by
    change (L - Real.log (∏ i, p i : ℕ) / Real.log (N : ℝ), actualPrimeTupleLog N p 5) =
      (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 (actualPrimeTupleLog N p), actualPrimeTupleLog N p 5)
    rw [Certificates.P2OriginalSixthElevenLogSemantics.S6_eq_sum,actualPrimeTupleLog_sum_prod p hp]
  obtain ⟨hl,hc⟩ := actualRosserQuotientParameters_exact (N : ℝ) (∏ i, p i : ℕ) (p 5 : ℝ) L
    (by exact_mod_cast (show 1 < N by omega))
    (by exact_mod_cast Finset.prod_pos (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hp i))
    (by exact_mod_cast hp 5)
  rw [hpar] at hl hc
  have hwin : (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t, t 5) ∈ window :=
    ⟨⟨⟨hcut.trans hlo, hhi.trans (by change _ ≤ 3 * high; linarith)⟩, hcut, hupper⟩, hhi⟩
  have hcap' : (p 5 : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hcap
  have hh := h N hN hEven (L - Certificates.P2OriginalSixthElevenLogSemantics.S6 t, t 5) hwin cap (by simpa only [hc] using hcap')
  simpa only [hl,hc] using hh



theorem reciprocal_rounding {s M R : ℝ} {n : ℕ}
    (hs : low ≤ R-s) (hr : R≤M) (hM : M-2*width n < R) :
    4/(R-s)-4/(M-s) ≤ 20000*width n := by
  have hs' : low ≤ M-s := hs.trans (sub_le_sub_right hr _)
  have hR := low_pos.trans_le hs
  have hM' := low_pos.trans_le hs'
  have hden : (1/2500:ℝ) ≤ (R-s)*(M-s) := by
    have h := mul_le_mul hs hs' low_pos.le hR.le
    norm_num [low] at h
    exact h
  calc
    _ = 4*(M-R)/((R-s)*(M-s)) := by field_simp [hR.ne',hM'.ne'] <;> ring
    _ ≤ _ := (div_le_iff₀ (mul_pos hR hM')).mpr (by
      have hh := mul_le_mul_of_nonneg_left hden
        (show 0 ≤ 20000*width n from mul_nonneg (by norm_num) (width_pos n).le)
      linarith only [hM,hh])

theorem exists_test_lower (eta : ℝ) (heta : 0<eta) :
    ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ n : ℕ,4*width n < 1/1600 →
      ∀ e : ℚ,∀ q : ℕ,∀ a : ℝ, Schedule e q a →
      primeSum N ≤ normalize N (before n (bank e q a) N) +
        (20000*width n+2*eta)*mass N := by
  obtain ⟨N0,hN0,H⟩ := quotient_window eta heta
  refine ⟨N0,hN0,?_⟩
  intro N hN hev n hn e q a hs
  have hN1 : 1<N := by omega
  have hNr : (1:ℝ)<N := by exact_mod_cast hN1
  let E := 20000*width n+2*eta
  have hE : 0≤E := add_nonneg (mul_nonneg (by norm_num) (width_pos n).le)
    (mul_nonneg (by norm_num) heta.le)
  let d := bank e q a
  have hpoint (p : Fin 6 → ℕ) (hp : p∈primes N) :
      combined (actualPrimeTupleLog N p) ≤ tupleResidual n d N N p + E := by
    let t := actualPrimeTupleLog N p
    obtain ⟨hpri,_⟩ := (mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp
    have hpos (j) := (hpri j).1.pos
    by_cases ha : ∃ i : Row,Source i t
    · obtain ⟨i,hi⟩ := ha
      obtain ⟨ht,hg⟩ := (source_iff i t).mp hi
      let P := old n d (N:ℝ) (pre p)
      let R := level n d (N:ℝ) (pre p)
      let M := endpoint i t
      obtain ⟨_,hPo,hPR,hRM,hround,hsP,hsR⟩ := on_positive i hs.1 p ht hg
        (actual_owner i hs hN1 p hpos ht) n hn
      have hlt := bounds i ht 5
      have hu : t 5≤high := hlt.2.le.trans (by norm_num)
      have hcut : t 5 ≤ P-Certificates.P2OriginalSixthElevenLogSemantics.S6 t := hsP.le
      have hcutR : t 5 ≤ R-Certificates.P2OriginalSixthElevenLogSemantics.S6 t := hcut.trans (sub_le_sub_right hPR _)
      have hpcap : p 5≤N := by
        have hh := (actualPrimeTupleLog_rpow hN1 p hpos 5).symm.trans_le
          (Real.rpow_le_rpow_of_exponent_le hNr.le (hu.trans (by norm_num : high≤1)))
        exact_mod_cast (by simpa only [Real.rpow_one] using hh : (p 5:ℝ)≤N)
      have hold := H N hN hev p hpos P hlt.1 hu hcut ((sub_le_sub_right hPR _).trans hsR) N hpcap
      have hnew := H N hN hev p hpos R hlt.1 hu hcutR hsR N hpcap
      have hrnd := reciprocal_rounding (s:=Certificates.P2OriginalSixthElevenLogSemantics.S6 t) (hlt.1.trans hcutR) hRM hround
      have hP0 := low_pos.trans_le (hlt.1.trans hcut)
      have hM0 := low_pos.trans_le (hlt.1.trans (hcutR.trans (sub_le_sub_right hRM _)))
      have htprod : 0<∏ j,t j := Finset.prod_pos (fun j _ => low_pos.trans_le (bounds i ht j).1)
      have hpf : profile i t ≤ 4/(P-Certificates.P2OriginalSixthElevenLogSemantics.S6 t)-4/(M-Certificates.P2OriginalSixthElevenLogSemantics.S6 t) := by
        calc
          _ ≤ (4*(M-P)/((P-Certificates.P2OriginalSixthElevenLogSemantics.S6 t)*(M-Certificates.P2OriginalSixthElevenLogSemantics.S6 t)*(∏ j,t j)))*(∏ j,t j) :=
            mul_le_mul_of_nonneg_right (rowTest_le_actual_ordinary i ht hg hPo hP0) htprod.le
          _ = _ := by field_simp [hP0.ne',hM0.ne',htprod.ne'] <;> ring
      change combined t ≤ tupleResidual n d N N p + E
      rw [combined_eq i ht]
      simp only [tupleResidual,actualPrimeTupleInitialSaving,sub_mul,sub_div]
      change _ ≤ actualSmallRosserPlusDensity N N (p 5:ℝ) ((N:ℝ)^P/(∏ j,p j:ℕ))*
        Real.log (N:ℝ)/singularSeries N -
        actualSmallRosserPlusDensity N N (p 5:ℝ) ((N:ℝ)^R/(∏ j,p j:ℕ))*
        Real.log (N:ℝ)/singularSeries N + (20000*width n+2*eta)
      linarith only [hpf,hrnd,(abs_lt.mp hold).1,(abs_lt.mp hnew).2]
    · have hf : ∀ i : Row,¬Source i t := fun i hi => ha ⟨i,hi⟩
      have hzero : combined t=0 := by
        by_contra hz
        obtain ⟨i,ht,hg⟩ := positive_owner hz
        exact hf i ((source_iff i t).mpr ⟨ht,hg⟩)
      change combined t ≤ _
      rw [hzero,off_source n d N N p hf,zero_add]; exact hE
  rw [original_raw_difference_eq_box n hn hs hN1]
  calc
    _ ≤ ∑ p∈primes N,(∏ j,weight (p j))*(tupleResidual n d N N p+E) :=
      Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_left (hpoint p hp) (actualPrimeBoxWeight_nonneg hp))
    _ = _ := by simp only [mul_add,Finset.sum_add_distrib,←Finset.sum_mul,mass,actualPrimeBoxMass,E,weight]; ring

theorem exists_actual_saved_gain (eps : ℝ) (heps : 0<eps) :
    ∃ n0 : ℕ,∀ n≥n0,∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<1/64000 →
      ∃ q0 : ℕ,0<q0 ∧ ∀ q≥q0,∀ a : ℝ,a≤1/800 →
        ∀ᶠ N : ℕ in atTop,Even N → currentUpperEighteenGains 3-eps <
          normalize N (before n (bank e q a) N) := by
  let B := ∏ _j : Fin 6,Real.log (high/low)
  have hB : 0≤B := Finset.prod_nonneg (fun _ _ => Real.log_nonneg ((one_le_div low_pos).mpr (by norm_num)))
  have hBp : 0<B+1 := by linarith
  let eta := eps/(8*(B+1))
  have heta : 0<eta := div_pos heps (mul_pos (by norm_num) hBp)
  have hbudget : eta*(B+1)=eps/8 := by dsimp [eta]; field_simp [hBp.ne'] <;> ring
  have hm : ∀ᶠ N : ℕ in atTop,mass N<B+1 :=
    (tendsto_actualPrimeBoxMass (fun _ : Fin 6 => low) (fun _ => high)
      (fun _ => low_pos) (fun _ => by norm_num)).eventually
      (gt_mem_nhds (lt_add_one B))
  obtain ⟨Na,hNa,hA⟩ := exists_test_lower eta heta
  have hwidth : ∀ᶠ n : ℕ in atTop,width n < min (eta/20000) (1/6400) :=
    width_tendsto.eventually (gt_mem_nhds (lt_min (div_pos heta (by norm_num)) (by norm_num)))
  obtain ⟨n0,hN⟩ := eventually_atTop.mp hwidth
  refine ⟨n0,?_⟩
  intro n hn e he hel
  have h4 : 4*width n<1/1600 := by linarith only [(hN n hn).trans_le (min_le_right _ _)]
  have hh : 20000*width n<eta := by linarith only [(hN n hn).trans_le (min_le_left _ _)]
  obtain ⟨q0,hq0,hstep⟩ := exists_refinement_step_le_half ((e:ℝ)/10) (by positivity)
  refine ⟨q0,hq0,?_⟩
  intro q hq a ha
  have hqpos := hq0.trans_le hq
  have hmono : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ logPrimeMeshStep 0 (19/96) (refinedMesh q0) := by
    rw [refined_step q hqpos,refined_step q0 hq0]
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (by norm_num))
  have hs : Schedule e q a := ⟨by exact_mod_cast he.le,by exact_mod_cast hel.le,hqpos,
    hmono.trans (by linarith only [hstep]),ha⟩
  filter_upwards [eventually_ge_atTop Na,hm,eventually_slot (eps/4) (by positivity)] with N hN' hmN hpN
  intro hev
  have H := hA N hN' hev n h4 e q a hs
  have herr : (20000*width n+2*eta)*mass N ≤ (3*eta)*(B+1) :=
    mul_le_mul (by linarith) hmN.le (actualPrimeBoxMass_nonneg _ _ _) (by positivity)
  linarith only [hpN,H,herr,hbudget,heps]

end
end ImbalancedChen.P4AOriginalSavedSixthActualGain
