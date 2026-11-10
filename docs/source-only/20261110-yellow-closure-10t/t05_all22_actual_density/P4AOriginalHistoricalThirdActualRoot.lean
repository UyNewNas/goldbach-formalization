import ImbalancedChen.P4AOriginalHistoricalThirdMajorant

/-! The actual signed before-third sum is bounded by a single ordered
compact test on its own physical tuples. The cut a is positive and fixed
before the cap modulus. Omitted cells make zero contribution, and the
ideal upper is nonnegative there. -/
namespace ImbalancedChen.P4AOriginalHistoricalThirdActualRoot
noncomputable section
open Set Filter Topology
open scoped Classical BigOperators
open P4AOriginalHistoricalThirdMajorant
open P4AOriginalHistoricalThirdOccurrence
open P4AOriginalHistoricalFirstStop (initial_approx)
open P4AOriginalFull87RawChronology (rawRoot cutoff)
open P4AOriginalNewFifthUnion (original)
open P4ACatalogFiveCoarseResidualUniformity
open P4ACatalogFiveCoarseWeightedPayment (weight candidateTuples carrier)
open P4AOriginalRankThreeRestorationSource (beforeThirdPolicy)
open P5OriginalCommonRefinedConstructor
open P5OriginalCommonPositivePresieve (normalize normalize_sub)
open HistoricalThirdCoarse
open HistoricalThirdCoarse.P1ActualTuple (history history_log mem_gateRegion)
open P4AOriginalThirdFallbackAdmission (raw_eq)
open P4AOriginalFourPositiveEndpoints (original_root_add_third_le_original_positive_sum)

theorem row_upper (d : OriginalData) (he : 0≤(d.e:ℝ)) (hc : 0≤d.chi)
    (hf : (d.e:ℝ)+7*d.chi≤3/256) (ha : 0<d.omega) {N : ℕ} (hN : 1<N)
    (p : Fin 3 → ℕ) (hp : p∈primes d.omega N) (tol delta : ℝ) (htol : 0≤tol)
    (hwidth : 4*(d.e:ℝ)+6*d.chi≤delta)
    (har : ∀ l : ℝ,l≤thirdPrefixTheta →
      |actualPrimeTupleOwnCubeMinus N N l p-primeTupleMinusProfile l (actualPrimeTupleLog N p)|<tol)
    (hmove : ∀ l L : ℝ,l≤thirdPrefixTheta → L≤thirdPrefixTheta → |l-L|≤delta →
      |primeTupleMinusProfile l (actualPrimeTupleLog N p)-primeTupleMinusProfile L (actualPrimeTupleLog N p)|≤tol) :
    applied d N p ≤ ordered.indicator (profile d.omega) (actualPrimeTupleLog N p)+4*tol := by
  let t := actualPrimeTupleLog N p
  have hb := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  have hpos := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
  have hn : 0≤ordered.indicator (profile d.omega) t := by
    by_cases h : t∈ordered
    · rw [indicator_of_mem h]; exact profile_nonneg ha (hb 2).1
    · rw [indicator_of_notMem h]
  by_cases hd : p∈candidateTuples d N
  · rw [applied,if_pos hd,charge]
    by_cases hs : lit d N (history p)
    · rw [if_pos hs]
      have hanti := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr
        ((mem_firstExitAdmittedTuples_iff_of_decreasing 3 (beforeThirdPolicy (old3 d (N:ℝ)))
          (carrier N) (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hd).1
      have hx (i : Fin 3) : t i < 19/96 := (hb i).2
      have hg : t∈ordered := (mem_gateRegion 2 2 t).mpr ⟨hanti,by linarith [hx 0],
        by linarith [hx 0],by linarith [hx 0,hx 1,hx 2]⟩
      obtain ⟨rough,j,hj,ht⟩ := (P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mp hs
      have hlevel : originalSeed d (N:ℝ) (history p)=levelExponent (d.e:ℝ) (box d.m j) := by
        have hpow := (raw_eq d N p).symm.trans (rawLevel_triple_on_cell
          (d.e:ℝ) d.chi d.m d.omega (N:ℝ) (p 0) (p 1) (p 2) rough j hj ht)
        have hn : (1:ℝ)<N := by exact_mod_cast hN
        exact le_antisymm ((Real.rpow_le_rpow_left_iff hn).mp hpow.le)
          ((Real.rpow_le_rpow_left_iff hn).mp hpow.ge)
      have hgeo := (mem_cells (d.e:ℝ) d.chi d.m j).mp hj
      have hl := gamma_le_cap _ _ he hgeo.1 hgeo.2.1
      let L := originalSeed d (N:ℝ) (history p)
      have hle : L≤thirdPrefixTheta := by
        change originalSeed _ _ _ ≤ _; rw [hlevel]
        dsimp [levelExponent,thirdPrefixTheta,VariableEnvelope.cap] at *; linarith
      have hmotion : |L-envelope t|≤delta := by
        change |originalSeed _ _ _ - _|≤_
        rw [hlevel]
        rw [history_log] at ht
        exact (cell_error he hc hf hj ht).trans hwidth
      have hnu : initial (d.e:ℝ) ≤ thirdPrefixTheta := by
        change thirdPrefixTheta-2*(d.e:ℝ)≤thirdPrefixTheta; linarith
      have hnu' : |initial (d.e:ℝ)-thirdPrefixTheta|≤delta := by
        change |thirdPrefixTheta-2*(d.e:ℝ)-thirdPrefixTheta|≤delta
        apply abs_le.mpr
        constructor <;> linarith
      have h1 := (abs_lt.mp (har (initial (d.e:ℝ)) hnu)).2
      have h2 := (abs_lt.mp (har L hle)).1
      have h3 := (abs_le.mp (hmove _ _ hnu le_rfl hnu')).2
      have h4 := (abs_le.mp (hmove _ _ hle (envelope_le t) hmotion)).1
      rw [indicator_of_mem hg,profile_eq ha (hb 2).1]
      change _-actualPrimeTupleOwnCubeMinus N N L p ≤ _
      linarith only [h1,h2,h3,h4]
    · rw [if_neg hs]
      linarith only [hn,htol]
  · rw [applied,if_neg hd]
    linarith only [hn,htol]

/-- The actual old3 of the enlarged policy has four original positive
suppliers. This cofinal bound needs no bridge to another mesh, root,
or small-third tail budget. -/
theorem exists_old3_le_positive (eta a : ℝ) (heta : 0<eta) (ha : 0<a) (har : a<thirdPrefixRho) :
    ∃ E : ℝ,0<E ∧ ∀ e : ℚ,0<(e:ℝ) → (e:ℝ)<E → ∃ q0 : ℕ,0<q0 ∧ ∀ q : ℕ,q0≤q →
      ∀ᶠ N : ℕ in atTop, Even N → normalize N (rawRoot (old3 (original e q a) (N:ℝ)) N) <
        (∑ i,currentUpperEighteenPositive i)+eta := by
  obtain ⟨M,hM,hm⟩ := exists_eventually_bounded_mass_of_tendsto
    (tendsto_actualPrimeBoxMass (fun _ : Fin 3 => a) (fun _ => thirdPrefixRho) (fun _ => ha) (fun _ => har))
  let tol := eta/(12*(M+1))
  have htol : 0<tol := by dsimp [tol]; positivity
  have hbound : M*(4*tol)≤eta/3 := by
    have hh : tol*(12*(M+1))=eta := div_mul_cancel₀ _ (by positivity)
    nlinarith only [hh,htol]
  obtain ⟨delta,hdelta,hmove⟩ := exists_actual_profile_cap_modulus a tol ha htol
  obtain ⟨Ni,hNi,haN⟩ := exists_all_caps_ownCube_uniform_threshold a tol ha htol
  obtain ⟨B,hB,hinit⟩ := initial_approx (eta/3) (by positivity)
  refine ⟨min B (min (delta/5) ((3/256)/100)),lt_min hB (lt_min (by positivity) (by norm_num)),?_⟩
  intro e he hE
  have hB' := hE.trans_le (min_le_left _ _)
  have hs := hE.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hwidth := hE.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨q0,hq0,_,hmesh⟩ := P4AActualRefinableArchivePayment.exists_actual_refinement_threshold (e:ℝ) he 0 0
  refine ⟨q0,hq0,?_⟩
  intro q hq
  let d := original e q a
  have hstart := hinit (e:ℝ) he hB' d.m (hmesh q hq).2
  have htest := (prime_limit ha har).eventually (gt_mem_nhds
    (by linarith only [test_integral_le ha,heta] : testIntegral a<actualExtendedThirdIdealFunctional+eta/3))
  filter_upwards [hstart,hm,htest,eventually_ge_atTop Ni] with N hi hmass ht hN hev
  have hN1 : 1<N := by omega
  have hcap := P4AOriginalFull87JointPhysicalBudget.cutoff_le_target N
    (by exact_mod_cast (show 1≤N by omega))
  have hsmall : d.chi < (d.e:ℝ)/10 := by change (e:ℝ)/20 < (e:ℝ)/10; linarith
  have hrow (p : Fin 3 → ℕ) (hp : p∈primes a N) := row_upper d he.le
    (show 0≤(e:ℝ)/20 by positivity) (show (e:ℝ)+7*((e:ℝ)/20)≤3/256 by linarith only [hs])
    ha hN1 p hp tol delta htol.le
    (show 4*(e:ℝ)+6*((e:ℝ)/20)≤delta by linarith only [hwidth,he])
    (haN N hN hev N hcap p hp)
    (fun l L hl hL hclose => hmove l L hl hL hclose _ (fun i =>
      let hc := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN1 _ _ p).mp hp).2 i
      ⟨hc.1,hc.2.le⟩))
  have hsum := Finset.sum_le_sum (s := primes a N) (fun p hp =>
    mul_le_mul_of_nonneg_left (hrow p hp) (actualPrimeBoxWeight_nonneg hp))
  simp_rw [mul_add] at hsum
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at hsum
  change _ ≤ testSum a N+actualPrimeBoxMass N (fun _ : Fin 3 => a) (fun _ => thirdPrefixRho)*(4*tol) at hsum
  have hraw := on_box d he hs hsmall hN1
  rw [normalize_sub] at hraw
  have hstart' := hi hev
  change normalize N (rawRoot (base d N) N) < _ at hstart'
  change normalize N (rawRoot (old3 d (N:ℝ)) N) < _
  linarith only [hraw,hsum,ht,hstart',original_root_add_third_le_original_positive_sum,hbound,
    mul_le_mul_of_nonneg_right hmass (show 0≤4*tol by positivity)]

end
end ImbalancedChen.P4AOriginalHistoricalThirdActualRoot
