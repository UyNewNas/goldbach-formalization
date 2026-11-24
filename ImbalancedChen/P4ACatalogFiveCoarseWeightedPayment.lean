import ImbalancedChen.P4ACatalogFiveCoarseResidualUniformity
import ImbalancedChen.ActualHistoricalThirdTupleDictionary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Q's genuine rawLevel-to-endpoint estimate is lifted to the COMPLETE
coarseRow sum on P's actual before-third candidate List. An active triple
has p3 >= N^omega; fixing h <= omega therefore bounds every active mass
by the same three-dimensional actual prime box. This is an occurrence
preserving List-to-Finset use of the existing root-frontier dictionary.
Old-rejected own cubes are represented by zero gates, not old residuals.
No numerical or finite guard is evaluated here.
-/

namespace ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment
noncomputable section
open scoped Classical BigOperators
open Filter Topology VariableEnvelope HistoricalThirdCoarse
open P1Pair12RetainedSignedSource
open P5OriginalCommonRefinedConstructor P5OriginalCommonRefinedPreservation
open P5OriginalCommonThirdScreenedSource P5OriginalCommonFourthSourceLedger
open P5OriginalAboveMuThirdLowerPhysicalCoefficient
open P4AOriginalRankThreeRestorationSource P4ACatalogFiveActualPairDecomposition
open P4ACatalogFiveCoarseResidualUniformity

abbrev weight (p : ℕ) : ℝ := 1 / ((p : ℝ)-1)
abbrev carrier (N : ℕ) : List ℕ := roughPrimeUniverse N N 0 ((N : ℝ)^(19/96:ℝ))

def candidateTuples (d : OriginalData) (N : ℕ) : Finset (Fin 3 → ℕ) :=
  firstExitAdmittedTuples 3 (beforeThirdPolicy (old3 d (N : ℝ))) (carrier N)

def coarseAbsoluteSum (d : OriginalData) (N : ℕ) : ℝ :=
  ((candidates d (N : ℝ) weight (carrier N)).map (fun s =>
    |coarseRow d (N : ℝ) weight (fun _ _ => 1) s *
      Real.log (N : ℝ) / singularSeries N|)).sum

def activeMass (d : OriginalData) (N : ℕ) : ℝ :=
  ((candidates d (N : ℝ) weight (carrier N)).map (fun s =>
    if activeSecond d (N : ℝ) s.selectedPrefix then s.mass else 0)).sum

def admittedOrdinary (Q : ℝ) (N : ℕ) (s : FirstExitDepthState ℕ) : ℝ :=
  if ordinaryRosserPrefixAdmissible false Q s.selectedPrefix then
    signedTest (ordinaryParityRosserPolicy false Q) weight (fun _ _ => 1)
      s.selectedPrefix s.positive s.mass s.remaining
  else 0

/-- This local dictionary keeps the entire admitted continuation and the
strict own-cube gate. Its first cube is a separate, visible hypothesis,
supplied from the original selected cell at the actual caller below. -/
theorem admittedOrdinary_normalized
    (d : OriginalData) (N : ℕ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) weight (carrier N))
    (p : Fin 3 → ℕ) (hp : s.selectedPrefix = [p 2,p 1,p 0])
    (hp2 : 0 < p 2) (Q : ℝ) (hcube : (p 0 : ℝ)^3 < Q) :
    admittedOrdinary Q N s * Real.log (N : ℝ) / singularSeries N =
      -s.mass * rawGatedMinus N N Q p := by
  obtain ⟨hlen,hsort,_,_,_,hsign,hmass⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N : ℝ))) N N ((N : ℝ)^(19/96:ℝ)) s hs
  have h32 : p 2 < p 1 :=
    (List.pairwise_cons.mp (hp ▸ hsort)).1 _ (by simp)
  have h21 : p 1 < p 0 :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp (hp ▸ hsort)).2).1 _ (by simp)
  have hfalse : s.positive = false := by simpa [hp,evenListLength] using hsign
  have hgate : ordinaryRosserPrefixAdmissible false Q s.selectedPrefix ↔
      (∏ i, p i : ℕ) * (p 2 : ℝ)^2 < Q := by
    rw [hp,historicalUnorderedThird_admissible_iff Q (p 0) (p 1) (p 2) hp2 h32 h21]
    simp only [hcube,true_and]
    congr 1
    simp only [Fin.prod_univ_three,Nat.cast_mul]
    ring
  by_cases hg : ordinaryRosserPrefixAdmissible false Q s.selectedPrefix
  · have hd := firstExitRetainedPolynomial_frozenParity_frontier_density false 3
      (by omega) (beforeThirdPolicy (old3 d (N : ℝ))) (fun _ => Q)
      N N ((N : ℝ)^(19/96:ℝ)) s hs hg
    change firstExitRetainedPolynomial (ordinaryParityRosserPolicy false Q)
      weight s.selectedPrefix s.positive s.mass s.remaining = _ at hd
    rw [admittedOrdinary,if_pos hg,signedTest_one_eq_polynomial,hd,
      rawGatedMinus,if_pos (hgate.mp hg)]
    simp only [actualFrozenFrontierDensityTerm,← hmass,
      ← hsign,hfalse,signedTreeCoefficient,ordinaryRosserResidualLower,hlen,
      hp,List.headD_cons,List.prod_cons,List.prod_nil,mul_one,
      Fin.prod_univ_three,Nat.cast_mul]
    norm_num <;> ring
  · simp only [admittedOrdinary,if_neg hg,rawGatedMinus,
      if_neg (mt hgate.mpr hg),zero_mul,zero_div,mul_zero]

theorem old_admitted_eq_ordinary (d : OriginalData) (N : ℕ)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) weight (carrier N)) :
    admittedTest (old3 d (N : ℝ)) weight (fun _ _ => 1) s =
      admittedOrdinary (rawLevel (d.e:ℝ) d.chi d.m d.omega (N:ℝ) s.selectedPrefix) N s := by
  obtain ⟨hlen,_,_,_,_,hsign,_⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N : ℝ))) N N ((N : ℝ)^(19/96:ℝ)) s hs
  have hfalse : s.positive = false := by
    have hpar := signedTreeCoefficient_evenListLength_eq_negOnePow s.selectedPrefix (1:ℝ)
    cases hb : evenListLength s.selectedPrefix with
    | false => exact hsign.trans hb
    | true => rw [hb,hlen] at hpar; norm_num [signedTreeCoefficient] at hpar
  have hself := rosserAncestor_self_of_length 3 s.selectedPrefix hlen
  have hnode : old3 d (N : ℝ) s.positive s.selectedPrefix =
      ordinaryParityRosserPolicy false
        (rawLevel (d.e:ℝ) d.chi d.m d.omega (N:ℝ) s.selectedPrefix)
        s.positive s.selectedPrefix := by
    simp only [old3,HistoricalThirdCoarse.policy,thirdCappedUpperPolicy,
      firstExitDepthSplicePolicy,if_neg (by omega : ¬s.selectedPrefix.length ≤ 2),
      frozenParityRosserPolicy,ancestorFrozenPolicy,hself]
  rw [admittedTest,hnode]
  simp only [hfalse,ordinaryParityRosserPolicy,oddFirstExitPolicy,Bool.false_eq_true,if_false,
    decide_eq_true_eq]
  unfold admittedOrdinary
  simp only [hfalse]
  split_ifs
  · rw [P5OriginalCommonThirdActualLowerSource.old_third_continuation d (N:ℝ)
      _ (by omega),signedTest_one_eq_polynomial,signedTest_one_eq_polynomial,
      firstExitRetainedPolynomial_frozenParityRosser_eq false 3 _ _ _ _ _ _ hlen]
  · rfl

theorem endpoint_admitted_eq_ordinary (d : OriginalData) (N : ℕ) (new : Bool)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) weight (carrier N))
    (hg : secondGuard (N : ℝ) s.selectedPrefix) :
    admittedTest (endpointPolicy d (N : ℝ) new) weight (fun _ _ => 1) s =
      admittedOrdinary (pairCap (N : ℝ) new (rosserAncestor 2 s.selectedPrefix)) N s := by
  obtain ⟨hlen,_,_,_,_,hsign,_⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy (old3 d (N : ℝ))) N N ((N : ℝ)^(19/96:ℝ)) s hs
  have hfalse : s.positive = false := by
    have hpar := signedTreeCoefficient_evenListLength_eq_negOnePow s.selectedPrefix (1:ℝ)
    cases hb : evenListLength s.selectedPrefix with
    | false => exact hsign.trans hb
    | true => rw [hb,hlen] at hpar; norm_num [signedTreeCoefficient] at hpar
  have hnode : endpointPolicy d (N : ℝ) new s.positive s.selectedPrefix =
      ordinaryParityRosserPolicy false (pairCap (N : ℝ) new (rosserAncestor 2 s.selectedPrefix))
        s.positive s.selectedPrefix := by
    simp only [endpointPolicy,firstExitDepthSplicePolicy,
      if_neg (by omega : ¬s.selectedPrefix.length ≤ 2),endpointReplacement,if_pos hg,
      frozenParityRosserPolicy,ancestorFrozenPolicy]
  rw [admittedTest,hnode]
  simp only [hfalse,ordinaryParityRosserPolicy,oddFirstExitPolicy,Bool.false_eq_true,if_false,
    decide_eq_true_eq]
  unfold admittedOrdinary
  simp only [hfalse]
  split_ifs
  · rw [endpointPolicy_continuation d (N:ℝ) new _ (by omega),if_pos hg]
  · rfl

theorem endpoint_pairCap_cube (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ)
    (hpos : ∀ i, 0 < p i) (hg : secondGuard (N:ℝ) [p 2,p 1,p 0]) (new : Bool) :
    (p 0 : ℝ)^3 < pairCap (N:ℝ) new (rosserAncestor 2 [p 2,p 1,p 0]) := by
  have hr : SecondRegion (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1) := by
    simpa [secondGuard,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple,
      actualPrimeTupleLog] using hg
  have hc := above_mu_old_cap_gt_cube hr.1 hr.2.1
  have hn := new_cap_gt_old hr.1 hr.2.2.1 hr.2.2.2
  have hNr : (1:ℝ) < N := by exact_mod_cast hN
  have hpow : (p 0 : ℝ)^3 < (N:ℝ)^v (actualPrimeTupleLog N p 0) := by
    have hh := (Real.rpow_lt_rpow_left_iff hNr).mpr hc
    rw [mul_comm (3:ℝ),Real.rpow_mul (zero_lt_one.trans hNr).le,
      actualPrimeTupleLog_rpow hN p hpos 0,Real.rpow_natCast] at hh
    exact hh
  cases new with
  | false => simpa [pairCap,rosserAncestor,primeHistoryLogCoordinates,
      primeHistoryTuple,actualPrimeTupleLog] using hpow
  | true =>
      have hh := hpow.trans ((Real.rpow_lt_rpow_left_iff hNr).mpr hn)
      simpa [pairCap,rosserAncestor,primeHistoryLogCoordinates,
        primeHistoryTuple,actualPrimeTupleLog] using hh

/-- The actual coarseRow is identified after both admission gates; no
old prefix admission is imposed on the before-test candidate. -/
theorem coarseRow_normalized_eq_gated_difference
    (d : OriginalData) (N : ℕ) (hN : 1 < N) (s : FirstExitDepthState ℕ)
    (hs : s ∈ candidates d (N : ℝ) weight (carrier N))
    (p : Fin 3 → ℕ) (hp : s.selectedPrefix = [p 2,p 1,p 0])
    (hpos : ∀ i, 0 < p i) (ha : activeSecond d (N : ℝ) s.selectedPrefix)
    (hcube : (p 0 : ℝ)^3 < rawLevel (d.e:ℝ) d.chi d.m d.omega (N:ℝ) s.selectedPrefix) :
    coarseRow d (N : ℝ) weight (fun _ _ => 1) s *
      Real.log (N : ℝ) / singularSeries N = s.mass *
      (actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 0)) p -
        rawGatedMinus N N (rawLevel (d.e:ℝ) d.chi d.m d.omega (N:ℝ) s.selectedPrefix) p) := by
  have hg : secondGuard (N:ℝ) [p 2,p 1,p 0] := hp ▸ ha.2
  have hc := endpoint_pairCap_cube N hN p hpos hg false
  have hQ : pairCap (N:ℝ) false (rosserAncestor 2 s.selectedPrefix) =
      (N:ℝ)^v (actualPrimeTupleLog N p 0) := by
    simp [hp,pairCap,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]
  rw [coarseRow,if_pos ha,sub_mul,sub_div,old_admitted_eq_ordinary d N s hs,
    endpoint_admitted_eq_ordinary d N false s hs ha.2]
  rw [admittedOrdinary_normalized d N s hs p hp (hpos 2) _ hcube,
    admittedOrdinary_normalized d N s hs p hp (hpos 2) _ (by simpa only [hp] using hc),hQ]
  change -s.mass * _ - -s.mass * actualPrimeTupleOwnCubeMinus N N _ p = _
  ring

/-- The active actual tuple carrier lies in one fixed positive box. -/
theorem active_candidate_tuple_mem_box
    (d : OriginalData) (h : ℝ) (hhomega : h ≤ d.omega)
    (N : ℕ) (hN : 1 < N) (p : Fin 3 → ℕ)
    (hp : p ∈ candidateTuples d N)
    (ha : activeSecond d (N : ℝ) (List.ofFn p).reverse) :
    p ∈ actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)) := by
  have hm := (mem_firstExitAdmittedTuples_iff_of_decreasing 3
    (beforeThirdPolicy (old3 d (N:ℝ))) (carrier N)
    (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hp
  have hpre : (List.ofFn p).reverse = [p 2,p 1,p 0] := by simp [List.ofFn_succ]
  have hsel : selectedThird d (N:ℝ) [p 2,p 1,p 0] := hpre ▸ ha.1
  have hsupport : P1ThirdFallbackSupport.supported (d.e:ℝ) d.chi d.m d.omega
      (N:ℝ) [p 2,p 1,p 0] := by
    simpa only [selectedThird,P1ThirdFallbackSupport.frozenSupported,
      rosserAncestor_self_of_length 3 _ (by simp)] using hsel
  have hrough := ((P1ThirdFallbackSupport.supported_triple _ _ _ _ _ _ _ _).mp hsupport).1
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN.le
  have hlow : (N:ℝ)^h ≤ (p 2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hNr hhomega).trans hrough
  apply mem_actualPrimeBoxTuples_iff.mpr
  intro i
  have hi := mem_roughPrimeUniverse.mp (hm.2.1 i)
  have hlast : p 2 ≤ p i := hm.1.antitone (by omega)
  exact ⟨hi.2.1,hi.2.2.1,hlow.trans (by exact_mod_cast hlast),hi.2.2.2.2⟩

theorem activeMass_le_box (d : OriginalData) (h : ℝ) (hhomega : h ≤ d.omega)
    (N : ℕ) (hN : 1 < N) :
    activeMass d N ≤ actualPrimeBoxMass N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)) := by
  have hmass : activeMass d N =
      ∑ p ∈ (candidateTuples d N).filter
        (fun p => activeSecond d (N:ℝ) (List.ofFn p).reverse),
        ∏ i, 1 / ((p i : ℝ)-1) := by
    have h := firstExitRootFrontier_history_sum_eq_admitted_tuple_sum 3
      (beforeThirdPolicy (old3 d (N:ℝ))) weight (carrier N)
      (roughPrimeUniverse_nodup _ _ _ _)
      (fun pre => if activeSecond d (N:ℝ) pre then (1:ℝ) else 0)
    rw [Finset.sum_filter]
    convert h using 1
    · unfold activeMass candidates
      congr 1
      apply List.map_congr_left
      intro s hs
      have hm := (actualPrimeFrontier_geometry 3 (by omega)
        (beforeThirdPolicy (old3 d (N:ℝ))) N N ((N:ℝ)^(19/96:ℝ)) s hs).2.2.2.2.2.2
      split_ifs <;> simp [hm]
    · apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
  rw [hmass]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    exact active_candidate_tuple_mem_box d h hhomega N hN p
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  · intro p hp _
    exact actualPrimeBoxWeight_nonneg hp

private theorem list_sum_le (L : List (FirstExitDepthState ℕ))
    (f g : FirstExitDepthState ℕ → ℝ) (hfg : ∀ s ∈ L, f s ≤ g s) :
    (L.map f).sum ≤ (L.map g).sum := by
  revert hfg
  induction L with
  | nil => intro hfg; simp
  | cons s L ih =>
      intro hfg
      simp only [List.map_cons,List.sum_cons]
      exact add_le_add (hfg s (by simp)) (ih (fun t ht => hfg t (by simp [ht])))

/-- One pre-N threshold controls the COMPLETE weighted coarse discrepancy
for every actual d with omega >= h and the explicit old buffer/mesh width.
No coarse-row error estimate is a hypothesis. -/
theorem exists_complete_coarseRow_payment (h epsilon : ℝ)
    (hh : 0 < h) (hhrho : h < (19/96:ℝ)) (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ d : OriginalData, h ≤ d.omega →
        0 < (d.e:ℝ) → (d.e:ℝ) < (3/256:ℝ)/100 → d.chi < (d.e:ℝ)/10 →
        (3/2:ℝ)*d.chi+2*(d.e:ℝ) ≤ delta →
      ∀ N : ℕ, N0 ≤ N → Even N → coarseAbsoluteSum d N < epsilon := by
  obtain ⟨M,hM,hmass⟩ := exists_eventually_bounded_mass_of_tendsto
    (tendsto_actualPrimeBoxMass (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ))
      (fun _ => hh) (fun _ => hhrho))
  obtain ⟨Nm,hNm⟩ := eventually_atTop.mp hmass
  let eta := epsilon/(M+1)
  have heta : 0 < eta := div_pos heps (by linarith)
  obtain ⟨delta,hd,Nr,hNr,hrow⟩ :=
    exists_actual_coarse_rawLevel_to_endpoint_threshold h eta hh heta
  refine ⟨delta,hd,max Nr Nm,hNr.trans (le_max_left _ _),?_⟩
  intro d hhomega he hesmall hchi hwidth N hN hEven
  have hN1 : 1 < N := by omega
  have hrowBound : ∀ s ∈ candidates d (N:ℝ) weight (carrier N),
      |coarseRow d (N:ℝ) weight (fun _ _ => 1) s * Real.log (N:ℝ) / singularSeries N| ≤
        eta * (if activeSecond d (N:ℝ) s.selectedPrefix then s.mass else 0) := by
    intro s hs
    by_cases ha : activeSecond d (N:ℝ) s.selectedPrefix
    · obtain ⟨hlen,_,_,_,_,_,hm⟩ := actualPrimeFrontier_geometry 3 (by omega)
        (beforeThirdPolicy (old3 d (N:ℝ))) N N ((N:ℝ)^(19/96:ℝ)) s hs
      let p := primeHistoryTuple 3 s.selectedPrefix
      have hp : s.selectedPrefix = [p 2,p 1,p 0] := by
        have hh := (primeHistoryTuple_reverse_ofFn hlen).symm
        simpa [List.ofFn_succ] using hh
      have htuple : p ∈ candidateTuples d N := by
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        refine ⟨s.selectedPrefix.reverse,?_,?_⟩
        · exact (firstExitRootFrontier_admitted_history_perm 3
            (beforeThirdPolicy (old3 d (N:ℝ))) weight (carrier N)).mem_iff.mp
              (List.mem_map.mpr ⟨s,hs,rfl⟩)
        · simp only [List.reverse_reverse]; rfl
      have hpre : (List.ofFn p).reverse = s.selectedPrefix := primeHistoryTuple_reverse_ofFn hlen
      have hb := active_candidate_tuple_mem_box d h hhomega N hN1 p htuple (hpre.symm ▸ ha)
      have hpos : ∀ i, 0 < p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hb i).1.pos
      obtain ⟨hc,hr⟩ := hrow d he hesmall hchi hwidth N ((le_max_left _ _).trans hN) hEven
        p hb (hp ▸ ha.1) (hp ▸ ha.2)
      rw [coarseRow_normalized_eq_gated_difference d N hN1 s hs p hp hpos ha (hp.symm ▸ hc),
        if_pos ha,abs_mul]
      have hw : 0 ≤ s.mass := by
        rw [hm,← primeHistoryTuple_reciprocal_mass hlen]
        exact actualPrimeBoxWeight_nonneg hb
      rw [abs_of_nonneg hw]
      have hr' : |actualPrimeTupleOwnCubeMinus N N (v (actualPrimeTupleLog N p 0)) p -
          rawGatedMinus N N (rawLevel (d.e:ℝ) d.chi d.m d.omega (N:ℝ) s.selectedPrefix) p| < eta := by
        rw [abs_sub_comm,hp]
        exact hr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hr'.le hw
    · simp [coarseRow,ha]
  have hsum := list_sum_le (candidates d (N:ℝ) weight (carrier N)) _ _ hrowBound
  have hfactor : ((candidates d (N:ℝ) weight (carrier N)).map
      (fun s => eta * (if activeSecond d (N:ℝ) s.selectedPrefix then s.mass else 0))).sum =
      eta * activeMass d N := by
    unfold activeMass
    induction candidates d (N:ℝ) weight (carrier N) with
    | nil => simp
    | cons s L ih => simp only [List.map_cons,List.sum_cons,ih]; ring
  rw [hfactor] at hsum
  have hA := (activeMass_le_box d h hhomega N hN1).trans (hNm N ((le_max_right _ _).trans hN))
  have hstrict : eta*M < epsilon := by
    calc
      eta*M < eta*(M+1) := mul_lt_mul_of_pos_left (by linarith) heta
      _ = epsilon := div_mul_cancel₀ _ (by linarith : M+1 ≠ 0)
  exact hsum.trans_lt ((mul_le_mul_of_nonneg_left hA heta.le).trans_lt hstrict)

end
end ImbalancedChen.P4ACatalogFiveCoarseWeightedPayment
