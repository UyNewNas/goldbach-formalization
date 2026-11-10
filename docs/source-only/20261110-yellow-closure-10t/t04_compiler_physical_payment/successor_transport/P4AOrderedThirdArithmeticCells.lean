import ImbalancedChen.P4AOrderedThirdArithmeticOccurrence

namespace ImbalancedChen.P4AOrderedThirdArithmeticCells
noncomputable section
open Set HistoricalThirdCoarse VariableEnvelope
open HistoricalThirdCoarse.P1ActualTuple (history history_log active_iff_log parent_two_iff mem_gateRegion)
open P5OriginalCommonRefinedConstructor
open P4AOriginalFull87RawChronology (rawRoot)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples)
open P4AOriginalRankThreeRestorationSource (beforeThirdPolicy)
open P5OriginalCommonPositivePresieve (normalize)
open P4AOriginalHistoricalThirdOccurrence (base primes)
open P4AOriginalHistoricalThirdMajorant (ordered)
open P4AOriginalOrderedThirdTable (Point retained capValue rawExponent atPoint atPoint_on_cell)
open P4AOrderedThirdArithmeticOccurrence (fresh region diff localDiff)
open scoped Classical BigOperators

theorem candidate_of_cell (d : OriginalData) (he : 0≤(d.e:ℝ)) (w : ℝ) {N : ℕ} (hN : 1<N)
    {p : Fin 3 → ℕ} (hp : p∈primes w N) {j : Cell d.m} (hj : j∈retained (d.e:ℝ) d.m)
    (ht : actualPrimeTupleLog N p∈region j) : p∈candidateTuples d N := by
  let t := actualPrimeTupleLog N p
  have hr := (Finset.mem_filter.mp hj).2.2
  have hp0 := mem_actualPrimeBoxTuples_iff.mp hp
  have hpos : ∀ i,0<p i := fun i => (hp0 i).1.pos
  have hNr : (1:ℝ)<N := by exact_mod_cast hN
  have hstop : firstStop (d.e:ℝ) d.m (N:ℝ) [p 0] :=
    (HistoricalThirdCoarse.P1ActualPartition.firstStop_iff_log _ _ N p).mpr
      ⟨j 0,(mem_logPrimeMeshCell.mp ht.1 0).1,(mem_logPrimeMeshCell.mp ht.1 0).2,hr⟩
  have hc := P5OriginalAboveMuThirdLowerPhysicalCoefficient.original_first_cube_from_stop he
    ((mem_logPrimeMeshCell.mp ht.1 0).2.le.trans hr)
  have hpar := (parent_two_iff (d.e:ℝ) d.chi d.m d.omega N p (hpos 0)).mpr
    ⟨first_cube_lt_level_of_exponent (p 0) hNr (actualPrimeTupleLog_rpow hN p hpos 0).symm.le hc,hstop⟩
  have hv : FirstExitValidSelection (beforeThirdPolicy (old3 d (N:ℝ))) [] true (List.ofFn p) := by
    simpa [List.ofFn_succ,FirstExitValidSelection,beforeThirdPolicy,firstExitDepthSplicePolicy,old3] using hpar
  have hcap : (N:ℝ)^thirdPrefixRho≤N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hNr.le
      (by norm_num [thirdPrefixRho] : thirdPrefixRho≤1)
  exact (mem_actualPrimeAdmittedTuples_iff_of_cutoff_le_cap 3 (beforeThirdPolicy (old3 d (N:ℝ)))
    N N 0 ((N:ℝ)^thirdPrefixRho) hcap p).mpr
    ⟨(actualPrimeTupleLog_strictAnti_iff hN p hpos).mp ((mem_gateRegion 2 2 t).mp ht.2).1,
      fun i => ⟨(hp0 i).1,(hp0 i).2.1,Nat.cast_nonneg _,(hp0 i).2.2.2⟩,hv⟩

def onCandidates (d : OriginalData) (w : ℝ) (N : ℕ) (p : Fin 3 → ℕ) :=
  if p∈candidateTuples d N then diff d w N p else 0

theorem on_candidates_eq (d : OriginalData) (he : 0≤(d.e:ℝ)) (w : ℝ) {N : ℕ} (hN : 1<N)
    {p : Fin 3 → ℕ} (hp : p∈primes w N) :
    onCandidates d w N p=∑ j∈retained (d.e:ℝ) d.m,localDiff d N j p := by
  let t := actualPrimeTupleLog N p
  have hb := mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff hN _ _ p).mp hp).2
  have hpos : ∀ i,0<p i := fun i => (mem_actualPrimeBoxTuples_iff.mp hp i).1.pos
  have ha := (active_iff_log hN w p hpos).mpr (hb 2).1
  by_cases hd : p∈candidateTuples d N
  · rw [onCandidates,if_pos hd,diff,rawExponent,if_pos ha,history_log]
    have hanti := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mpr
      ((mem_firstExitAdmittedTuples_iff_of_decreasing 3 (beforeThirdPolicy (old3 d (N:ℝ)))
        (carrier N) (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hd).1
    have hx (i : Fin 3) : t i<19/96 := (hb i).2
    have ho : t∈ordered := (mem_gateRegion 2 2 t).mpr ⟨hanti,by linarith [hx 0],
      by linarith [hx 0],by linarith [hx 0,hx 1,hx 2]⟩
    by_cases h : ∃ j∈retained (d.e:ℝ) d.m,t∈logPrimeMeshCell 0 (19/96) d.m j
    · obtain ⟨j,hj,ht⟩ := h
      rw [atPoint_on_cell hj ht,Finset.sum_eq_single_of_mem j hj]
      · rw [localDiff,if_pos (show t∈region j from ⟨ht,ho⟩)]
      · intro k hk hn
        exact if_neg (fun H : t∈region k => hn (logPrimeMeshCell_unique (by norm_num) H.1 ht))
    · rw [atPoint,dif_neg h,sub_self]
      symm
      apply Finset.sum_eq_zero
      intro k hk
      exact if_neg (fun H : t∈region k => h ⟨k,hk,H.1⟩)
  · rw [onCandidates,if_neg hd]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    exact if_neg (fun ht : t∈region j => hd (candidate_of_cell d he w hN hp hj ht))

theorem source_cells (d : OriginalData) (w : ℝ) (he : 0<(d.e:ℝ)) (hsmall : (d.e:ℝ)≤1/384)
    (hstep : logPrimeMeshStep 0 (19/96) d.m≤(d.e:ℝ)/2) {N : ℕ} (hN : 1<N) :
    normalize N (rawRoot (fresh d w N) N-rawRoot (base d N) N) =
      ∑ j∈retained (d.e:ℝ) d.m,∑ p∈primes w N,(∏ i,weight (p i))*localDiff d N j p := by
  rw [P4AOrderedThirdArithmeticOccurrence.source d w he hsmall hstep hN]
  let C := candidateTuples d N
  let S := C.filter (fun p => active w (N:ℝ) (history p))
  have hsub : S⊆primes w N := by
    intro p hp
    obtain ⟨hc,ha⟩ := Finset.mem_filter.mp hp
    have hg := (mem_firstExitAdmittedTuples_iff_of_decreasing 3 (beforeThirdPolicy (old3 d (N:ℝ)))
      (carrier N) (roughPrimeUniverse_pairwise_gt _ _ _ _) p).mp hc
    exact P4ACatalogFiveOmittedOrderPayment.candidate_cutoff_mem_box d w N hN p hc
      ((active_iff_log hN w p (fun i => (mem_roughPrimeUniverse_prime (hg.2.1 i)).pos)).mp ha)
  have hzero {p : Fin 3 → ℕ} (hc : p∈C) (hs : p∉S) : diff d w N p=0 := by
    have hh : ¬active w (N:ℝ) (history p) := fun ha => hs (Finset.mem_filter.mpr ⟨hc,ha⟩)
    simp [diff,rawExponent,hh]
  calc
    _ = ∑ p∈S,(∏ i,weight (p i))*diff d w N p := (Finset.sum_subset (Finset.filter_subset _ _)
      (fun p hp hn => by rw [hzero hp hn,mul_zero])).symm
    _ = ∑ p∈S,(∏ i,weight (p i))*onCandidates d w N p := Finset.sum_congr rfl
      (fun p hp => by rw [onCandidates,if_pos (Finset.mem_filter.mp hp).1])
    _ = ∑ p∈primes w N,(∏ i,weight (p i))*onCandidates d w N p := Finset.sum_subset hsub (by
      intro p hp hn
      by_cases hc : p∈C
      · rw [onCandidates,if_pos hc,hzero hc hn,mul_zero]
      · rw [onCandidates,if_neg hc,mul_zero])
    _ = ∑ p∈primes w N,∑ j∈retained (d.e:ℝ) d.m,(∏ i,weight (p i))*localDiff d N j p :=
      Finset.sum_congr rfl (fun p hp => by rw [on_candidates_eq d he.le w hN hp,Finset.mul_sum])
    _ = _ := Finset.sum_comm

end
end ImbalancedChen.P4AOrderedThirdArithmeticCells

