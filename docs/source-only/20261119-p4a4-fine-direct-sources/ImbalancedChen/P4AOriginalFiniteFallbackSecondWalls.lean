import ImbalancedChen.P4AOriginalFiniteFallbackSecondEndpoint

namespace ImbalancedChen.P4AOriginalFiniteFallbackSecondWalls
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open P4AOriginalFiniteFallbackOwnCubeRows (pairPoint old secondRow)
open P4AOriginalFiniteFallbackSmallThird (diff)
open P4AOriginalFiniteFallbackSecondEndpoint (row guard_iff)
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AFallbackCanonicalBanks (bank second_some_iff meshCell_subset_closedBox)
open P4AFallbackOriginalCompactTrims (secondCore exists_second_core_owners)
open P4AFallbackJointFiniteCover (exists_endpoint_accuracy second_closed_error)
open P4AOriginalFiniteFallbackCanonical (selected_second)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples weight)
open P4ACatalogFiveCoarseResidualUniformity (exists_all_caps_ownCube_uniform_threshold)
open P4ACatalogFiveSmallThirdEndpointTail (tupleGuard)
open P4ACatalogFivePrimeIntegral (trimForms trimBounds sourceRegion trimRegion)
open VariableEnvelope

abbrev cube (h : ℝ) (N : ℕ) := actualPrimeBoxTuples N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ))
abbrev W (p : Fin 3 → ℕ) := ∏ i,weight (p i)
def gate : Fin 4 → (Fin 3 → ℝ) →L[ℝ] ℝ :=
  ![-ContinuousLinearMap.proj 0,ContinuousLinearMap.proj 0,
    -(3:ℝ) • ContinuousLinearMap.proj 0-ContinuousLinearMap.proj 1,
    -ContinuousLinearMap.proj 0+ContinuousLinearMap.proj 1]

theorem proper (i : Fin 4) : gate i ≠ 0 := by
  fin_cases i <;> intro hh
  all_goals have H := congrArg (fun F : (Fin 3 → ℝ) →L[ℝ] ℝ => F ![1,0,0]) hh
  all_goals norm_num [gate] at H

theorem gate_eq (p : Fin 3 → ℕ) (N : ℕ) (i : Fin 4) :
    gate i (actualPrimeTupleLog N p)=trimForms i (pairPoint N p) := by fin_cases i <;> rfl

theorem missed {delta : ℝ} (hd : 0<delta) {m : ℕ} (N : ℕ) (p : Fin 3 → ℕ) (hg : tupleGuard N p)
    (hr : read m (bank m).second (pairPoint N p)=none)
    (hcover : ∀ t∈secondCore delta,∃! j,t∈logPrimeMeshCell 0 (19/96) m j ∧
      (bank m).second j=some (P4AFallbackCanonicalBanks.level2 m j)) :
    actualPrimeTupleLog N p∈primeAffineWallStrip gate (trimBounds 0) delta := by
  have hs : pairPoint N p∈sourceRegion :=
    (P4ACatalogFiveActualPairDecomposition.secondRegion_iff_catalog_domain _ _).mp ((guard_iff N p).mp hg)
  have hn : pairPoint N p∉trimRegion delta := by
    intro ht
    have hin : pairPoint N p∈secondCore delta := by
      refine ⟨((pairPoint N p) 0,(pairPoint N p) 1),ht,?_⟩
      funext i; fin_cases i <;> rfl
    obtain ⟨j,hj,_⟩ := hcover _ hin
    rw [P4AOriginalFiniteFallbackBank.read_on_cell hj.1,hj.2] at hr
    contradiction
  obtain ⟨j,hj⟩ := P4ACatalogFiveHistoricalPairBoundaryPayment.source_not_trim_in_wall hd hs hn
  exact ⟨j,by rwa [gate_eq]⟩

theorem endpoint_bound (h : ℝ) (hh : 0<h) :
    ∃ C : ℝ,0<C ∧ ∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ p∈cube h N,row N p≤C := by
  let T := 1/(2*Real.exp Real.eulerMascheroniConstant)
  let C := 2+4*T/h
  obtain ⟨N0,hN0,H⟩ := exists_all_caps_ownCube_uniform_threshold h 1 hh (by norm_num)
  refine ⟨C,by dsimp [C,T]; positivity,N0,hN0,?_⟩
  intro N hN hEven p hp
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hcap : (N:ℝ)^(19/96:ℝ)≤N := by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn
    (by norm_num : (19/96:ℝ)≤1)
  let t := actualPrimeTupleLog N p
  have hz : h≤t 2 := (mem_logPrimeBox.mp ((mem_actualPrimeBoxTuples_log_iff (by omega) _ _ p).mp hp).2 2).1
  have htop (L : ℝ) : v L≤thirdPrefixTheta := (v_le_cap _).trans (by norm_num [cap,thirdPrefixTheta])
  have ho := (abs_lt.mp (H N hN hEven N hcap p hp _ (htop (t 0)))).1
  have hn' := (abs_lt.mp (H N hN hEven N hcap p hp _ (htop (t 1)))).2
  have hlo (L : ℝ) : 0≤primeTupleMinusProfile L t := by
    rw [primeTupleMinusProfile_eq_extendedThirdFactor L t (hh.trans_le hz)]
    exact div_nonneg (mul_nonneg (by norm_num) (actualExtendedThirdLowerFactor_nonneg _)) (hh.trans_le hz).le
  have hhi (L : ℝ) : primeTupleMinusProfile L t≤4*T/h := by
    rw [primeTupleMinusProfile_eq_extendedThirdFactor L t (hh.trans_le hz)]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (actualExtendedThirdLowerFactor_le_normalization _) (by norm_num)) (hh.trans_le hz).le).trans
      (div_le_div_of_nonneg_left (by dsimp [T]; positivity) hh hz)
  unfold row
  split
  · unfold diff
    change _≤2+4*T/h
    linarith only [hlo (v (t 0)),hhi (v (t 1)),ho,hn']
  · dsimp [C,T]; positivity

end
end ImbalancedChen.P4AOriginalFiniteFallbackSecondWalls
