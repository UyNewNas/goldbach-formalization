import ImbalancedChen.P4AOriginalFiniteFallbackSecondWalls

namespace ImbalancedChen.P4AOriginalFiniteFallbackSecondCompactPayment
noncomputable section
open scoped Classical BigOperators Topology
open Set Filter
open VariableEnvelope
open P4AOriginalFiniteFallbackOwnCubeRows (pairPoint old secondRow)
open P4AOriginalFiniteFallbackSmallThird (diff)
open P4AOriginalFiniteFallbackSecondEndpoint (row guard_iff)
open P4AOriginalFiniteFallbackSecondWalls (cube W gate proper missed endpoint_bound)
open P4AOriginalFiniteFallbackBank (read read_some_iff)
open P4AFallbackCanonicalBanks (bank second_some_iff meshCell_subset_closedBox)
open P4AFallbackOriginalCompactTrims (exists_second_core_owners)
open P4AFallbackJointFiniteCover (exists_endpoint_accuracy second_closed_error)
open P4AOriginalFiniteFallbackCanonical (selected_second)
open P5OriginalCommonRefinedConstructor (OriginalData)
open P4ACatalogFiveCoarseWeightedPayment (candidateTuples)
open P4ACatalogFiveSmallThirdEndpointTail (tupleGuard)
open P4ACatalogFivePrimeIntegral (trimBounds)
open P4AOriginalFiniteFallbackCandidate (high_upper)
open P4ACatalogFiveOmittedOrderPayment (candidate_cutoff_mem_box)

def S (d : OriginalData) (h : ℝ) (N : ℕ) := (candidateTuples d N).filter (fun p => h≤actualPrimeTupleLog N p 2)

theorem compact_payment (h eps : ℝ) (hh : 0<h) (hr : h<19/96) (heps : 0<eps) :
    ∃ m0 : ℕ,∀ m≥m0,∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,Even N → ∀ d : OriginalData,0≤(d.e:ℝ) →
      ∀ w : ℝ,w≤h → ∑ p∈S d h N,W p*(row N p-secondRow m d w N p)<eps := by
  obtain ⟨M,hM,hmass⟩ := exists_eventually_bounded_mass_of_tendsto
    (tendsto_actualPrimeBoxMass (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)) (fun _ => hh) (fun _ => hr))
  let eta := eps/(15*(M+1))
  have heta : 0<eta := div_pos heps (by linarith)
  obtain ⟨dc,hdc,Nc,hNc,hcomp⟩ := P4AOriginalFiniteFallbackCompactRows.compact h eta hh heta
  obtain ⟨C,hC,Nb,hNb,hbound⟩ := endpoint_bound h hh
  obtain ⟨δ,hδ,Ns,hNs,hstrip⟩ := exists_actualPrimeAffineWallStrip_mass_lt hh hr gate (trimBounds 0) proper
    (eps/(3*C)) (by positivity)
  obtain ⟨m1,_,hcover⟩ := exists_second_core_owners δ hδ
  obtain ⟨m2,hacc⟩ := exists_endpoint_accuracy dc hdc
  obtain ⟨Nm,hNm⟩ := eventually_atTop.mp hmass
  refine ⟨max m1 m2,?_⟩
  intro m hm
  refine ⟨max (max Nc Nb) (max Ns Nm),by omega,?_⟩
  intro N hN hEven d he w hw
  have hn : 1<N := by omega
  let strip := primeAffineWallStrip gate (trimBounds 0) δ
  let box := cube h N
  let carriers := S d h N
  have sub : carriers⊆box := by
    intro p hp
    obtain ⟨hc,hz⟩ := Finset.mem_filter.mp hp
    exact candidate_cutoff_mem_box d h N hn p hc hz
  have topV (x : ℝ) : v x≤thirdPrefixTheta := (v_le_cap _).trans (by norm_num [cap,thirdPrefixTheta])
  have H (p : Fin 3 → ℕ) (hp : p∈carriers) :
      row N p-secondRow m d w N p≤5*eta+(if actualPrimeTupleLog N p∈strip then C else 0) := by
    obtain ⟨hc,hz⟩ := Finset.mem_filter.mp hp
    have hext : 0≤(if actualPrimeTupleLog N p∈strip then C else 0) := by split <;> linarith
    cases h2 : read m (bank m).second (pairPoint N p) with
    | none =>
      rw [secondRow,h2,sub_zero]
      by_cases hg : tupleGuard N p
      · have hst := missed hδ N p hg h2 (hcover m (by omega))
        rw [if_pos (show actualPrimeTupleLog N p∈strip from hst)]
        linarith [hbound N (by omega) hEven p (sub hp)]
      · rw [row,if_neg hg]; linarith
    | some c =>
      have hgeom := selected_second h2
      have hg := (guard_iff N p).mpr hgeom.1
      have ho := high_upper hn he hc (hw.trans hz) hgeom.1.1
      obtain ⟨j,hj,hs⟩ := read_some_iff.mp h2
      obtain ⟨_,rfl⟩ := (second_some_iff m j c).mp hs
      have he' := second_closed_error m j _ (meshCell_subset_closedBox _ _ hj)
      have hacc' := hacc m (by omega)
      have near : |(P4AFallbackCanonicalBanks.level2 m j:ℝ)-v (actualPrimeTupleLog N p 1)|≤dc := by
        change |(P4AFallbackCanonicalBanks.level2 m j:ℝ)-v (pairPoint N p 1)|≤dc
        rw [abs_of_nonpos (by linarith [he'.1])]
        linarith [he'.2]
      have ha := (hcomp N (by omega) hEven p (sub hp) (old d w N p) _
        (v (actualPrimeTupleLog N p 0)) (v (actualPrimeTupleLog N p 1)) ho (topV _) hgeom.2.2.2.1.le (topV _) near).2
      rw [row,if_pos hg,secondRow,h2]
      linarith
  have hle := Finset.sum_le_sum (s:=carriers) (fun p hp => mul_le_mul_of_nonneg_left (H p hp)
    (actualPrimeBoxWeight_nonneg (sub hp)))
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun p => W p*
    (5*eta+(if actualPrimeTupleLog N p∈strip then C else 0))) sub
    (fun p hp _ => mul_nonneg (actualPrimeBoxWeight_nonneg hp) (by split_ifs <;> linarith))
  have heq : (∑ p∈box,W p*(5*eta+(if actualPrimeTupleLog N p∈strip then C else 0)))=
      actualPrimeBoxMass N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ))*(5*eta)+
      actualPrimeAffineWallStripMass N (fun _ : Fin 3 => h) (fun _ => (19/96:ℝ)) gate (trimBounds 0) δ*C := by
    simp only [mul_add,Finset.sum_add_distrib,actualPrimeBoxMass,actualPrimeAffineWallStripMass,
      Finset.sum_mul,Finset.sum_filter,mul_ite,mul_zero,ite_mul,zero_mul,box,strip,W,P4ACatalogFiveCoarseWeightedPayment.weight]
  rw [heq] at hsub
  have hm' := mul_le_mul_of_nonneg_right (hNm N (by omega)) (by linarith : 0≤5*eta)
  have hs' := (lt_div_iff₀ (by positivity : 0<3*C)).mp (hstrip N (by omega))
  have e' : eta*(15*(M+1))=eps := div_mul_cancel₀ eps (by linarith)
  change (∑ p∈carriers,W p*(row N p-secondRow m d w N p))<eps
  nlinarith only [hle.trans hsub,hm',hs',e',heta,heps]

end
end ImbalancedChen.P4AOriginalFiniteFallbackSecondCompactPayment
