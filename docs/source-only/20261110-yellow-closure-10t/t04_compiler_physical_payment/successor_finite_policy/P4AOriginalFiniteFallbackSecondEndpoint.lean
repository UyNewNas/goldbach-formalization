import ImbalancedChen.P4AOriginalFiniteFallbackCompactRows

namespace ImbalancedChen.P4AOriginalFiniteFallbackSecondEndpoint
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFiniteFallbackOwnCubeRows (pairPoint)
open P4AOriginalFiniteFallbackSmallThird (diff)
open P4AOriginalFiniteFallbackSignedSource (sum)
open P4ACatalogFiveHistoricalPairBoundaryPayment (normalizedHistoricalEndpoint)
open P4ACatalogFiveActualPairDecomposition
open P4ACatalogFiveOmittedOrderPayment (endpointRow_normalized_eq_gated_difference)
open P4ACatalogFiveSmallThirdEndpointTail (tupleGuard)
open P4ACatalogFiveCoarseWeightedPayment (weight carrier candidateTuples)
open P5OriginalCommonRefinedConstructor (OriginalData old3)
open P5OriginalAboveMuThirdLowerPhysicalCoefficient (SecondRegion secondGuard)
open P4AOriginalRankThreeRestorationSource (beforeThirdPolicy candidates admittedTest)
open P1Pair12RetainedSignedSource (signedTest)
open HistoricalThirdCoarse.P1ActualTuple (history)
open P4AOriginalThirdFallbackAdmission (pre_eq)
open P5OriginalCommonPositivePresieve (normalize normalize_add)
open VariableEnvelope

def row (N : ℕ) (p : Fin 3 → ℕ) :=
  if tupleGuard N p then diff N p (v (actualPrimeTupleLog N p 0)) (v (actualPrimeTupleLog N p 1)) else 0

theorem guard_iff (N : ℕ) (p : Fin 3 → ℕ) :
    tupleGuard N p ↔ SecondRegion (actualPrimeTupleLog N p 0) (actualPrimeTupleLog N p 1) := by
  simp [tupleGuard,secondGuard,rosserAncestor,primeHistoryLogCoordinates,primeHistoryTuple,actualPrimeTupleLog]

theorem endpoint_sum (d : OriginalData) (N : ℕ) (hn : 1<N) :
    normalizedHistoricalEndpoint d N=sum d N (row N) := by
  let P := old3 d (N:ℝ)
  let G := endpointRow d N weight (fun _ _ => (1:ℝ))
  change normalize N (endpointSource d (N:ℝ) weight (fun _ _ => 1) (carrier N))=_
  rw [endpointSource_eq_candidate_sum]
  have hnorm (xs : List (FirstExitDepthState ℕ)) :
      normalize N (xs.map G).sum=(xs.map (fun s => normalize N (G s))).sum := by
    induction xs with
    | nil => simp [normalize]
    | cons s ss ih => simp only [List.map_cons,List.sum_cons,normalize_add,ih]
  rw [hnorm,sum,←firstExitRootFrontier_weighted_sum_eq_admitted_tuple_sum 3 (beforeThirdPolicy P)
    weight (carrier N) (roughPrimeUniverse_nodup _ _ _ _) (row N)]
  congr 1
  apply List.map_congr_left
  intro s hs
  obtain ⟨hl,_,_,_,_,_,hm⟩ := actualPrimeFrontier_geometry 3 (by omega)
    (beforeThirdPolicy P) N N (P4AOriginalFull87RawChronology.cutoff N) s hs
  let p := primeHistoryTuple 3 s.selectedPrefix
  have hp : s.selectedPrefix=history p := by rw [←pre_eq p,primeHistoryTuple_reverse_ofFn hl]
  have hc : p∈candidateTuples d N := by
    apply List.mem_toFinset.mpr; apply List.mem_map.mpr
    refine ⟨s.selectedPrefix.reverse,?_,?_⟩
    · exact (firstExitRootFrontier_admitted_history_perm 3 (beforeThirdPolicy P) weight (carrier N)).mem_iff.mp
        (List.mem_map.mpr ⟨s,hs,rfl⟩)
    · simp only [List.reverse_reverse]; rfl
  obtain ⟨_,hbox,_,_⟩ := P4AOriginalFiniteFallbackCandidate.geometry d hn hc
  have hpos (i : Fin 3) := (mem_actualPrimeBoxTuples_iff.mp hbox i).1.pos
  rw [←hm]
  by_cases hg : tupleGuard N p
  · exact (endpointRow_normalized_eq_gated_difference d N hn s hs p hp hpos (hp ▸ hg)).trans
      (by simp [row,hg,diff])
  · have hng : ¬secondGuard (N:ℝ) s.selectedPrefix := by simpa only [hp] using hg
    have hnode (new : Bool) : endpointPolicy d N new s.positive s.selectedPrefix=
        old3 d N s.positive s.selectedPrefix := by
      simp [endpointPolicy,firstExitDepthSplicePolicy,endpointReplacement,hng,show ¬s.selectedPrefix.length≤2 by omega]
    simp only [G,endpointRow,admittedTest,hnode,endpointPolicy_continuation d N false _ (by omega) weight _,
      endpointPolicy_continuation d N true _ (by omega) weight _,if_neg hng,sub_self,row,if_neg hg,mul_zero]
    simp [normalize]

end
end ImbalancedChen.P4AOriginalFiniteFallbackSecondEndpoint
