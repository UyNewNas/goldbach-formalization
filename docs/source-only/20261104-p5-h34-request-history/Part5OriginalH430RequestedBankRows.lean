import ImbalancedChen.Part5OriginalH430RequestedHistory

/-!
Finite connection of the generated bank requests to the EXISTING
cell-labelled production row. SOURCE ONLY / UNCOMPILED.
Fixed requests read specified cells; dynamic requests read the real
perform query. No bank candidate/quadrature/base licence is inferred.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedBankRows

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers P2EnhancedLowerPrimeChildGeometry
open Part5OriginalUpsilon5CausalDictionary
open Part5OriginalH430PrimeChildAdmission Part5OriginalH430IntegerItineraries
open Part5OriginalH430FixedReadDictionary Part5OriginalH430FixedReadRows
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430W1WindowDictionary
open Part5OriginalH430W1StrictRows
open Part5OriginalH430W2ProductionRows
open P2OriginalChildPhysicalNormalization

private theorem list_sum_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  change (s.val.toList.map f).sum = (s.val.map f).sum
  exact Multiset.sum_map_toList _ _

private theorem coords_w1 (N : ℕ) (i : Fin 7) (j : Fin 10) (q : Fin (N+1)) :
    edgeCoordinates (.w1Prime i j q) = singleCoordinates N q.val := by
  funext a
  fin_cases a <;> simp [edgeCoordinates,edgePrimes,singleCoordinates,physicalPrime]

private theorem coords_w2_single (N : ℕ) (j : Fin 36) (k : Fin 3) (q : Fin (N+1)) :
    edgeCoordinates (.w2Prime j k q) = singleCoordinates N q.val := by
  funext a
  fin_cases a <;> simp [edgeCoordinates,edgePrimes,singleCoordinates,physicalPrime]

private theorem coords_w2_pair (N : ℕ) (j : Fin 36) (k : Fin 4)
    (q : Fin (N+1) × Fin (N+1)) :
    edgeCoordinates (.w2Pair j k q) = pairCoordinates N q.1.val q.2.val := by
  funext a
  fin_cases a <;> rfl

def coefficient {N : ℕ} (Q : ℝ) (r : Request) (e : Edge N) (b : RowAtom) : ℝ :=
  edgeWeight e * thetaAtom N Q (parentProduct (nextRequest r e).old) * requestAtom (nextRequest r e) b

private theorem fixed_w1_coefficient (N : ℕ) (Q : ℝ) (r : Request)
    (i : Fin 7) (j : Fin 10) (b : RowAtom) :
    coefficient Q r (Edge.w1Fixed (N := N) i j) b =
      cellKernel (thetaAtom N Q (parentProduct r.old)) (w1Cell j) b := by
  by_cases hb : b = .inl (.inl (w1Cell j))
  all_goals simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,appendedWord,
    advance,childUpper,requestAtom,cellKernel,hb]

private theorem fixed_w2_coefficient (N : ℕ) (Q : ℝ) (r : Request)
    (j : Fin 36) (anchor : Bool) (b : RowAtom) :
    coefficient Q r (Edge.w2Fixed (N := N) j anchor) b =
      (if anchor then 4/5 else 1/5) *
        cellKernel (thetaAtom N Q (parentProduct r.old)) (w2Cell j anchor) b := by
  by_cases hb : b = .inl (.inl (w2Cell j anchor))
  all_goals cases anchor <;>
    simp_all [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,appendedWord,
      advance,childUpper,requestAtom,cellKernel,mul_assoc]

private theorem single_w1_coefficient {N : ℕ} {Q : ℝ} {r : Request}
    (hw : parentWindow N Q r.old r.node.physical.ceiling)
    (hL : residual r.node.physical = physicalLevel N Q r.old)
    (i : Fin 7) (j : Fin 10) (q : Fin (N+1)) (b : RowAtom) :
    coefficient Q r (.w1Prime i j q) b =
      match b with
      | .inl _ => 0
      | .inr a => atomTerm N Q r.old j a q.val/2 := by
  have hq := childQuery_is_physical hw hL i j q
  cases b with
  | inl a => simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,advance,childUpper,requestAtom]
  | inr a =>
      by_cases ha : childQuery Q r.old j q.val ∈ tableAtomSet true a
      all_goals
        simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,advance,childUpper,
          requestAtom,coords_w1,hq,appendedWord,edgePrimes,parentProduct,atomTerm,ha] <;> ring

private theorem single_w2_coefficient (N : ℕ) (Q : ℝ) (r : Request)
    (j : Fin 36) (k : Fin 3) (q : Fin (N+1)) (b : RowAtom) :
    coefficient Q r (.w2Prime j k q) b = match b with
      | .inl _ => 0
      | .inr a =>
          (if (perform r.node.physical (.w2Singleton j k) (singleCoordinates N q.val)).argument ∈
            tableAtomSet true a then thetaAtom N Q (parentProduct (singleWord r.old q.val)) else 0)/5 := by
  cases b with
  | inl a => simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,advance,childUpper,requestAtom]
  | inr a =>
      by_cases ha : (perform r.node.physical (.w2Singleton j k) (singleCoordinates N q.val)).argument ∈ tableAtomSet true a
      all_goals
        simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,advance,childUpper,
          requestAtom,coords_w2_single,appendedWord,edgePrimes,singleWord,ha] <;> ring

private theorem pair_w2_coefficient (N : ℕ) (Q : ℝ) (r : Request)
    (j : Fin 36) (k : Fin 4) (q : Fin (N+1) × Fin (N+1)) (b : RowAtom) :
    coefficient Q r (.w2Pair j k q) b = match b with
      | .inl a =>
          (if (perform r.node.physical (.w2Pair j k) (pairCoordinates N q.1.val q.2.val)).argument ∈
            tableAtomSet false a then thetaAtom N Q (parentProduct (pairWord r.old q.1.val q.2.val)) else 0)/5
      | .inr _ => 0 := by
  cases b with
  | inr a => simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,advance,childUpper,requestAtom]
  | inl a =>
      by_cases ha : (perform r.node.physical (.w2Pair j k) (pairCoordinates N q.1.val q.2.val)).argument ∈ tableAtomSet false a
      all_goals
        simp [coefficient,nextRequest,edgeWeight,edgeShape,edgeMode,advance,childUpper,
          requestAtom,coords_w2_pair,appendedWord,edgePrimes,pairWord,ha] <;> ring

/-- Equality BEFORE absolute values. The two fixed W2 reads retain
4/5 and1/5; every singleton/pair occurrence retains its single1/5. -/
theorem bank_edgeRow_eq {N : ℕ} {Q : ℝ} {r : Request}
    (hw : parentWindow N Q r.old r.node.physical.ceiling)
    (hL : residual r.node.physical = physicalLevel N Q r.old)
    (a : Original106Action) (b : RowAtom) :
    edgeRow Q r (bankEdges N Q r a) b = cellReadRow N Q r.old r.node.physical a b := by
  change ((bankEdges N Q r a).map (fun e => coefficient Q r e b)).sum = _
  rcases a with ⟨i,j⟩ | j
  · cases b with
    | inl b =>
        simp [bankEdges,w1Edges,List.map_map,Function.comp_def,fixed_w1_coefficient,
          single_w1_coefficient hw hL,cellReadRow,readFixed,dynamicRow,cellKernel]
    | inr b =>
        simp only [bankEdges,w1Edges,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
          fixed_w1_coefficient,single_w1_coefficient hw hL,list_sum_finset,
          cellReadRow,readFixed,dynamicRow,cellKernel,reduceCtorEq,if_false,zero_add]
        rw [← Finset.sum_div]
        rfl
  · cases b
    all_goals
      simp only [bankEdges,w2SingleEdges,w2PairEdges,List.map_append,List.sum_append,
        List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.map_map,Function.comp_def,
        fixed_w2_coefficient,single_w2_coefficient,pair_w2_coefficient,list_sum_finset,
        cellReadRow,readFixed,dynamicRow,productionSingleAtom,productionPairAtom,
        Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,if_true,if_false]
      simp [← Finset.sum_div,cellKernel] <;> ring

/-- The generated bank requests consume the actual old array and the
existing production row, not an independently declared ideal profile. -/
theorem bank_edgeValue_eq {N : ℕ} {Q : ℝ} {r : Request}
    (hw : parentWindow N Q r.old r.node.physical.ceiling)
    (hL : residual r.node.physical = physicalLevel N Q r.old)
    (a : Original106Action) (t : P2Selected430CausalOccurrenceExporter.Table) :
    edgeValue Q t r (bankEdges N Q r a) =
      cellReadProfile N Q r.old r.node.physical a (t true) (t false) := by
  rw [← edgeRow_value]
  simp_rw [bank_edgeRow_eq hw hL]
  exact cellReadRow_value _ _ _ _ _ _ _

end
end ImbalancedChen.Part5OriginalH430RequestedBankRows
