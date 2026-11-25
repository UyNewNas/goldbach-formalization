import ImbalancedChen.P2FiniteMarkedGamma5SeedCellFibre
import ImbalancedChen.P2FiniteMarkedGamma5SharpTupleCount
import ImbalancedChen.P2FiniteMarkedGamma5ActualPhysicalPlateau

namespace ImbalancedChen.P2FiniteMarkedGamma5TestedSeedAtom
noncomputable section
open Finset Real LiLiuPrereqBuchstab
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430FrozenRootRefinement (rootCode frozenLeafCutoffFloor frozenLeafCutoffFloor_pos)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedHistory Part5OriginalH430SeedHistoryMass
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels pair_eq)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FiniteMarkedGamma5NativeSeedSum (Index coordinateOld coordinatePath primeTuples literal_iff_selected)
open P2FiniteMarkedGamma5OrderedOldSlots (coordinateOld_length oldSlotEquiv)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple weight)
open P2FiniteMarkedGamma5RealSelectedPrefix (selected)
open P2FiniteMarkedGamma5SeedCellReadout (nativePoint nativeDomain planAt acceptAt actual_weight)
open P2FiniteMarkedGamma5SeedCellFibre (oldValue nativePoint_eq exactCell exactCell_native exactCell_sameQ prefix_iff)
open P2FiniteMarkedGamma5ActualRootCells (mem_originalRootCellBand)
open P2FiniteMarkedGamma5ActualRank
open P2FiniteMarkedGamma5ActualPhysicalPlateau
open P2FiniteMarkedGamma5LogExtension (sourcePair canonicalTail canonicalTail_list)
open P2FiniteMarkedGamma5EulerWordBudget (slotEquiv slotEquiv_old physicalToFin finPhysicalProfile)
open P2FiniteMarkedGamma5PhysicalExtension (Slot)
open P2FiniteMarkedGamma5SharpTupleCount (tupleFresh tupleTail tuple_list_decomposition)
open P2FiniteMarkedGamma5ActualRadialAggregate (tuplePrefix)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5AllRankEulerBudget (scaleThreshold)
open Part5OriginalCausalSmoothAtlas (Plan)
open Part5OriginalH430JointQueryEnclosure (Cube hit readout sharp_sandwich)
open scoped Classical BigOperators

private def values {k r : ℕ} (old qs : List ℕ) (m : ℕ)
    (hk : old.length=k) (hr : m.primeFactorsList.length=r) :
    Fin (k+(2+r)) → ℕ := fun j => match (slotEquiv k r).symm j with
  | .inl i => old.get (i.cast hk.symm)
  | .inr (.inl b) => sourcePair qs b
  | .inr (.inr b) => canonicalTail m (b.cast hr.symm)

private theorem blocks {k r : ℕ} (old qs : List ℕ) (m : ℕ)
    (hk : old.length=k) (hr : m.primeFactorsList.length=r)
    (hqs : qs=[qs.getD 0 0,qs.getD 1 0]) :
    let V := values old qs m hk hr
    tuplePrefix V = old ∧ [tupleFresh V 0,tupleFresh V 1]=qs ∧
      List.ofFn (tupleTail V)=m.primeFactorsList := by
  subst k; subst r
  dsimp only
  constructor
  · simpa only [tuplePrefix,← slotEquiv_old,values,Equiv.symm_apply_apply] using
      (List.ofFn_getElem (xs:=old))
  · constructor
    · simpa only [tupleFresh,values,Equiv.symm_apply_apply,sourcePair] using hqs.symm
    · simpa only [tupleTail,values,Equiv.symm_apply_apply] using canonicalTail_list m

private theorem flat_plateau {k r : ℕ} (old qs : List ℕ) (m : ℕ)
    (hk : old.length=k) (hr : m.primeFactorsList.length=r)
    (L N width b : ℝ)
    (H : finPhysicalProfile L N width b (physicalToFin (sourcePhysicalPoint old qs m))=1) :
    finPhysicalProfile L N width b (fun j => (values old qs m hk hr j:ℝ))=1 := by
  subst k; subst r
  have he : (fun j => (values old qs m rfl rfl j:ℝ)) =
      physicalToFin (sourcePhysicalPoint old qs m) := by
    funext j
    unfold physicalToFin values
    rcases (slotEquiv old.length m.primeFactorsList.length).symm j with a | a
    · rfl
    · rcases a with a | a <;> rfl
  rw [he]
  exact H

/-- On the actual selected old tuple, put back exactly the two original
fresh primes and m.primeFactorsList in its canonical order. The complete
product, both decoded source labels, and every old coordinate are retained.
The additive prime test therefore uses the identical integer N-M. -/
theorem original_atom {N n : ℕ} (hN : 2≤N) (t width : ℝ)
    (ht : 0≤t) (ht' : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hw : 0<width) (hw1 : width≤1)
    (hscale : scaleThreshold frozenLeafCutoffFloor≤(N:ℝ)) (mesh : Index 430→ℕ)
    (i : Index 430) (x : NativeSlot i.val.1 → Fin (N+1))
    (hx : x∈primeTuples N .U4 i)
    (hs : (fun z => physicalPrime N (x z).val) ∈ selected n .U4 t i.val.1 i.val.2)
    (qs : List ℕ) (m : ℕ)
    (hq : qs∈badLabels N (rootQ N n .U4 t (x (.inl ())).val)
      (coordinateOld n .U4 t ⟨i,x⟩).prod)
    (hm : m∈roughNumbers ((N:ℝ)/((coordinateOld n .U4 t ⟨i,x⟩).prod*qs.prod:ℕ))
      (cutoff (rootQ N n .U4 t (x (.inl ())).val) (coordinateOld n .U4 t ⟨i,x⟩).prod (227/50))) :
    ∃ (v : Entry n) (u : Tuple N v), v.val.1=i ∧
      u ∈ Part3.labelledPrimeTuples (rank v) (2*N) ∧ exactCell v .U4 t u ∧
      tuplePrefix (k:=oldRank v) (r:=tailRank v) (tupleValues u)=coordinateOld n .U4 t ⟨i,x⟩ ∧
      [tupleFresh (k:=oldRank v) (r:=tailRank v) (tupleValues u) 0,
       tupleFresh (k:=oldRank v) (r:=tailRank v) (tupleValues u) 1]=qs ∧
      List.ofFn (tupleTail (k:=oldRank v) (r:=tailRank v) (tupleValues u))=m.primeFactorsList ∧
      Part3.labelledProduct u=(coordinateOld n .U4 t ⟨i,x⟩).prod*qs.prod*m ∧
      1 ≤ weight v (planAt mesh v) width frozenLeafCutoffFloor_pos hw hw1
        (acceptAt .U4 t mesh v) N u := by
  let w := coordinateOld n .U4 t ⟨i,x⟩
  let p := (x (.inl ())).val
  have hp := (mem_filter.mp hx).2.1
  have hxpr := (mem_filter.mp hx).2.2
  obtain ⟨l,hl,hle⟩ := ((literal_iff_selected hN ht ht' hn i x).mpr
    ⟨⟨hp,hxpr⟩,hs⟩).2.1
  have hold : (levelOccurrence l).current.old = w := by
    change _ = (replay (rootRequest N n .U4 t p) (coordinatePath ⟨i,x⟩)).old
    rw [← hle]
    exact congrArg Request.old (history_facts (levelOccurrence_source l).1).2.2
  have hd : wordProduct l = w.prod := congrArg List.prod hold
  have hq' : qs∈badLabels N (rootQ N n .U4 t p) (wordProduct l) := by simpa only [hd] using hq
  have hm' : m∈roughNumbers ((N:ℝ)/(wordProduct l*qs.prod:ℕ))
      (cutoff (rootQ N n .U4 t p) (wordProduct l) (227/50)) := by simpa only [hd] using hm
  have hlen := coordinateOld_length n .U4 t i x
  have hr := enhanced_position_source_rank hN ht ht' hn hp l hq' hm'
  rw [hold,hlen] at hr
  let c := rootCode n (sourceRoot .U4 t (physicalPrime N p)).physical.total
  let v : Entry n := ⟨⟨i,c,⟨m.primeFactorsList.length,by omega⟩⟩,hr⟩
  let f : Fin (rank v) → ℕ := values w qs m (show w.length=oldRank v from hlen)
    (show m.primeFactorsList.length=tailRank v from rfl)
  have B := blocks w qs m (show w.length=oldRank v from hlen)
    (show m.primeFactorsList.length=tailRank v from rfl) (pair_eq (mem_filter.mp hq).1)
  obtain ⟨hprefix,hpair,htail⟩ := B
  have hlist : List.ofFn f = sourceSlots l qs m := by
    rw [tuple_list_decomposition,hprefix,hpair,htail]
    simp only [sourceSlots,hold]
  obtain ⟨hall,hprod,hcap,_⟩ := enhanced_position_source_data hN ht ht' hn hp l hq' hm'
  have prime (j) : (f j).Prime := (hall _ (hlist ▸ List.mem_ofFn.mpr ⟨j,rfl⟩)).1
  have hpf : (∏ j,f j) = wordProduct l*qs.prod*m := by
    simpa only [← List.prod_ofFn,hlist] using hprod
  have hc : (∏ j,f j) ≤ 2*N := by
    rw [← List.prod_ofFn,hlist]; omega
  let u : Tuple N v := fun j => ⟨f j,Nat.lt_succ_of_le (by
    exact (P2FiniteMarkedGamma5PrimeCube.prime_coordinates_le_target f prime hc j).trans
      (by omega))⟩
  have he := (prefix_iff v .U4 t u x).mp hprefix.symm
  have hnpt : nativePoint v u = fun z => physicalPrime N (x z).val := by
    rw [nativePoint_eq]
    funext z
    exact congrArg (physicalPrime N) (he z).symm
  have hex : exactCell v .U4 t u := by
    refine ⟨mem_originalRootCellBand.mpr ⟨?_,?_⟩,?_,?_⟩
    · simpa only [← he] using hp
    · simp only [← he]; rfl
    · intro z; simpa only [← he] using (hxpr z).2
    · simpa only [hnpt] using hs
  have hQ : rootQ N n .U4 t p = cellQ N n c := by
    simpa only [← he] using exactCell_sameQ hex
  have HP := enhanced_position_finPhysical_source_one hN ht ht' hn hp hw l hq' hm'
  rw [hold] at HP
  have hOne := flat_plateau w qs m (show w.length=oldRank v from hlen)
    (show m.primeFactorsList.length=tailRank v from rfl) _ _ _ _ HP
  rw [hQ] at hOne
  have hCube : Cube (nativePoint v u) := by
    rw [hnpt]
    intro z
    exact Part5OriginalH430SmoothPrefixRequests.physicalPrime_unit
      (by omega) (hxpr z).1.one_lt.le (Nat.lt_succ_iff.mp (x z).isLt)
  have hro := (sharp_sandwich (planAt mesh v) (nativeDomain v .U4 t) hCube).2
  rw [if_pos ((exactCell_native v .U4 t u hN).mp hex).2.2] at hro
  refine ⟨v,u,rfl,mem_filter.mpr ⟨mem_univ _,prime⟩,hex,hprefix,hpair,htail,?_,?_⟩
  · exact hpf.trans (by rw [hd])
  · rw [actual_weight v .U4 t mesh u width hw hw1 hscale (by omega)]
    change 1 ≤ finPhysicalProfile _ _ _ _ (fun j => (f j : ℝ)) * _
    rw [show finPhysicalProfile (log (cellQ N n c)) (N:ℝ) width ((N:ℝ)^frozenLeafCutoffFloor)
          (fun j => (f j:ℝ)) = 1 from hOne, one_mul]
    exact hro

end
end ImbalancedChen.P2FiniteMarkedGamma5TestedSeedAtom
