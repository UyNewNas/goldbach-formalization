import ImbalancedChen.P2FiniteMarkedGamma5SeedCellReadout
import ImbalancedChen.P2FiniteMarkedGamma5PrimeCube

namespace ImbalancedChen.P2FiniteMarkedGamma5SeedCellFibre
noncomputable section
open Finset
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430NativeQueryPaths (NativeSlot)
open Part5OriginalH430PhysicalRoots (Root sourceRoot)
open Part5OriginalH430FrozenRootRefinement (rootCode)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430SameQHistoryCells (cellQ)
open Part5OriginalH430TaggedArithmeticReceivers (originalBand original_band_geometry)
open P2FiniteMarkedGamma5NativeSeedSum (coordinateOld primeTuples)
open P2FiniteMarkedGamma5OrderedOldSlots (oldSlotEquiv coordinateOld_eq_ofFn)
open P2FiniteMarkedGamma5SeedAtlasFinitePP (Entry oldRank tailRank rank Tuple)
open P2FiniteMarkedGamma5ActualRadialAggregate (tuplePrefix)
open P2FiniteMarkedGamma5RadialNaturalMass (tupleValues)
open P2FiniteMarkedGamma5SeedCellReadout (nativePoint nativeDomain ordered_logs)
open P2FiniteMarkedGamma5RealSelectedPrefix (selected)
open P2FiniteMarkedGamma5ActualRootCells (originalRootCellBand mem_originalRootCellBand originalRootCellBand_Q)
open scoped Classical BigOperators

/-- The original old position of every native coordinate, including the root. -/
def oldValue {n N : ℕ} (v : Entry n) (u : Tuple N v)
    (z : NativeSlot v.val.1.val.1) : ℕ :=
  (u (Fin.castAdd (2+tailRank v) ((oldSlotEquiv v.val.1.val.1).symm z))).val

theorem nativePoint_eq {n N : ℕ} (v : Entry n) (u : Tuple N v) :
    nativePoint v u = fun z => physicalPrime N (oldValue v u z) := by
  funext z
  have H := congrFun (ordered_logs v u) ((oldSlotEquiv v.val.1.val.1).symm z)
  simpa only [Function.comp_apply,Equiv.apply_symm_apply] using H.symm

theorem prefix_iff {n N : ℕ} (v : Entry n) (root : Root) (t : ℝ) (u : Tuple N v)
    (x : NativeSlot v.val.1.val.1 → Fin (N+1)) :
    coordinateOld n root t ⟨v.val.1,x⟩ = tuplePrefix (k:=oldRank v) (r:=tailRank v) (tupleValues u) ↔
      ∀ z, (x z).val = oldValue v u z := by
  rw [coordinateOld_eq_ofFn]
  change List.ofFn (fun j => (x (oldSlotEquiv _ j)).val) =
    List.ofFn (fun j => (u (Fin.castAdd (2+tailRank v) j)).val) ↔ _
  constructor
  · intro h z
    have H := congrFun (List.ofFn_injective h) ((oldSlotEquiv v.val.1.val.1).symm z)
    simpa only [Equiv.apply_symm_apply,oldValue] using H
  · intro h
    apply congrArg List.ofFn
    funext j
    simpa only [oldValue,Equiv.symm_apply_apply] using h (oldSlotEquiv v.val.1.val.1 j)

private def recovered {n N : ℕ} (v : Entry n) (u : Tuple N v)
    (hu : ∀ j, (u j).val.Prime) (hM : (∏ j,(u j).val) ≤ 2*N) :
    NativeSlot v.val.1.val.1 → Fin (N+1) :=
  fun z => ⟨oldValue v u z,Nat.lt_succ_of_le
    (P2FiniteMarkedGamma5PrimeCube.prime_coordinates_le_target
      (k:=oldRank v) (r:=tailRank v) (fun j => (u j).val) hu hM _)⟩

/-- The exact arithmetic seed restrictions involve only its old primes.
Fresh and tail primes may share factors with the additive target. -/
def exactCell {n N : ℕ} (v : Entry n) (root : Root) (t : ℝ) (u : Tuple N v) : Prop :=
  oldValue v u (.inl ()) ∈ originalRootCellBand N n root t v.val.2.1 ∧
  (∀ z, (oldValue v u z).Coprime N) ∧
  nativePoint v u ∈ selected n root t v.val.1.val.1 v.val.1.val.2

theorem exactCell_native {n N : ℕ} (v : Entry n) (root : Root) (t : ℝ) (u : Tuple N v)
    (hN : 2 ≤ N) :
    exactCell v root t u ↔
      oldValue v u (.inl ()) ∈ originalBand N root ∧
      (∀ z, (oldValue v u z).Coprime N) ∧ nativePoint v u ∈ nativeDomain v root t := by
  rw [nativePoint_eq]
  unfold exactCell nativeDomain
  rw [nativePoint_eq,mem_originalRootCellBand]
  constructor
  · rintro ⟨⟨hp,hc⟩,hcop,hs⟩
    exact ⟨hp,hcop,⟨⟨original_band_geometry hN hp,hs⟩,hc⟩⟩
  · rintro ⟨hp,hcop,⟨⟨_,hs⟩,hc⟩⟩
    exact ⟨⟨hp,hc⟩,hcop,hs⟩

theorem exactCell_sameQ {n N : ℕ} {v : Entry n} {root : Root} {t : ℝ} {u : Tuple N v}
    (H : exactCell v root t u) :
    rootQ N n root t (oldValue v u (.inl ())) = cellQ N n v.val.2.1 :=
  originalRootCellBand_Q H.1

/-- At a fixed full labelled tuple this is the whole arithmetic fibre.
Its unique element is recovered coordinate by coordinate, even when prime
values repeat. This also works for every tail length including zero. -/
theorem fibre_iff {n N : ℕ} (v : Entry n) (root : Root) (t : ℝ) (u : Tuple N v)
    (hu : ∀ j, (u j).val.Prime) (hM : (∏ j,(u j).val) ≤ 2*N)
    (x : NativeSlot v.val.1.val.1 → Fin (N+1)) :
    (x ∈ primeTuples N root v.val.1 ∧
      rootCode n (sourceRoot root t (physicalPrime N (x (.inl ())).val)).physical.total = v.val.2.1 ∧
      (fun z => physicalPrime N (x z).val) ∈ selected n root t v.val.1.val.1 v.val.1.val.2 ∧
      coordinateOld n root t ⟨v.val.1,x⟩ = tuplePrefix (k:=oldRank v) (r:=tailRank v) (tupleValues u)) ↔
      exactCell v root t u ∧ x = recovered v u hu hM := by
  constructor
  · rintro ⟨hx,hc,hs,hw⟩
    have he := (prefix_iff v root t u x).mp hw
    have hx' : x = recovered v u hu hM := funext (fun z => Fin.ext (he z))
    subst x
    obtain ⟨hp,hps⟩ := (mem_filter.mp hx).2
    refine ⟨⟨mem_originalRootCellBand.mpr ⟨hp,hc⟩,fun z => (hps z).2,?_⟩,rfl⟩
    simpa only [nativePoint_eq] using hs
  · rintro ⟨⟨hp,hcop,hs⟩,rfl⟩
    have H := mem_originalRootCellBand.mp hp
    refine ⟨mem_filter.mpr ⟨mem_univ _,H.1,fun z => ⟨hu _,hcop z⟩⟩,H.2,?_,?_⟩
    · simpa only [nativePoint_eq] using hs
    · exact (prefix_iff _ _ _ _ _).mpr (fun _ => rfl)

/-- A constant weight on this fibre occurs once or zero times. The
outer arithmetic prime labels stay on their original bounded carrier. -/
theorem sum_fibre {n N : ℕ} (v : Entry n) (root : Root) (t : ℝ) (u : Tuple N v)
    (hu : ∀ j, (u j).val.Prime) (hM : (∏ j,(u j).val) ≤ 2*N) (w : ℝ) :
    (∑ x ∈ primeTuples N root v.val.1,
      if rootCode n (sourceRoot root t (physicalPrime N (x (.inl ())).val)).physical.total = v.val.2.1 ∧
         (fun z => physicalPrime N (x z).val) ∈ selected n root t v.val.1.val.1 v.val.1.val.2 ∧
         coordinateOld n root t ⟨v.val.1,x⟩ = tuplePrefix (k:=oldRank v) (r:=tailRank v) (tupleValues u)
      then w else 0) = if exactCell v root t u then w else 0 := by
  rw [← Finset.sum_filter]
  let G := (primeTuples N root v.val.1).filter (fun x =>
    rootCode n (sourceRoot root t (physicalPrime N (x (.inl ())).val)).physical.total = v.val.2.1 ∧
    (fun z => physicalPrime N (x z).val) ∈ selected n root t v.val.1.val.1 v.val.1.val.2 ∧
    coordinateOld n root t ⟨v.val.1,x⟩ = tuplePrefix (k:=oldRank v) (r:=tailRank v) (tupleValues u))
  change (∑ _x ∈ G,w) = _
  have H (x) : x ∈ G ↔ exactCell v root t u ∧ x = recovered v u hu hM :=
    mem_filter.trans (fibre_iff v root t u hu hM x)
  by_cases hf : exactCell v root t u
  · have he : G = {recovered v u hu hM} := by ext x; simp [H,hf]
    simp [he,hf]
  · have he : G = ∅ := by ext x; simp [H,hf]
    simp [he,hf]

end
end ImbalancedChen.P2FiniteMarkedGamma5SeedCellFibre
