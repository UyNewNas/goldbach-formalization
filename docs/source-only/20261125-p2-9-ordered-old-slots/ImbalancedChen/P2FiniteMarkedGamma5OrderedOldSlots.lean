import ImbalancedChen.P2FiniteMarkedGamma5NativeSeedSum
import ImbalancedChen.Part5OriginalH430SmoothPrefixRequests
import Mathlib.Data.Fintype.EquivFin

namespace ImbalancedChen.P2FiniteMarkedGamma5OrderedOldSlots

noncomputable section
open Finset
open P2EnhancedLowerPhysicalTransition (StepShape)
open P2EnhancedLowerPrimeChildCarriers (physicalPrime)
open Part5OriginalH430NativeQueryPaths (arity NativeSlot nativeRank nativeRank_exact)
open Part5OriginalH430IntegerItineraries (appendedWord)
open Part5OriginalH430RequestedBranches (edgeShape edgePrimes)
open Part5OriginalH430RequestedHistory (rootRequest)
open Part5OriginalH430SmoothPrefixRequests (added replay_old_word)
open Part5OriginalH430PhysicalRoots (Root)
open P2FiniteMarkedGamma5FixedNativeItinerary
open P2FiniteMarkedGamma5NativeSeedSum
open scoped Classical BigOperators

/-- Stages stay in chronological order. Within a stage, rev on Fin 0/1/2
respectively contributes no slot, the single slot, or large then small. -/
def stageSlots {d : ℕ} (sh : Fin d → StepShape) (i : Fin d) :
    List (NativeSlot sh) :=
  List.ofFn fun j : Fin (arity (sh i)) => Sum.inr ⟨i,j.rev⟩

def wordSlots {d : ℕ} (sh : Fin d → StepShape) : List (NativeSlot sh) :=
  Sum.inl () :: (List.ofFn (stageSlots sh)).flatten

theorem length_wordSlots {d : ℕ} (sh : Fin d → StepShape) :
    (wordSlots sh).length = Nat.card (NativeSlot sh) := by
  rw [Nat.card_eq_fintype_card]
  change _ = nativeRank sh
  rw [nativeRank_exact]
  simp [wordSlots,stageSlots,List.map_ofFn,Function.comp_def,List.sum_ofFn,Nat.add_comm]

private theorem covers {d : ℕ} (sh : Fin d → StepShape) (j : NativeSlot sh) :
    j ∈ wordSlots sh := by
  rcases j with u | ⟨i,j⟩
  · cases u
    simp [wordSlots]
  · apply List.mem_cons_of_mem
    apply List.mem_flatten.mpr
    refine ⟨stageSlots sh i,List.mem_ofFn.mpr ⟨i,rfl⟩,?_⟩
    exact List.mem_ofFn.mpr ⟨j.rev,by simp⟩

/-- The forward map is get on the explicit ordered list. Cardinality
is used only to verify injectivity of this already specified map. -/
def oldSlotEquiv {d : ℕ} (sh : Fin d → StepShape) :
    Fin (Nat.card (NativeSlot sh)) ≃ NativeSlot sh :=
  let f := fun j : Fin (Nat.card (NativeSlot sh)) =>
    (wordSlots sh).get (j.cast (length_wordSlots sh).symm)
  Equiv.ofBijective f ((Fintype.bijective_iff_surjective_and_card f).mpr (by
    refine ⟨?_,by simp [Nat.card_eq_fintype_card]⟩
    intro t
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp (covers sh t)
    exact ⟨j.cast (length_wordSlots sh),hj⟩))

theorem ofFn_oldSlotEquiv {d : ℕ} (sh : Fin d → StepShape) :
    List.ofFn (oldSlotEquiv sh) = wordSlots sh := by
  apply List.ext_getElem
  · simp [length_wordSlots]
  · intro i h₁ h₂
    rw [List.getElem_ofFn]
    rfl

private theorem edge_word {N : ℕ} (s : StepShape) (hs : noTransport s)
    (a : Fin 200) (x : Fin (arity s) → Fin (N+1)) :
    appendedWord (edgeShape (edgeAt s hs a x)) (edgePrimes (edgeAt s hs a x)) =
      List.ofFn fun j : Fin (arity s) => (x j.rev).val := by
  cases s with
  | transport j => exact False.elim (hs j rfl)
  | _ => rfl

/-- No emitted-membership, ordering, or primality assumption is needed.
The original replay identity supplies every previous old coordinate. -/
theorem coordinateOld_eq_map {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (i : Index 430)
    (x : NativeSlot i.val.1 → Fin (N+1)) :
    coordinateOld n k t ⟨i,x⟩ = (wordSlots i.val.1).map (fun j => (x j).val) := by
  unfold coordinateOld
  rw [replay_old_word]
  change (x (.inl ())).val ::
    added (pathAt i.val.1 i.property i.val.2 x) = _
  simp only [wordSlots,List.map_cons,List.map_flatten,List.map_ofFn,Function.comp_def,
    added,pathAt,List.flatMap_def]
  apply congrArg (List.cons (x (.inl ())).val)
  apply congrArg List.flatten
  simp only [List.map_ofFn,Function.comp_def]
  apply congrArg List.ofFn
  funext j
  simpa only [stageSlots,List.map_ofFn,Function.comp_def] using
    edge_word (i.val.1 j) (i.property j) (i.val.2 j).1 (fun b => x (.inr ⟨j,b⟩))

theorem coordinateOld_eq_ofFn {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (i : Index 430)
    (x : NativeSlot i.val.1 → Fin (N+1)) :
    coordinateOld n k t ⟨i,x⟩ =
      List.ofFn (fun j => (x (oldSlotEquiv i.val.1 j)).val) := by
  rw [coordinateOld_eq_map,← ofFn_oldSlotEquiv]
  simp only [List.map_ofFn,Function.comp_def]

theorem coordinateOld_length {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (i : Index 430)
    (x : NativeSlot i.val.1 → Fin (N+1)) :
    (coordinateOld n k t ⟨i,x⟩).length = Nat.card (NativeSlot i.val.1) := by
  rw [coordinateOld_eq_ofFn,List.length_ofFn]

theorem coordinateOld_product {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (i : Index 430)
    (x : NativeSlot i.val.1 → Fin (N+1)) :
    (coordinateOld n k t ⟨i,x⟩).prod = ∏ j, (x (oldSlotEquiv i.val.1 j)).val := by
  rw [coordinateOld_eq_ofFn,List.prod_ofFn]

theorem coordinateOld_logs {N : ℕ} (n : ℕ) (k : Root) (t : ℝ) (i : Index 430)
    (x : NativeSlot i.val.1 → Fin (N+1)) :
    (coordinateOld n k t ⟨i,x⟩).map (physicalPrime N) =
      List.ofFn (fun j => physicalPrime N (x (oldSlotEquiv i.val.1 j)).val) := by
  rw [coordinateOld_eq_ofFn,List.map_ofFn]
  rfl

end
end ImbalancedChen.P2FiniteMarkedGamma5OrderedOldSlots
