import ImbalancedChen.Part5OriginalH430OwnedThetaWord

/-! Multiplicity in the literal selected request list at a fixed root. -/
namespace ImbalancedChen.Part5OriginalH430EmittedPathMultiplicity
noncomputable section
open scoped Classical BigOperators
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerPrimeChildCarriers
open P2Selected430CausalOccurrenceExporter P5OriginalActionMassBound
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430OwnedThetaWord
open Part5OriginalH430PhysicalRoots

abbrev Letter := StepShape × ℕ × ℕ

def letter {N : ℕ} (e : Edge N) : Letter :=
  (edgeShape e,edgePrimes e 0,edgePrimes e 1)

def itinerary {N : ℕ} (o : Occurrence N) : List Letter := o.path.map letter

private theorem map_distinct {A B : Type*} (f : A → B) (l : List A)
    (hf : Function.Injective f) (hl : l.Nodup) : (l.map f).Nodup := by
  refine (List.nodup_map_iff_inj_on hl).2 ?_
  exact fun _ _ _ _ h => hf h

private theorem singleDistinct {N : ℕ} (shape : StepShape) (S : Finset (Fin (N+1))) :
    (S.toList.map (fun p => (shape,p.val,1:ℕ))).Nodup := by
  apply map_distinct _ _ _ (by simp)
  intro p q h
  exact Fin.ext (congrArg (fun z : Letter => z.2.1) h)

private theorem pairDistinct {N : ℕ} (shape : StepShape)
    (S : Finset (Fin (N+1) × Fin (N+1))) :
    (S.toList.map (fun p => (shape,p.1.val,p.2.val))).Nodup := by
  apply map_distinct _ _ _ (by simp)
  intro p q h
  exact Prod.ext (Fin.ext (congrArg (fun z : Letter => z.2.1) h))
    (Fin.ext (congrArg (fun z : Letter => z.2.2) h))

private theorem bank_distinct (N : ℕ) (Q : ℝ) (r : Request) (a : Original106Action) :
    ((bankEdges N Q r a).map letter).Nodup := by
  cases a with
  | inl ij =>
    rcases ij with ⟨i,j⟩
    simp only [bankEdges,w1Edges,List.map_cons,List.map_map,List.nodup_cons]
    exact ⟨by simp [letter,edgeShape,edgePrimes,Function.comp_def], singleDistinct _ _⟩
  | inr j =>
    simp only [bankEdges,w2SingleEdges,w2PairEdges,List.map_append,List.map_map,
      List.map_cons,List.map_nil,Function.comp_def,letter,edgeShape,edgePrimes]
    simp [List.nodup_append, List.mem_append, List.mem_map, singleDistinct, pairDistinct,
      Matrix.cons_val_zero, Matrix.cons_val_one] <;> aesop
    
theorem children_itinerary_nodup (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    ((children N Q g r).map letter).Nodup := by
  unfold children
  cases hi : resolve (g+1) r with
  | none => simp
  | some i =>
    cases hd : (roundDecision (iterate g) r.node.upper i).choice with
    | retained => simp [branchEdges]
    | bank a => exact bank_distinct N Q r _
    | buchstab =>
      cases hu : r.node.upper <;>
        simp only [branchEdges,hu,List.map_map,Function.comp_def,letter,edgeShape,edgePrimes] <;>
        exact singleDistinct _ _

private theorem branch_words {E A : Type*} (c : E → A) (ls : List E)
    (T : E → List (List A)) (hc : (ls.map c).Nodup) (ht : ∀ e ∈ ls, (T e).Nodup) :
    (ls.flatMap (fun e => (T e).map (List.cons (c e)))).Nodup := by
  induction ls with
  | nil => simp
  | cons e es ih =>
    obtain ⟨he,hrest⟩ := List.nodup_cons.mp hc
    rw [List.flatMap_cons]
    apply List.nodup_append.mpr
    refine ⟨map_distinct _ _ (fun _ _ h => (List.cons.inj h).2)
      (ht e (List.mem_cons_self ..)), ih hrest (fun q hq => ht q (List.mem_cons_of_mem _ hq)), ?_⟩
    intro u hu v hv huv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hu
    obtain ⟨q,hq,hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hv
    exact he (List.mem_map.mpr ⟨q,hq,(List.cons.inj huv).1.symm⟩)

private theorem encoded_subtrees (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request)
    (edges : List (Edge N)) :
    ((edges.flatMap (fun e => (history N Q g (nextRequest r e)).map (prepend e))).map
        itinerary) =
      edges.flatMap (fun e => ((history N Q g (nextRequest r e)).map itinerary).map
        (List.cons (letter e))) := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.map_append,List.map_map,ih]
    rfl

/-- An element of the mapped list represents exactly one original position
at a fixed root and fixed ordered shape/prime word, including retained
cells whose indices disappear from the geometric StepShape. -/
theorem history_itinerary_nodup (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    ((history N Q g r).map itinerary).Nodup := by
  induction g generalizing r with
  | zero => simp [history]
  | succ g ih =>
    rw [history,List.map_cons,encoded_subtrees]
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨e,he,h⟩ := List.mem_flatMap.mp h
      obtain ⟨p,hp,hh⟩ := List.mem_map.mp h
      exact List.cons_ne_nil _ _ hh
    · exact branch_words letter _ _ (children_itinerary_nodup _ _ _ _)
        (fun e _ => ih (nextRequest r e))

/-- Sum of actual marks at positions with a specified code, before any
reindexing by products. -/
def fibreMark {N : ℕ} (key : List Letter) : List (Occurrence N) → ℝ
  | [] => 0
  | o :: os => (if itinerary o = key then mark o else 0) + fibreMark key os

private theorem fibre_zero {N : ℕ} (key : List Letter) (os : List (Occurrence N))
    (h : key ∉ os.map itinerary) : fibreMark key os = 0 := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    simp only [List.map_cons,List.mem_cons,not_or] at h
    simp only [fibreMark,if_neg (Ne.symm h.1),ih h.2,add_zero]

private theorem fibre_le {N : ℕ} (key : List Letter) (os : List (Occurrence N))
    (h : (os.map itinerary).Nodup) : fibreMark key os ≤ 1 := by
  induction os with
  | nil => exact zero_le_one
  | cons o os ih =>
    obtain ⟨ho,hs⟩ := List.nodup_cons.mp h
    by_cases hk : itinerary o = key
    · rw [fibreMark,if_pos hk,fibre_zero key os (hk ▸ ho),add_zero]
      exact history_mark_le_one o
    · simpa only [fibreMark,if_neg hk,zero_add] using ih hs

theorem rootHistory_itinerary_mass_le_one (N n : ℕ) (k : Root) (tau : ℝ) (p : ℕ)
    (key : List Letter) : fibreMark key (rootHistory N n k tau p) ≤ 1 :=
  fibre_le _ _ (history_itinerary_nodup ..)

end
end ImbalancedChen.Part5OriginalH430EmittedPathMultiplicity

