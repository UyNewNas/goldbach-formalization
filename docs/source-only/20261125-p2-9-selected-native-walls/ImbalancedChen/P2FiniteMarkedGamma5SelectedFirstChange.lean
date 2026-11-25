import ImbalancedChen.P2FiniteMarkedGamma5SelectedQueryRows

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedFirstChange
noncomputable section
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalUpsilon5CausalDictionary Part5OriginalH430ClosedOwner
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430NativeQueryPaths Part5OriginalH430EmittedNativeQueries
open Part5OriginalH430JointQueryEnclosure
open Part5OriginalH430MemberGateRows Part5OriginalH430FullMemberStrips
open P2FiniteMarkedGamma5FixedNativeItinerary P2FiniteMarkedGamma5RealSelectedPrefix
open P2FiniteMarkedGamma5SelectedSeedTerminal P2FiniteMarkedGamma5SelectedQueryRows
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement

abbrev PairedRow := ReadLabel × StepShape × (Point × Point)

def leftRow (r : PairedRow) : Row := (r.1,r.2.1,r.2.2.1)
def rightRow (r : PairedRow) : Row := (r.1,r.2.1,r.2.2.2)

def atomChange (p q : TypedNode) : Prop :=
  ∃ b : FloorAtom, ¬ (p.physical.argument ∈ tableAtomSet (!p.upper) b ↔
    q.physical.argument ∈ tableAtomSet (!q.upper) b)

private theorem atoms_agree {p q : TypedNode} (h : ¬ atomChange p q) :
    (fun b : FloorAtom => p.physical.argument ∈ tableAtomSet (!p.upper) b) =
      fun b => q.physical.argument ∈ tableAtomSet (!q.upper) b := by
  classical
  funext b
  apply propext
  by_contra hn
  exact h ⟨b,hn⟩

private theorem resolve_agrees {p q : TypedNode} (hu : p.upper=q.upper)
    (h : ¬ atomChange p q) (g : ℕ) (m : ReadMode) :
    nodeResolve g p m = nodeResolve g q m := by
  cases m with
  | cell i => rfl
  | scalar =>
    let f (up : Bool) (pred : FloorAtom → Prop) : Option (Fin 200) := by
      classical
      exact if he : ∃ b, pred b then some (atomOwner (iterate g up) (Classical.choose he)) else none
    change f p.upper _ = f q.upper _
    exact congrArg₂ f hu (atoms_agree h)

private theorem positive_agrees {p q : TypedNode} (hu : p.upper=q.upper)
    (h : ¬ atomChange p q) (m : ReadMode) : positive p m ↔ positive q m := by
  let r : Request := ⟨p,[],m⟩
  let u : Request := ⟨q,[],m⟩
  change 0 < requestValue (iterate 0) r ↔ 0 < requestValue (iterate 0) u
  rw [← terminalTest_iff r,← terminalTest_iff u]
  have he := atoms_agree h
  cases m <;> simp [r,u,terminalTest,hu,he]

/-- Both points must reach the same preceding read and pass its full
original branch before a later wall can be charged. -/
def firstChange : ℕ → TypedNode → TypedNode → ReadMode → List PairedRow → Prop
  | _,p,q,_,[] => atomChange p q
  | 0,_,_,_,_::_ => False
  | g+1,p,q,m,(a,s,x,y)::rows =>
    atomChange p q ∨
    (nodeResolve (g+1) p m = some a.1 ∧
     nodeResolve (g+1) q m = some a.1 ∧
     (roundDecision (iterate g) p.upper a.1).choice = a.2 ∧
     ((¬ (branch p x a.2 s ↔ branch q y a.2 s)) ∨
       (branch p x a.2 s ∧ branch q y a.2 s ∧
        firstChange g (advance p s x) (advance q s y) (modeAfter a.1 s) rows)))

theorem walk_change {g : ℕ} {p q : TypedNode} (hu : p.upper=q.upper)
    (m : ReadMode) (rs : List PairedRow)
    (h : ¬ (walk g p m (rs.map leftRow) ↔ walk g q m (rs.map rightRow))) :
    firstChange g p q m rs := by
  classical
  induction rs generalizing g p q m with
  | nil =>
    by_contra hn
    exact h (positive_agrees hu hn m)
  | cons head tail ih =>
    obtain ⟨a,s,x,y⟩ := head
    cases g with
    | zero => exact False.elim (h Iff.rfl)
    | succ g =>
      change atomChange p q ∨ _
      by_cases ha : atomChange p q
      · exact Or.inl ha
      have hr := resolve_agrees hu ha (g+1) m
      simp only [List.map_cons,leftRow,rightRow,walk] at h
      by_cases hp : nodeResolve (g+1) p m = some a.1
      · have hq : nodeResolve (g+1) q m = some a.1 := hr.symm.trans hp
        by_cases hc : (roundDecision (iterate g) p.upper a.1).choice = a.2
        · have hd : (roundDecision (iterate g) q.upper a.1).choice = a.2 := by simpa only [← hu] using hc
          refine Or.inr ⟨hp,hq,hc,?_⟩
          by_cases hs : branch p x a.2 s ↔ branch q y a.2 s
          · by_cases hx : branch p x a.2 s
            · have hy := hs.mp hx
              simp only [hp,hq,hc,hd,hx,hy,true_and] at h
              have he : (advance p s x).upper = (advance q s y).upper := by simp [advance,hu]
              exact Or.inr ⟨hx,hy,ih he _ h⟩
            · exact False.elim (h (by simp [hp,hq,hc,hd,hx,mt hs.mpr hx]))
          · exact Or.inl hs
        · exact False.elim (h (by simp [hp,hq,hc,← hu]))
      · exact False.elim (h (by simp [← hr,hp]))

theorem selected_change {d : ℕ} (n : ℕ) (k : Root) (tau : ℝ)
    (sh : Fin d → StepShape) (a : Fin d → ReadLabel)
    (x y : NativeSlot sh → ℝ)
    (h : ¬ (x ∈ selected n k tau sh a ↔ y ∈ selected n k tau sh a)) :
    d=430 ∧ firstChange 430 (frozenRoot n k tau (x (.inl ())))
      (frozenRoot n k tau (y (.inl ()))) .scalar
      (List.ofFn fun i => (a i,sh i,nativeCoordinates sh x i,nativeCoordinates sh y i)) := by
  classical
  by_cases hd : d=430
  · refine ⟨hd,walk_change rfl _ _ ?_⟩
    simpa [selected,hd,List.map_ofFn,leftRow,rightRow,Function.comp_def] using h
  · exact False.elim (h (by simp [selected,hd]))

/-- A changed read in a common affine chart inherits the original finite
four-row atom catalogue with the gain fixed by its shape. -/
theorem changed_read_strip {p q : TypedNode} (hu : p.upper=q.upper)
    {gain D E : ℝ} (hp : represents p.physical gain D)
    (hq : represents q.physical gain E) (h : atomChange p q) :
    ∃ b : FloorAtom, ∃ r ∈ (atomRows (!p.upper) b).map (cleared gain),
      r.value (residual p.physical) D ≠ r.value (residual q.physical) E ∧
      |r.value (residual p.physical) D| ≤
        |r.level|*|residual p.physical-residual q.physical|+|r.query|*|D-E| := by
  obtain ⟨b,hb⟩ := h
  exact ⟨b,changed_atom_cleared hp hq _ b (by simpa only [← hu] using hb)⟩

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedFirstChange
