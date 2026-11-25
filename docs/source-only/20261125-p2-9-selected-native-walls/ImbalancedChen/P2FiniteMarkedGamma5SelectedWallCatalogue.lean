import ImbalancedChen.P2FiniteMarkedGamma5SelectedBranchRows

namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedWallCatalogue
noncomputable section
open P2Selected430CausalOccurrenceExporter
open P5OriginalActionMassBound P5OriginalFeedbackDomains P5OriginalFeedbackTableKernels
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open Part5OriginalUpsilon5CausalDictionary Part5OriginalH430ClosedOwner
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430NativeQueryPaths Part5OriginalH430EmittedNativeQueries
open Part5OriginalH430MemberGateRows Part5OriginalH430FullMemberStrips
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430ActiveKnotPullbacks Part5OriginalH430BankSlotTargets
open P2FiniteMarkedGamma5FixedNativeItinerary P2FiniteMarkedGamma5RealSelectedPrefix
open P2FiniteMarkedGamma5SelectedQueryRows P2FiniteMarkedGamma5SelectedFirstChange
open P2FiniteMarkedGamma5SelectedBranchRows P2FiniteMarkedGamma5StrictPhysicalChildren

structure Chart (V : Type*) where
  total : V
  level : V
  ceiling : V
  den : V
  gain : ℝ

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def Chart.after (u : Chart V) (s : StepShape) (x y : V) : Chart V :=
  let fixed (c : ℝ) : Chart V := { u with den := u.level, gain := c }
  let one (D : V) (g : ℝ) : Chart V :=
    ⟨u.total,u.level-x,x,D,g⟩
  match s with
  | .retain => u
  | .transport i => fixed (gridArgument i)
  | .w1Fixed _ j => fixed (W1Anchor j)
  | .w2Fixed j b => fixed (if b then (originalW2At j).s0 else (originalW2At j).phi1)
  | .buchstabUpper | .buchstabLower => one x 1
  | .w1Singleton _ j => one u.level (W1Anchor j)
  | .w2Singleton j _ => one u.level (originalW2At j).s0
  | .w2Pair j piece =>
      ⟨u.total,u.level-y-x,x,if piece.val<2 then u.level else x,
        if piece.val<2 then (originalW2At j).s0 else 1⟩

def Chart.fits (u : Chart V) (f : V →ₗ[ℝ] ℝ) (p : PhysicalNode) : Prop :=
  p.total=f u.total ∧ residual p=f u.level ∧ p.ceiling=f u.ceiling ∧
    0 < residual p ∧ represents p u.gain (f u.den)

private theorem branch_implies_gate (p : TypedNode) (z : Point) (c : Choice) (s : StepShape)
    (h : branch p z c s) : literalGate p.physical z s := by
  cases c with
  | retained => cases s <;> simp_all [branch,literalGate]
  | buchstab => cases s <;> cases hu : p.upper <;> simp_all [branch,literalGate]
  | bank k =>
    cases ha : actionOfSlot k with
    | inl ab => obtain ⟨i,j⟩ := ab; cases s <;> simp_all [branch,ha,bankGate,literalGate]
    | inr j => cases s <;> simp_all [branch,ha,bankGate,literalGate]

private theorem fits_after (u : Chart V) (f : V →ₗ[ℝ] ℝ) (p : TypedNode)
    (s : StepShape) (x y : V) (c : Choice) (hf : u.fits f p.physical)
    (h : branch p ![f x,f y] c s) :
    (u.after s x y).fits f (advance p s ![f x,f y]).physical := by
  have hg := branch_implies_gate _ _ _ _ h
  obtain ⟨ht,hl,hc,hlp,hr⟩ := hf
  let z : Point := ![f x,f y]
  have act (q : FeedbackQuery) (hx : 0 < f x) :=
    active_chart p.physical z q hlp hx
  cases s with
  | retain => exact ⟨ht,hl,hc,hlp,hr⟩
  | transport i =>
    exact ⟨ht,hl,hc,hlp,by simpa only [← hl] using compare_chart p.physical (gridArgument i) hlp⟩
  | w1Fixed i j =>
    exact ⟨ht,hl,hc,hlp,by simpa only [← hl] using compare_chart p.physical (W1Anchor j) hlp⟩
  | w2Fixed j b =>
    exact ⟨ht,hl,hc,hlp,by simpa only [← hl] using
      compare_chart p.physical (if b then (originalW2At j).s0 else (originalW2At j).phi1) hlp⟩
  | buchstabUpper | buchstabLower | w1Singleton | w2Singleton =>
    have hx : 0 < f x := hg.2.1
    have hcap : f x < residual p.physical := hg.2.2.2.2
    refine ⟨ht,?_,rfl,?_,?_⟩
    · simp [Chart.after,advance,perform,hl]
    · simpa [advance,perform,sub_pos] using hcap
    · first
      | exact act (.buchstabUpper 0) hx
      | exact act (.buchstabLower 0) hx
      | simpa [activeGain,knotDenominator,← hl] using act (.w1 _ _) hx
      | simpa [activeGain,knotDenominator,← hl] using act (.w2Singleton _ _) hx
  | w2Pair j b =>
    have hx : 0 < f x := hg.2.1
    have hcap : f x+f y < residual p.physical := hg.2.2.2.2.2.2
    refine ⟨ht,?_,rfl,?_,?_⟩
    · simp [Chart.after,advance,perform,hl]
    · change 0 < residual (perform p.physical (.w2Pair j b) z)
      rw [perform,residual_appendPair]
      change 0 < residual p.physical-f y-f x
      linarith
    · have he := act (.w2Pair j b) hx
      by_cases hh : b.val<2 <;>
        simpa [Chart.after,activeGain,knotDenominator,hh,← hl,z,FeedbackQuery.shape] using he

/-- The entire finite table-atom row collection is fixed before any evaluation. -/
def ownerForms (u : Chart V) : List V :=
  [false,true].flatMap fun b => (Finset.univ : Finset FloorAtom).toList.flatMap fun i =>
    (atomRows b i).map fun r => (r.query*u.gain) • u.level+r.constant • u.den

private theorem owner_mem (u : Chart V) (b : Bool) (i : FloorAtom) (r : GateRow)
    (hr : r ∈ atomRows b i) :
    (r.query*u.gain) • u.level+r.constant • u.den ∈ ownerForms u := by
  classical
  apply List.mem_flatMap.mpr
  refine ⟨b,by cases b <;> simp,?_⟩
  apply List.mem_flatMap.mpr
  exact ⟨i,by simp,List.mem_map.mpr ⟨r,hr,rfl⟩⟩

abbrev SymbolicRow (V : Type*) := ReadLabel × StepShape × (V × V)

def catalogue (one : V) : Chart V → List (SymbolicRow V) → List V
  | u,[] => ownerForms u
  | u,(_,s,x,y)::rs => ownerForms u ++
      (literalRows u.gain one u.total u.level u.ceiling u.den x y s).map Prod.snd ++
      catalogue one (u.after s x y) rs

def atRow (f : V →ₗ[ℝ] ℝ) (r : SymbolicRow V) : Row :=
  (r.1,r.2.1,![f r.2.2.1,f r.2.2.2])

/-- Both strict and weak signs are retained. Ties may only be discarded
when evaluation is actually identical at the two points. -/
def agree (f h : V →ₗ[ℝ] ℝ) (v : V) : Prop :=
  (0 < f v ↔ 0 < h v) ∧ (0 ≤ f v ↔ 0 ≤ h v)

private theorem atom_agrees (u : Chart V) (f h : V →ₗ[ℝ] ℝ) (p q : TypedNode)
    (hu : p.upper=q.upper) (hp : u.fits f p.physical) (hq : u.fits h q.physical)
    (hs : ∀ v ∈ ownerForms u, agree f h v) : ¬ atomChange p q := by
  rintro ⟨i,hi⟩
  apply hi
  rw [← hu,atom_row_iff hp.2.2.2.2,atom_row_iff hq.2.2.2.2]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro hr
  have ha := hs _ (owner_mem u (!p.upper) i r hr)
  simp only [agree,map_add,map_smul,smul_eq_mul,← hp.2.1,← hq.2.1] at ha
  cases r.strict <;> simp [ha.1,ha.2]

private theorem gate_agrees (u : Chart V) (one x y : V) (s : StepShape)
    (f h : V →ₗ[ℝ] ℝ) (p q : TypedNode) (c : Choice) (hu : p.upper=q.upper)
    (hp : u.fits f p.physical) (hq : u.fits h q.physical)
    (hf : f one=1) (hh : h one=1)
    (hs : ∀ row ∈ literalRows u.gain one u.total u.level u.ceiling u.den x y s,
      agree f h row.2) :
    branch p ![f x,f y] c s ↔ branch q ![h x,h y] c s := by
  classical
  by_contra H
  apply changed_branch_gate p q hu _ _ c s H
  rw [gate_iff_rows _ _ s hp.2.2.2.2,gate_iff_rows _ _ s hq.2.2.2.2]
  have left := map_literalRows f u.gain one u.total u.level u.ceiling u.den x y s
  have right := map_literalRows h u.gain one u.total u.level u.ceiling u.den x y s
  rw [hf,← hp.1,← hp.2.1,← hp.2.2.1] at left
  rw [hh,← hq.1,← hq.2.1,← hq.2.2.1] at right
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← left,← right]
  simp only [allPass,List.forall_mem_map]
  apply forall_congr'
  intro row
  apply forall_congr'
  intro hr
  obtain ⟨hpos,hnonneg⟩ := hs row hr
  cases row.1 <;> simp [passes,hpos,hnonneg]

/-- A sign agreement on this particular finite list suffices for the
entire original selected walk; physical state hypotheses are propagated
only through accepted prefixes. -/
theorem walk_agrees (one : V) (u : Chart V) (rs : List (SymbolicRow V))
    (f h : V →ₗ[ℝ] ℝ) (p q : TypedNode) (m : ReadMode) (g : ℕ)
    (hp : u.fits f p.physical) (hq : u.fits h q.physical) (hu : p.upper=q.upper)
    (hf : f one=1) (hh : h one=1)
    (hs : ∀ v ∈ catalogue one u rs, agree f h v) :
    walk g p m (rs.map (atRow f)) ↔ walk g q m (rs.map (atRow h)) := by
  classical
  by_contra H
  have hc := walk_change hu m
    (rs.map (fun r => (r.1,r.2.1,![f r.2.2.1,f r.2.2.2],![h r.2.2.1,h r.2.2.2]))) (by
      simpa [List.map_map,Function.comp_def,leftRow,rightRow,atRow] using H)
  clear H
  induction rs generalizing u p q g m with
  | nil => exact atom_agrees u f h p q hu hp hq hs hc
  | cons r rs ih =>
    obtain ⟨a,s,x,y⟩ := r
    cases g with
    | zero => exact hc
    | succ g =>
      have ha : ∀ v ∈ ownerForms u, agree f h v :=
        fun v hv => hs v (by simp [catalogue,hv])
      rcases hc with head | ⟨_,_,_,head | ⟨hx,hy,tail⟩⟩
      · exact atom_agrees u f h p q hu hp hq ha head
      · exact head (gate_agrees u one x y s f h p q a.2 hu hp hq hf hh
          (fun row hr => hs _ (by simp [catalogue,List.mem_map.mpr ⟨row,hr,rfl⟩])))
      · exact ih (u.after s x y) _ _ _ _
          (fits_after u f p s x y a.2 hp hx) (fits_after u h q s x y a.2 hq hy)
          (by simp [advance,hu]) (fun v hv => hs v (by simp [catalogue,hv])) tail

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedWallCatalogue
