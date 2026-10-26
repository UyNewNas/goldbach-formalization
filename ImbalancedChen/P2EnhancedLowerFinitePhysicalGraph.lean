import ImbalancedChen.P2EnhancedLowerPhysicalTransition
import ImbalancedChen.P2PhysicalIncomingPrefixCells

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A deterministic finite family graph for the original feedback components.
Its vertices are finite action words and finite PHYSICAL cell labels.
Coordinates belong to the fixed physical mesh, not a residual mesh chosen
after seeing a descendant.  Realization computes every child, its query
kind, actual residual and alpha.  Membership evaluates the literal local
filters; gate, positive-cutoff and bounded-rank conclusions are proved.

This constructs the graph rather than taking an arbitrary graph or an
admission proof as input.  It is the feedback-family constructor.  The
eleven root marked families, quantitative compact approximation, scalar
action constants and beta/rough compiler binding remain separate inputs
to the complete theorem.  In particular this file does not claim the
actual eleven-root below-half support or the final enhanced density.
-/

namespace ImbalancedChen.P2EnhancedLowerFinitePhysicalGraph

noncomputable section
open Set Classical
open P2EnhancedLowerPhysicalNode P2EnhancedLowerPhysicalTransition
open P5OriginalActionMassBound (Point)

abbrev PhysicalCell (mesh : ℕ) := P2PhysicalIncomingPrefixCells.CellCode mesh
abbrev StepCode (mesh : ℕ) := StepShape × (PhysicalCell mesh × PhysicalCell mesh)
abbrev Program (mesh depth : ℕ) := Fin depth → StepCode mesh
abbrev Coordinates (depth : ℕ) := Fin depth → Point

structure TypedNode where
  upper : Bool
  physical : PhysicalNode

def incomingAllowed (upper : Bool) : StepShape → Prop
  | .retain => True
  | .buchstabLower => upper=false
  | _ => upper=true

def childUpper (upper : Bool) : StepShape → Bool
  | .retain => upper
  | .buchstabUpper => false
  | .w1Singleton _ _ => false
  | .w2Singleton _ _ => false
  | _ => true

def advance (n : TypedNode) (shape : StepShape) (z : Point) : TypedNode :=
  ⟨childUpper n.upper shape, perform n.physical shape z⟩

def physicalLabel (a b : ℝ) (mesh : ℕ) (z : Point) : PhysicalCell mesh × PhysicalCell mesh :=
  (P2PhysicalIncomingPrefixCells.exponentCode a b mesh (z 0),
   P2PhysicalIncomingPrefixCells.exponentCode a b mesh (z 1))

def cellMember (a b : ℝ) (mesh : ℕ) (cell : PhysicalCell mesh × PhysicalCell mesh)
    (z : Point) : Prop :=
  z 0 ∈ Icc a b ∧ z 1 ∈ Icc a b ∧
  z 0 ∈ P2PhysicalIncomingPrefixCells.exponentCell a b mesh cell.1 ∧
  z 1 ∈ P2PhysicalIncomingPrefixCells.exponentCell a b mesh cell.2

theorem physicalLabel_member {a b : ℝ} {mesh : ℕ} {z : Point}
    (hz0 : z 0 ∈ Icc a b) (hz1 : z 1 ∈ Icc a b) :
    cellMember a b mesh (physicalLabel a b mesh z) z :=
  ⟨hz0,hz1,P2PhysicalIncomingPrefixCells.exponentCode_membership hz0,
    P2PhysicalIncomingPrefixCells.exponentCode_membership hz1⟩

theorem cellMember_unique {a b : ℝ} (hab : a<b) {mesh : ℕ}
    {c d : PhysicalCell mesh × PhysicalCell mesh} {z : Point}
    (hc : cellMember a b mesh c z) (hd : cellMember a b mesh d z) : c=d := by
  apply Prod.ext
  · exact P2PhysicalIncomingPrefixCells.exponentCell_unique hab hc.2.2.1 hd.2.2.1
  · exact P2PhysicalIncomingPrefixCells.exponentCell_unique hab hc.2.2.2 hd.2.2.2

def tail {α : Type*} {depth : ℕ} (f : Fin (depth+1) → α) : Fin depth → α :=
  fun i => f i.succ

def realize {mesh : ℕ} : (depth : ℕ) → TypedNode → Program mesh depth → Coordinates depth → TypedNode
  | 0,n,_,_ => n
  | depth+1,n,code,z => realize depth (advance n (code 0).1 (z 0)) (tail code) (tail z)

def Member (a b : ℝ) {mesh : ℕ} :
    (depth : ℕ) → TypedNode → Program mesh depth → Coordinates depth → Prop
  | 0,_,_,_ => True
  | depth+1,n,code,z =>
      cellMember a b mesh (code 0).2 (z 0) ∧
      incomingAllowed n.upper (code 0).1 ∧
      LocalDomain n.physical (code 0).1 (z 0) ∧
      Member a b depth (advance n (code 0).1 (z 0)) (tail code) (tail z)

/-- ALL finite component/cell itineraries, including empty cells.  Empty
cells have no members and need no arithmetic normalization. -/
def allPrograms (mesh depth : ℕ) : Finset (Program mesh depth) := Finset.univ

/-- A graph vertex retains the finite remaining-generation label and
the entire action/cell itinerary.  Two equal arithmetic products reached
through different itineraries are distinct labelled vertices. -/
abbrev GraphVertex (mesh horizon : ℕ) :=
  Sigma (fun level : Fin (horizon+1) => Program mesh level.val)

def allVertices (mesh horizon : ℕ) : Finset (GraphVertex mesh horizon) := Finset.univ

def parentVertex {mesh horizon depth : ℕ} (h : depth<horizon)
    (code : Program mesh (depth+1)) : GraphVertex mesh horizon :=
  ⟨⟨depth+1,by omega⟩,code⟩

def childVertex {mesh horizon depth : ℕ} (h : depth<horizon)
    (code : Program mesh (depth+1)) : GraphVertex mesh horizon :=
  ⟨⟨depth,by omega⟩,tail code⟩

theorem constructed_edge_previous_generation {mesh horizon depth : ℕ}
    (h : depth<horizon) (code : Program mesh (depth+1)) :
    (parentVertex h code).1.val=(childVertex h code).1.val+1 := rfl

@[simp] theorem mem_allPrograms (mesh depth : ℕ) (p : Program mesh depth) :
    p ∈ allPrograms mesh depth := Finset.mem_univ _

theorem allPrograms_card (mesh depth : ℕ) :
    (allPrograms mesh depth).card =
      (Fintype.card StepShape * (Fintype.card (PhysicalCell mesh))^2)^depth := by
  simp [allPrograms, Program, StepCode, Fintype.card_fun, pow_two, mul_assoc]

/-- Canonical deterministic code of a physical itinerary.  Branch labels
remain part of this code even if two paths produce the same prime word. -/
def canonicalProgram (a b : ℝ) (mesh : ℕ) {depth : ℕ}
    (shape : Fin depth → StepShape) (z : Coordinates depth) : Program mesh depth :=
  fun i => (shape i,physicalLabel a b mesh (z i))

def LocalPath (a b : ℝ) :
    (depth : ℕ) → TypedNode → (Fin depth → StepShape) → Coordinates depth → Prop
  | 0,_,_,_ => True
  | depth+1,n,shape,z =>
      (z 0) 0 ∈ Icc a b ∧ (z 0) 1 ∈ Icc a b ∧
      incomingAllowed n.upper (shape 0) ∧ LocalDomain n.physical (shape 0) (z 0) ∧
      LocalPath a b depth (advance n (shape 0) (z 0)) (tail shape) (tail z)

/-- No externally serialized graph is needed to assign a locally retained
physical path to the finite graph.  Every earlier-prefix state is computed
by the same constructor in both sides of this equivalence. -/
theorem canonicalProgram_member {a b : ℝ} {mesh depth : ℕ}
    (n : TypedNode) (shape : Fin depth → StepShape) (z : Coordinates depth)
    (hz : LocalPath a b depth n shape z) :
    Member a b depth n (canonicalProgram a b mesh shape z) z := by
  induction depth generalizing n with
  | zero => trivial
  | succ depth ih =>
      exact ⟨physicalLabel_member hz.1 hz.2.1,hz.2.2.1,hz.2.2.2.1,
        ih _ _ _ hz.2.2.2.2⟩

theorem realize_total {mesh depth : ℕ} (n : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth n code z).physical.total=n.physical.total := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
      exact (ih _ (tail code) (tail z)).trans (perform_total _ _ _)

theorem realize_occurrence {mesh depth : ℕ} (n : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth n code z).physical.occurrence=n.physical.occurrence := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
      exact (ih _ (tail code) (tail z)).trans (perform_occurrence _ _ _)

theorem realize_rank {mesh depth : ℕ} (n : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth) :
    (realize depth n code z).physical.slots.length≤n.physical.slots.length+2*depth := by
  induction depth generalizing n with
  | zero => simp [realize]
  | succ depth ih =>
      have htail := ih (advance n (code 0).1 (z 0)) (tail code) (tail z)
      have hstep := perform_rank n.physical (code 0).1 (z 0)
      change (realize depth (advance n (code 0).1 (z 0)) (tail code) (tail z)).physical.slots.length
        ≤n.physical.slots.length+2*(depth+1)
      dsimp only [advance] at htail
      omega

theorem realize_selected {mesh depth : ℕ} (n : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth) :
    selectedWord (realize depth n code z).physical.slots=selectedWord n.physical.slots := by
  induction depth generalizing n with
  | zero => rfl
  | succ depth ih =>
      exact (ih _ (tail code) (tail z)).trans (perform_selected _ _ _)

theorem perform_prefix (n : PhysicalNode) (shape : StepShape) (z : Point) :
    ∃ suffix,(perform n shape z).slots=n.slots++suffix := by
  cases shape with
  | retain => exact ⟨[],(List.append_nil _).symm⟩
  | transport cell => exact ⟨[],(List.append_nil _).symm⟩
  | buchstabUpper => exact ⟨[unselected (z 0)],rfl⟩
  | buchstabLower => exact ⟨[unselected (z 0)],rfl⟩
  | w1Fixed i j => exact ⟨[],(List.append_nil _).symm⟩
  | w1Singleton i j => exact ⟨[unselected (z 0)],rfl⟩
  | w2Fixed bank anchor => exact ⟨[],(List.append_nil _).symm⟩
  | w2Singleton bank piece => exact ⟨[unselected (z 0)],rfl⟩
  | w2Pair bank piece => exact ⟨[unselected (z 1),unselected (z 0)],rfl⟩

/-- Every old slot and its selected mark survives literally.  Any frozen
ancestor cap/cell lookup on that prefix therefore sees the same input. -/
theorem realize_prefix {mesh depth : ℕ} (n : TypedNode)
    (code : Program mesh depth) (z : Coordinates depth) :
    ∃ suffix,(realize depth n code z).physical.slots=n.physical.slots++suffix := by
  induction depth generalizing n with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ depth ih =>
      obtain ⟨old,hOld⟩ := perform_prefix n.physical (code 0).1 (z 0)
      obtain ⟨later,hLater⟩ := ih (advance n (code 0).1 (z 0)) (tail code) (tail z)
      refine ⟨old++later,?_⟩
      change (realize depth (advance n (code 0).1 (z 0)) (tail code) (tail z)).physical.slots=_
      simpa only [advance,hOld,List.append_assoc] using hLater

def markedWord (n : PhysicalNode) : List P2PhysicalIncomingPrefixCells.MarkedExponent :=
  n.slots.map (fun slot => (slot.exponent,slot.selected))

/-- Bind the finite graph to the actual rankwise physical cap lookup.
Appending later action coordinates cannot alter ANY earlier decision,
including an identical-inherit cap or a positive-mass structural clamp. -/
theorem realize_ancestor_choice {mesh depth capDepth capMesh : ℕ}
    (P : P2PhysicalIncomingPrefixCells.CapPlan capDepth capMesh)
    (a b : ℝ) (n : TypedNode) (code : Program mesh depth) (z : Coordinates depth)
    (rank : ℕ) (hr : rank≤n.physical.slots.length) :
    P2PhysicalIncomingPrefixCells.incomingChoice P a b rank
        (markedWord (realize depth n code z).physical)=
      P2PhysicalIncomingPrefixCells.incomingChoice P a b rank (markedWord n.physical) := by
  obtain ⟨suffix,hslots⟩ := realize_prefix n code z
  unfold markedWord
  rw [hslots,List.map_append]
  exact P2PhysicalIncomingPrefixCells.incomingChoice_future_invariant P a b rank
    _ _ (by simpa only [List.length_map] using hr)

theorem realize_ancestor_cap {mesh depth capDepth capMesh : ℕ}
    (P : P2PhysicalIncomingPrefixCells.CapPlan capDepth capMesh)
    (a b incoming : ℝ) (n : TypedNode) (code : Program mesh depth) (z : Coordinates depth)
    (rank : ℕ) (hr : rank≤n.physical.slots.length) :
    (P2PhysicalIncomingPrefixCells.incomingChoice P a b rank
        (markedWord (realize depth n code z).physical)).freeze incoming=
      (P2PhysicalIncomingPrefixCells.incomingChoice P a b rank
        (markedWord n.physical)).freeze incoming := by
  rw [realize_ancestor_choice P a b n code z rank hr]

theorem realize_gates_alpha {a b : ℝ} {mesh depth : ℕ} {n : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hf : fullGates n.physical) (hs : selectedGates n.physical)
    (ha : 2≤alpha n.physical) (hz : Member a b depth n code z) :
    fullGates (realize depth n code z).physical ∧
    selectedGates (realize depth n code z).physical ∧
    alpha n.physical≤alpha (realize depth n code z).physical := by
  induction depth generalizing n with
  | zero => exact ⟨hf,hs,le_rfl⟩
  | succ depth ih =>
      have hg := perform_gates hf hs hz.2.2.1
      have hA := perform_alpha hz.2.2.1 ha
      have htail := ih hg.1 hg.2 (ha.trans hA) hz.2.2.2
      exact ⟨htail.1,htail.2.1,hA.trans htail.2.2⟩

/-- Conservative finite-depth lower cutoff, derived from each original
action domain.  It is not a bound supplied by the caller or a stationarity
claim about infinitely many generations. -/
theorem realize_residual_bound {a b : ℝ} {mesh depth : ℕ} {n : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hz : Member a b depth n code z) :
    residual n.physical/(101:ℝ)^depth≤residual (realize depth n code z).physical := by
  induction depth generalizing n with
  | zero => simp [realize]
  | succ depth ih =>
      have hstep := perform_residual_bound hz.2.2.1
      have htail := ih hz.2.2.2
      have hd : 0<(101:ℝ)^depth := pow_pos (by norm_num) _
      have hscaled := (div_le_div_iff_of_pos_right hd).mpr hstep
      have heq : residual n.physical/(101:ℝ)^(depth+1)=
          (residual n.physical/101)/(101:ℝ)^depth := by
        rw [pow_succ]
        field_simp [hd.ne']
        <;> ring
      rw [heq]
      exact hscaled.trans htail

theorem realize_residual_pos {a b : ℝ} {mesh depth : ℕ} {n : TypedNode}
    {code : Program mesh depth} {z : Coordinates depth}
    (hL : 0<residual n.physical) (hz : Member a b depth n code z) :
    0<residual (realize depth n code z).physical :=
  (div_pos hL (pow_pos (by norm_num : (0:ℝ)<101) _)).trans_le (realize_residual_bound hz)

def generation (horizon spent : ℕ) : ℕ := horizon-spent

/-- The finite graph labels feedback children by the PRECEDING generation;
retention/maximum choices do not create same-generation feedback reads. -/
theorem generation_child {horizon spent : ℕ} (h : spent<horizon) :
    generation horizon spent=generation horizon (spent+1)+1 := by
  unfold generation
  omega

end
end ImbalancedChen.P2EnhancedLowerFinitePhysicalGraph
