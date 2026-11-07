import ImbalancedChen.P2PhysicalIncomingPrefixCells
import ImbalancedChen.P2EnhancedLowerPhysicalNode

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual rankwise chronological-prefix constructor, not an arbitrary policy
fibre. Each physical append computes its own prefix-cell choice, freezes
its new cap, and keeps the old cap and all old frames literally. Admission
tests use the INCOMING frozen cap. Full/selected gates are DERIVED using
the genuine physical append theorem. No cap/gate/cell witness is a field
of the raw physical node and no bank or action is redefined here.
-/

namespace ImbalancedChen.P2PhysicalFrozenPrefixHistory
noncomputable section
open Set Classical
open P2PhysicalIncomingPrefixCells
open P2EnhancedLowerPhysicalNode

def markedWord (n : PhysicalNode) : List MarkedExponent :=
  n.slots.map (fun s =>(s.exponent,s.selected))

@[simp] theorem markedWord_appendOne (n : PhysicalNode) (x s : ℝ) :
    markedWord (appendOne n x s)=markedWord n++[(x,false)] := by
  simp only [markedWord,appendOne,List.map_append,List.map_cons,List.map_nil,unselected]

@[simp] theorem markedWord_appendPair (n : PhysicalNode) (x y s : ℝ) :
    markedWord (appendPair n x y s)=markedWord n++[(y,false),(x,false)] := by
  simp only [markedWord,appendPair,List.map_append,List.map_cons,List.map_nil,unselected]

structure FrozenFrame where
  parent : PhysicalNode
  child : PhysicalNode
  incomingCap : ℝ
  frozenCap : ℝ
  choice : CapChoice
  query : QueryLabel

structure History where
  node : PhysicalNode
  cap : ℝ
  frames : List FrozenFrame
  accepted : Bool

def rootGate (depth : ℕ) (a b : ℝ) (n : PhysicalNode) : Prop :=
  n.slots.length≤depth ∧ (∀ p ∈ markedWord n,p.1 ∈ Icc a b) ∧ fullGates n ∧ selectedGates n

def start {depth m : ℕ} (P : CapPlan depth m) (a b seedCap : ℝ) (n : PhysicalNode) : History :=
  { node:=n
    cap:=(incomingChoice P a b n.slots.length (markedWord n)).freeze seedCap
    frames:=[]
    accepted:=decide (rootGate depth a b n) }

/-- The own-cube test at rank3→4 is exactly S3+3t4<lambda3.
The cap used is H.cap, frozen BEFORE x and the new child cap exist. -/
def stepGate (depth : ℕ) (a b : ℝ) (H : History) (x : ℝ) : Prop :=
  H.node.slots.length+1≤depth ∧ x ∈ Icc a b ∧ 0<x ∧ x<H.node.ceiling ∧
  2*x≤residual H.node ∧ (word H.node).sum+3*x<H.cap ∧
  fullGates H.node ∧ selectedGates H.node

def step {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (x s : ℝ) : History :=
  let child:=appendOne H.node x s
  let choice:=incomingChoice P a b child.slots.length (markedWord child)
  let frozen:=choice.freeze H.cap
  { node:=child
    cap:=frozen
    frames:=H.frames++[⟨H.node,child,H.cap,frozen,choice,queryLabel child.argument⟩]
    accepted:=H.accepted && decide (stepGate depth a b H x) }

def advance {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (physical : List (ℝ×ℝ)) : History :=
  physical.foldl (fun H p =>step P a b H p.1 p.2) H

@[simp] theorem step_accepted_iff {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (x s : ℝ) :
    (step P a b H x s).accepted=true ↔ H.accepted=true ∧ stepGate depth a b H x := by
  simp only [step,Bool.and_eq_true,decide_eq_true_eq]

theorem admitted_step_gates {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (x s : ℝ) (h : (step P a b H x s).accepted=true) :
    fullGates (step P a b H x s).node ∧ selectedGates (step P a b H x s).node ∧
      (step P a b H x s).node.ceiling=x ∧ x<H.node.ceiling ∧
      (word H.node).sum+3*x<H.cap := by
  have hg := ((step_accepted_iff P a b H x s).mp h).2
  have hboth := appendOne_gates (s:=s) hg.2.2.2.2.2.2.1 hg.2.2.2.2.2.2.2 hg.2.2.2.2.1
  exact ⟨hboth.1,hboth.2,rfl,hg.2.2.2.1,hg.2.2.2.2.2.1⟩

/-- Geometric membership is a CONCLUSION of the computed admission. -/
theorem admitted_step_cell_membership {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (x s : ℝ) (h : (step P a b H x s).accepted=true) :
    x ∈ exponentCell a b m (exponentCode a b m x) := by
  have hg := ((step_accepted_iff P a b H x s).mp h).2
  exact exponentCode_membership hg.2.1

/-- The structural equality capChild=capParent is retained literally. -/
theorem step_inherit_cap {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (x s q : ℝ)
    (hi : incomingChoice P a b (appendOne H.node x s).slots.length
      (markedWord (appendOne H.node x s))=.inherit q) :
    (step P a b H x s).cap=H.cap := by
  simp only [step,hi,CapChoice.freeze]

theorem step_structural_clamp_label {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (x : ℝ) :
    (step P a b H x 2).frames=H.frames++
      [⟨H.node,appendOne H.node x 2,H.cap,(step P a b H x 2).cap,
        incomingChoice P a b (appendOne H.node x 2).slots.length
          (markedWord (appendOne H.node x 2)),.exactlyTwo⟩] := by
  simp only [step,appendOne,queryLabel,show ¬(2:ℝ)<2 by norm_num,if_false,if_true]

theorem advance_append {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (xs ys : List (ℝ×ℝ)) :
    advance P a b H (xs++ys)=advance P a b (advance P a b H xs) ys := by
  exact List.foldl_append

/-- Every later refinement copies ALL earlier cap/branch/physical
records. No ancestor choice is recalculated using later coordinates. -/
theorem advance_frames_extend {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (physical : List (ℝ×ℝ)) :
    ∃ extra,(advance P a b H physical).frames=H.frames++extra := by
  induction physical generalizing H with
  | nil => exact ⟨[],by simp only [advance,List.foldl_nil,List.append_nil]⟩
  | cons p ps ih =>
      obtain ⟨extra,he⟩ := ih (step P a b H p.1 p.2)
      refine ⟨[⟨H.node,appendOne H.node p.1 p.2,H.cap,
        (step P a b H p.1 p.2).cap,
        incomingChoice P a b (appendOne H.node p.1 p.2).slots.length
          (markedWord (appendOne H.node p.1 p.2)),queryLabel p.2⟩]++extra,?_⟩
      simpa only [advance,List.foldl_cons,step,appendOne,List.append_assoc] using he

theorem advance_ancestor_records {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (physical : List (ℝ×ℝ)) :
    (advance P a b H physical).frames.take H.frames.length=H.frames := by
  obtain ⟨extra,he⟩ := advance_frames_extend P a b H physical
  rw [he,List.take_append_length]

theorem advance_accepted_incoming {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (physical : List (ℝ×ℝ))
    (h : (advance P a b H physical).accepted=true) : H.accepted=true := by
  induction physical generalizing H with
  | nil => exact h
  | cons p ps ih =>
      have hs := ih (step P a b H p.1 p.2) h
      exact ((step_accepted_iff P a b H p.1 p.2).mp hs).1

theorem advance_actual_gates {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (H : History) (physical : List (ℝ×ℝ)) (hroot : fullGates H.node ∧ selectedGates H.node)
    (h : (advance P a b H physical).accepted=true) :
    fullGates (advance P a b H physical).node ∧ selectedGates (advance P a b H physical).node := by
  induction physical generalizing H with
  | nil => exact hroot
  | cons p ps ih =>
      have hs := advance_accepted_incoming P a b (step P a b H p.1 p.2) ps h
      have hg := admitted_step_gates P a b H p.1 p.2 hs
      exact ih (step P a b H p.1 p.2) ⟨hg.1,hg.2.1⟩ h

/-- Actual finite constructor derives its final full and selected gates
from its own tests. No support/cap/gain assumption is passed through. -/
theorem constructed_retained_gates {depth m : ℕ} (P : CapPlan depth m)
    (a b seedCap : ℝ) (n : PhysicalNode) (physical : List (ℝ×ℝ))
    (h : (advance P a b (start P a b seedCap n) physical).accepted=true) :
    fullGates (advance P a b (start P a b seedCap n) physical).node ∧
      selectedGates (advance P a b (start P a b seedCap n) physical).node := by
  have hs := advance_accepted_incoming P a b (start P a b seedCap n) physical h
  have hr : rootGate depth a b n := of_decide_eq_true hs
  exact advance_actual_gates P a b (start P a b seedCap n) physical ⟨hr.2.2.1,hr.2.2.2⟩ h

end
end ImbalancedChen.P2PhysicalFrozenPrefixHistory
