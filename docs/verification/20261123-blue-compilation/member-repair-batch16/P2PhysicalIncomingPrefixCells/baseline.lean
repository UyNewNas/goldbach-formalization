import ImbalancedChen.CurrentP5MarkedTupleCommonRefinement
import ImbalancedChen.LogPrimeBoxMesh

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual physical exponent cells and earlier-prefix cap lookups for the
typed-density bridge section4. The finite geometric plan is fixed before
any arithmetic target; it reads physical chronological prefixes only.
Later coordinates cannot change earlier cell codes or frozen decisions.
Inherited caps and the structural argument=2 label are literal data.
-/

namespace ImbalancedChen.P2PhysicalIncomingPrefixCells
noncomputable section
open Set Classical

abbrev CellCode (m : ℕ) := Option (Fin (m+1))
abbrev MarkedExponent := ℝ×Bool

def exponentCell (a b : ℝ) (m : ℕ) : CellCode m → Set ℝ
  | none => {b}
  | some j => Ico (logPrimeMeshPoint a b m j.val)
      (logPrimeMeshPoint a b m (j.val+1))

def exponentCode (a b : ℝ) (m : ℕ) (x : ℝ) : CellCode m :=
  if hx : x ∈ Ico a b then some (Classical.choose (exists_logPrimeMeshInterval a b m hx)) else none

theorem exponentCell_unique {a b : ℝ} (hab : a<b) {m : ℕ}
    {i j : CellCode m} {x : ℝ} (hi : x ∈ exponentCell a b m i)
    (hj : x ∈ exponentCell a b m j) : i=j := by
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some k =>
          have he : x=b := hi
          have hb := (logPrimeMeshLoHi_bounds (d:=1) hab m (fun _ =>k) 0).2.2
          exact ((hj.2.trans_le hb).ne he).elim
  | some k =>
      cases j with
      | none =>
          have he : x=b := hj
          have hb := (logPrimeMeshLoHi_bounds (d:=1) hab m (fun _ =>k) 0).2.2
          exact ((hi.2.trans_le hb).ne he).elim
      | some l =>
          have hk : (fun _ : Fin 1 =>x) ∈ logPrimeMeshCell a b m (fun _ =>k) := by
            exact mem_logPrimeMeshCell.mpr (fun _ =>hi)
          have hl : (fun _ : Fin 1 =>x) ∈ logPrimeMeshCell a b m (fun _ =>l) := by
            exact mem_logPrimeMeshCell.mpr (fun _ =>hj)
          exact congrArg some (congrFun (logPrimeMeshCell_unique hab.le hk hl) 0)

theorem exponentCode_membership {a b : ℝ} {m : ℕ} {x : ℝ}
    (hx : x ∈ Icc a b) : x ∈ exponentCell a b m (exponentCode a b m x) := by
  unfold exponentCode
  split_ifs with hi
  · exact Classical.choose_spec (exists_logPrimeMeshInterval a b m hi)
  · have he : x=b := by
      by_contra hn
      exact hi ⟨hx.1,lt_of_le_of_ne hx.2 hn⟩
    exact he

theorem exponentCode_eq_of_cell {a b : ℝ} (hab : a<b) {m : ℕ}
    {x : ℝ} {c : CellCode m} (hx : x ∈ Icc a b) (hc : x ∈ exponentCell a b m c) :
    exponentCode a b m x=c :=
  exponentCell_unique hab (exponentCode_membership hx) hc

/-- Default padding is the top singleton with an unselected mark;
at every genuine prefix position no default is read. -/
def physicalCode (a b : ℝ) (depth m : ℕ) (prefix : List MarkedExponent) :
    Fin depth → CellCode m×Bool := fun i =>
  let p := prefix.getD i.val (b,false)
  (exponentCode a b m p.1,p.2)

def incomingCode (a b : ℝ) (depth m rank : ℕ) (word : List MarkedExponent) :
    Fin depth → CellCode m×Bool := physicalCode a b depth m (word.take rank)

theorem incomingCode_future_invariant (a b : ℝ) (depth m rank : ℕ)
    (parent future : List MarkedExponent) (hr : rank≤parent.length) :
    incomingCode a b depth m rank (parent++future)=incomingCode a b depth m rank parent := by
  unfold incomingCode
  rw [List.take_append_of_le_length hr]

inductive CapChoice where
  | inherit (argument : ℝ)
  | fresh (cap argument : ℝ)

def CapChoice.argument : CapChoice → ℝ
  | .inherit s =>s
  | .fresh _ s =>s
def CapChoice.freeze (incoming : ℝ) : CapChoice → ℝ
  | .inherit _ =>incoming
  | .fresh c _ =>c

inductive QueryLabel where
  | belowTwo
  | exactlyTwo
  | aboveTwo
  deriving DecidableEq

def queryLabel (s : ℝ) : QueryLabel :=
  if s<2 then .belowTwo else if s=2 then .exactlyTwo else .aboveTwo

theorem queryLabel_exactlyTwo_iff (s : ℝ) : queryLabel s=.exactlyTwo ↔ s=2 := by
  unfold queryLabel
  split_ifs <;> simp_all

/-- A genuinely finite family of incoming-prefix geometric choices:
finite rank, finite physical bins, and the actual selected marks.
Unused padded coordinates cannot encode any later physical input. -/
structure CapPlan (depth m : ℕ) where
  choose : Fin (depth+1) → (Fin depth → CellCode m×Bool) → CapChoice

def incomingChoice {depth m : ℕ} (P : CapPlan depth m) (a b : ℝ)
    (rank : ℕ) (word : List MarkedExponent) : CapChoice :=
  P.choose ⟨min rank depth,Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
    (incomingCode a b depth m rank word)

theorem incomingChoice_future_invariant {depth m : ℕ} (P : CapPlan depth m)
    (a b : ℝ) (rank : ℕ) (parent future : List MarkedExponent) (hr : rank≤parent.length) :
    incomingChoice P a b rank (parent++future)=incomingChoice P a b rank parent := by
  unfold incomingChoice
  rw [incomingCode_future_invariant a b depth m rank parent future hr]

/-- In particular, a third cap lookup reads no fourth/fifth coordinate. -/
theorem third_cap_future_invariant {depth m : ℕ} (P : CapPlan depth m)
    (a b incoming : ℝ) (parent : List MarkedExponent) (h3 : parent.length=3)
    (later : List MarkedExponent) :
    (incomingChoice P a b 3 (parent++later)).freeze incoming=
      (incomingChoice P a b 3 parent).freeze incoming := by
  rw [incomingChoice_future_invariant P a b 3 parent later (by omega)]

end
end ImbalancedChen.P2PhysicalIncomingPrefixCells
