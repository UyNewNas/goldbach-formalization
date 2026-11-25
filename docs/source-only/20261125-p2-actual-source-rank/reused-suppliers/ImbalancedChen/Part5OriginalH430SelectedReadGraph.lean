import ImbalancedChen.Part5OriginalH430DecisionProvenance

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual selected scalar action as a finite expression. Individual
product floors, the OUTER divisor, all repeated read occurrences, the
original base, and the original strict maximum are retained exactly.
The read graph has scalar-generation depth, not physical Program depth.
-/
namespace ImbalancedChen.Part5OriginalH430SelectedReadGraph

noncomputable section
open scoped Classical BigOperators
open P2Selected430LiteralActionData (Row rows logWeights q)
open P2Selected430CausalOccurrenceExporter
open Part5OriginalH430DecisionProvenance

inductive Expr where
  | lit (z : ℤ)
  | read (up : Bool) (index : ℕ)
  | add (left right : Expr)
  | mul (left right : Expr)
  | quot (body : Expr) (divisor : ℤ)

abbrev ReadEnv := Bool → ℕ → ℤ

def eval (rho : ReadEnv) : Expr → ℤ
  | .lit z => z
  | .read up j => rho up j
  | .add x y => eval rho x + eval rho y
  | .mul x y => eval rho x * eval rho y
  | .quot x d => eval rho x / d

def listExpr {α : Type*} (f : α → Expr) : List α → Expr
  | [] => .lit 0
  | a::as => .add (f a) (listExpr f as)

def rangeExpr (f : ℕ → Expr) : ℕ → Expr
  | 0 => .lit 0
  | n+1 => .add (rangeExpr f n) (f n)

theorem eval_listExpr {α : Type*} (rho : ReadEnv) (f : α → Expr) (as : List α) :
    eval rho (listExpr f as) = (as.map (fun a => eval rho (f a))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [listExpr, eval, List.map_cons, List.sum_cons, ih]

theorem eval_rangeExpr (rho : ReadEnv) (f : ℕ → Expr) (n : ℕ) :
    eval rho (rangeExpr f n) = ∑ r ∈ Finset.range n, eval rho (f r) := by
  induction n with
  | zero => simp [rangeExpr, eval]
  | succ n ih => simp only [rangeExpr, eval, ih, Finset.sum_range_succ]

def suffixExpr (up : Bool) (k : ℕ) : Expr :=
  rangeExpr (fun r => .quot
    (.mul (.read up (k+r)) (.lit (if hj : k+r < 200 then logWeights ⟨k+r,hj⟩ else 0))) q)
    (200-k)

def pointExpr (p : ℕ × ℤ) : Expr := .mul (.read true p.1) (.lit p.2)
def weightExpr (up : Bool) (p : ℕ × ℤ) : Expr :=
  .quot (.mul (.read up p.1) (.lit p.2)) q

def bankExpr (a : Row) : Expr :=
  .add (.lit a.base)
    (.quot (.add (.add (listExpr pointExpr a.points)
      (listExpr (weightExpr false) a.lowerWeights))
      (listExpr (weightExpr true) a.upperWeights)) (a.divisor : ℤ))

def choiceExpr (up : Bool) (i : Fin 200) : Choice → Expr
  | .retained => .read up i.val
  | .buchstab => if up then suffixExpr false (max 50 (i.val-49))
      else suffixExpr true (i.val-49)
  | .bank k => bankExpr (rows k)

def chosenExpr (old : Table) (up : Bool) (i : Fin 200) : Expr :=
  choiceExpr up i (roundDecision old up i).choice

theorem eval_suffixExpr (old : Table) (up : Bool) (k : ℕ) :
    eval (read old) (suffixExpr up k) = suffix old up k := by
  simp only [suffixExpr, eval_rangeExpr, eval, suffix]

theorem eval_bankExpr (old : Table) (a : Row) :
    eval (read old) (bankExpr a) = candidate old a := by
  simp only [bankExpr, eval, eval_listExpr, pointExpr, weightExpr, candidate]

theorem eval_choiceExpr (old : Table) (up : Bool) (i : Fin 200) (c : Choice) :
    eval (read old) (choiceExpr up i c) = choiceValue old up i c := by
  cases c with
  | retained => simp [choiceExpr, choiceValue, eval, read, i.isLt]
  | buchstab => cases up <;>
      simpa only [choiceExpr, choiceValue, buchstabValue, Bool.false_eq_true,
        if_false, if_true] using eval_suffixExpr old _ _
  | bank k => exact eval_bankExpr old (rows k)

theorem eval_chosenExpr (old : Table) (up : Bool) (i : Fin 200) :
    eval (read old) (chosenExpr old up i) = (roundDecision old up i).numerator := by
  rw [chosenExpr, eval_choiceExpr, roundDecision_value]

/-- Retention chooses the preceding scalar entry, not the new one.
The selector remains the existing interpreter; only its dependency
expression is unfolded recursively. This is not a Python replay audit. -/
def replay : ℕ → Table
  | 0 => seed
  | n+1 => fun up i => eval (read (replay n)) (chosenExpr (iterate n) up i)

theorem replay_eq_iterate (n : ℕ) : replay n = iterate n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext up i
      change eval (read (replay n)) (chosenExpr (iterate n) up i) = _
      rw [ih, eval_chosenExpr]

/-- Lists, not sets: duplicate occurrences in a literal row survive. -/
def readOccurrences : Expr → List (Bool × ℕ)
  | .lit _ => []
  | .read up j => [(up,j)]
  | .add x y => readOccurrences x ++ readOccurrences y
  | .mul x y => readOccurrences x ++ readOccurrences y
  | .quot x _ => readOccurrences x

theorem eval_congr_on_reads (e : Expr) (rho eta : ReadEnv)
    (h : ∀ r ∈ readOccurrences e, rho r.1 r.2 = eta r.1 r.2) :
    eval rho e = eval eta e := by
  revert h
  induction e with
  | lit z => intro _; rfl
  | read up j => intro h; exact h (up,j) (by simp [readOccurrences])
  | add x y ihx ihy =>
      intro h
      exact congrArg₂ (fun a b : ℤ => a+b)
        (ihx (fun r hr => h r (List.mem_append.mpr (Or.inl hr))))
        (ihy (fun r hr => h r (List.mem_append.mpr (Or.inr hr))))
  | mul x y ihx ihy =>
      intro h
      exact congrArg₂ (fun a b : ℤ => a*b)
        (ihx (fun r hr => h r (List.mem_append.mpr (Or.inl hr))))
        (ihy (fun r hr => h r (List.mem_append.mpr (Or.inr hr))))
  | quot x d ih => intro h; exact congrArg (fun a : ℤ => a/d) (ih h)

def predecessorReads (g : ℕ) (up : Bool) (i : Fin 200) : List (ℕ × Bool × ℕ) :=
  (readOccurrences (chosenExpr (iterate g) up i)).map (fun r => (g,r.1,r.2))

/-- Every dependency of the actual next-generation winner is strictly
older. No equation generation = 430 - physicalDepth is introduced. -/
theorem predecessorReads_generation {g : ℕ} {up : Bool} {i : Fin 200}
    {r : ℕ × Bool × ℕ} (hr : r ∈ predecessorReads g up i) :
    r.1 = g ∧ r.1 < g+1 := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  exact ⟨rfl, Nat.lt_succ_self g⟩

theorem literal430_selected_value (g : Fin 430) (up : Bool) (i : Fin 200) :
    eval (read (iterate g.val)) (chosenExpr (iterate g.val) up i) =
      iterate (g.val+1) up i := eval_chosenExpr _ _ _

end
end ImbalancedChen.Part5OriginalH430SelectedReadGraph
