import Mathlib

namespace ImbalancedChen.Probes.FixedFuelProbe

inductive Expr where
  | rational : Nat → Expr
  | logarithm : Nat → Expr
  | add : Expr → Expr → Expr
  | neg : Expr → Expr
  | mul : Expr → Expr → Expr
  | rounded : Nat → Expr → Expr

/-- Nonrecursive work-stack transition. Counts visited constructors only. -/
def step (s : List Expr × Nat) : List Expr × Nat :=
  match s with
  | ([], n) => ([], n)
  | (.rational _ :: rest, n) => (rest, n + 1)
  | (.logarithm _ :: rest, n) => (rest, n + 1)
  | (.add a b :: rest, n) => (a :: b :: rest, n + 1)
  | (.neg a :: rest, n) => (a :: rest, n + 1)
  | (.mul a b :: rest, n) => (a :: b :: rest, n + 1)
  | (.rounded _ a :: rest, n) => (a :: rest, n + 1)

/-- No local recursive definition; uses pinned Nat.rec csimp bridge. -/
def run (fuel : Nat) (e : Expr) : List Expr × Nat :=
  Nat.rec (motive := fun _ => List Expr × Nat) ([e], 0)
    (fun _ s => step s) fuel

def sample : Expr :=
  .rounded 3 (.add (.neg (.rational 2)) (.mul (.logarithm 5) (.rational 7)))

def finishedWith (s : List Expr × Nat) (n : Nat) : Bool :=
  s.1.isEmpty && s.2 == n

def outputChecks : Bool :=
  (finishedWith (run 0 (.rational 0)) 0 == false) &&
  finishedWith (run 1 (.rational 0)) 1 &&
  finishedWith (run 7 sample) 7 &&
  finishedWith (run 100 sample) 7

/-- Closed kernel-reduction checks only; these do not evaluate native output. -/
theorem literal_fuel_zero :
    finishedWith (run 0 (.rational 0)) 0 = false := by rfl

theorem literal_fuel_one :
    finishedWith (run 1 (.rational 0)) 1 = true := by rfl

theorem literal_fuel_seven :
    finishedWith (run 7 sample) 7 = true := by rfl

theorem literal_fuel_hundred :
    finishedWith (run 100 sample) 7 = true := by rfl

end ImbalancedChen.Probes.FixedFuelProbe
