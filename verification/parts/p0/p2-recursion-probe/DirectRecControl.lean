import Mathlib

namespace ImbalancedChen.Probes.DirectRecControl

inductive Expr where
  | leaf : Expr
  | node : Expr → Expr → Expr

def count : Expr → Nat :=
  Expr.rec (motive := fun _ => Nat) 1 (fun _ _ a b => a + b + 1)

end ImbalancedChen.Probes.DirectRecControl
