import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows

/-! SOURCE ONLY / UNCOMPILED. Check every original constructor equation
against the explicit-recursion owner candidate, using only reflexivity. -/

namespace ImbalancedChen.P2OwnerRecursionEquations

open OriginalDescendingFifteenLiteralAffineRows (Expr coefficients evaluate)

theorem coefficients_constant (c : ℚ) :
    coefficients (.constant c) = (fun k : Fin 9 => if k = 0 then c else 0) := rfl

theorem coefficients_coord (j : Fin 8) :
    coefficients (.coord j) = (fun k : Fin 9 => if k = j.succ then 1 else 0) := rfl

theorem coefficients_add (a b : Expr) :
    coefficients (.add a b) = (fun k => coefficients a k + coefficients b k) := rfl

theorem coefficients_sub (a b : Expr) :
    coefficients (.sub a b) = (fun k => coefficients a k - coefficients b k) := rfl

theorem coefficients_scale (c : ℚ) (a : Expr) :
    coefficients (.scale c a) = (fun k => c * coefficients a k) := rfl

theorem evaluate_constant (c : ℚ) (t : Fin 8 → ℝ) :
    evaluate (.constant c) t = (c : ℝ) := rfl

theorem evaluate_coord (j : Fin 8) (t : Fin 8 → ℝ) :
    evaluate (.coord j) t = t j := rfl

theorem evaluate_add (a b : Expr) (t : Fin 8 → ℝ) :
    evaluate (.add a b) t = evaluate a t + evaluate b t := rfl

theorem evaluate_sub (a b : Expr) (t : Fin 8 → ℝ) :
    evaluate (.sub a b) t = evaluate a t - evaluate b t := rfl

theorem evaluate_scale (c : ℚ) (a : Expr) (t : Fin 8 → ℝ) :
    evaluate (.scale c a) t = (c : ℝ) * evaluate a t := rfl

end ImbalancedChen.P2OwnerRecursionEquations
