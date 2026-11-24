private theorem ownership_eval_notation_add (a b : Expr) (t : Point) :
    evaluate (a + b) t = evaluate a t + evaluate b t := by rfl

private theorem ownership_eval_notation_sub (a b : Expr) (t : Point) :
    evaluate (a - b) t = evaluate a t - evaluate b t := by rfl

private theorem ownership_eval_notation_smul (q : ℚ) (a : Expr) (t : Point) :
    evaluate (q • a) t = (q : ℝ) * evaluate a t := by rfl

