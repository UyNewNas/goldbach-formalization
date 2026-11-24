  fin_cases r
  all_goals
    norm_num only [semanticSlack, semanticExpr, namedSlack,
      Matrix.cons_val_zero, Matrix.cons_val_zero',
      Matrix.cons_val_succ, Matrix.cons_val_succ', Matrix.cons_val_fin_one,
      ownership_eval_notation_add, ownership_eval_notation_sub,
      ownership_eval_notation_smul, evaluate, evaluate_ite,
      evaluate_subsetExpr, oldExpr, newExpr, ascendingExpr, descendingExpr, K, X,
      oldRaw, newCap, total, history3, history5, history7, d, selectedSum,
      branchPlane, prefixSquareExpr, Finset.sum_filter,
      Fin.sum_univ_succ, Fin.sum_univ_zero,
      Fin.succ, Fin.instOfNat, Fin.ofNat, Fin.Internal.ofNat,
      Fin.lt_def, Fin.ext_iff, Fin.val_zero, Fin.val_succ,
      Fin.val_mk, Fin.coe_ofNat_eq_mod, Fin.mk_lt_mk, Fin.mk.inj_iff,
      ne_eq, Nat.reduceMod, and_true, true_and, and_false, false_and,
      not_true_eq_false, not_false_eq_true, ite_true, ite_false,
      Rat.cast_zero, Rat.cast_one, Rat.cast_add, Rat.cast_sub,
      Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
      VariableEnvelope.A, VariableEnvelope.C, eta, VariableEnvelope.cap, mu]
    <;> first
      | rfl
      | (split_ifs <;> ring1!)
      | ring1!
