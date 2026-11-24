/-- The original complete-homogeneous prefix convolution, using the
existing pair antidiagonal rather than enumerating rejected tuples. -/
private def exactPrefixH : List Nat → Nat → Nat
  | [], k => if k = 0 then 1 else 0
  | a :: as, k =>
      ((List.Nat.antidiagonal k).map fun p =>
        a ^ p.1 * exactPrefixH as p.2).sum

private theorem exactPrefixH_zero (as : List Nat) : exactPrefixH as 0 = 1 := by
  induction as with
  | nil => simp [exactPrefixH]
  | cons a as ih => simp [exactPrefixH, ih]

/-- The producer's original h[k] += a*h[k-1] prefix identity, without
any division, archive value, distinctness or nonzero-node premise. -/
private theorem exactPrefixH_cons_succ (a : Nat) (as : List Nat) (k : Nat) :
    exactPrefixH (a :: as) (k + 1) =
      exactPrefixH as (k + 1) + a * exactPrefixH (a :: as) k := by
  simp only [exactPrefixH, List.Nat.antidiagonal_succ,
    List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    Prod.map_apply, id_eq, Nat.succ_eq_add_one, pow_zero, one_mul]
  congr 1
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [pow_succ]
  ring

private theorem antidiagonalTuple_sum_eq_prefixH {n : Nat}
    (nodes : Fin n → Nat) (k : Nat) :
    ((List.Nat.antidiagonalTuple n k).map
      (fun α => ∏ i : Fin n, nodes i ^ α i)).sum =
        exactPrefixH (List.ofFn nodes) k := by
  induction n generalizing k with
  | zero =>
      cases k <;> simp [List.Nat.antidiagonalTuple, exactPrefixH, List.ofFn]
  | succ n ih =>
      rw [List.ofFn_succ, exactPrefixH]
      simp only [List.Nat.antidiagonalTuple, List.map_flatMap,
        List.map_map, Function.comp_def, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, List.flatMap, List.sum_flatten,
        List.sum_map_mul_left, ih]

/-- Nat.rec retains the preceding coefficient in the original prefix
recurrence. This is an exact proof representation, not a new moment. -/
private def exactPrefixRec : List Nat → Nat → Nat
  | [] => fun k => if k = 0 then 1 else 0
  | a :: as =>
      Nat.rec 1 (fun k previous => exactPrefixRec as (k + 1) + a * previous)

private theorem exactPrefixH_eq_rec (as : List Nat) (k : Nat) :
    exactPrefixH as k = exactPrefixRec as k := by
  induction as generalizing k with
  | nil => rfl
  | cons a as ih =>
      induction k with
      | zero =>
          rw [exactPrefixH_zero]
          rfl
      | succ k ihk =>
          rw [exactPrefixH_cons_succ]
          change exactPrefixH as (k + 1) + a * exactPrefixH (a :: as) k =
            exactPrefixRec as (k + 1) + a * exactPrefixRec (a :: as) k
          rw [ih, ihk]

private theorem homogeneous_eq_exact_prefixRec (nodes : Fin 9 → Nat) (k : Nat) :
    homogeneous nodes k = exactPrefixRec (List.ofFn nodes) k := by
  calc
    homogeneous nodes k =
        ∑ α ∈ Finset.Nat.antidiagonalTuple 9 k, ∏ i : Fin 9, nodes i ^ α i :=
      homogeneous_eq_exact_antidiagonal nodes k
    _ = ((List.Nat.antidiagonalTuple 9 k).map
        (fun α => ∏ i : Fin 9, nodes i ^ α i)).sum := by rfl
    _ = exactPrefixH (List.ofFn nodes) k := antidiagonalTuple_sum_eq_prefixH nodes k
    _ = exactPrefixRec (List.ofFn nodes) k := exactPrefixH_eq_rec _ _

