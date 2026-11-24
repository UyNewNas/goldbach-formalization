
@[simp] theorem map_id_fun : map (id : α → α) = id := by
  funext l
  induction l <;> simp_all

/-- `map_id_fun'` differs from `map_id_fun` by representing the identity function as a lambda, rather than `id`. -/
@[simp] theorem map_id_fun' : map (fun (a : α) => a) = id := map_id_fun

-- This is not a `@[simp]` lemma because `map_id_fun` will apply.
-- The argument `l : List α` is explicit to allow rewriting from right to left.
theorem map_id (l : List α) : map (id : α → α) l = l := by
  induction l <;> simp_all

