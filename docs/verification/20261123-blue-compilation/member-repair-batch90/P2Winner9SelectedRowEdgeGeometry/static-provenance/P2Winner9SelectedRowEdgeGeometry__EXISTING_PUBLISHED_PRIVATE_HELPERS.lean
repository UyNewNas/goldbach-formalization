/-- Trailing matrix after clearing the first column below its pivot. -/
private def trailingMatrix {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => A i.succ j.succ + -(A i.succ 0 / A 0 0) * A 0 j.succ

private theorem det_eliminate_first_column {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (pivot : A 0 0 ≠ 0) :
    A.det = A 0 0 * (trailingMatrix A).det := by
  let c (i : Fin (n + 1)) : ℚ := if i = 0 then 0 else -(A i 0 / A 0 0)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
    fun i j => A i j + c i * A 0 j
  have hDet : B.det = A.det :=
    Matrix.det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [c]) (fun _ _ => rfl)
  have hFirst : B 0 0 = A 0 0 := by simp [B, c]
  have hColumn (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, c, neg_mul, div_mul_cancel₀ _ pivot]
  have hMinor : B.submatrix Fin.succ Fin.succ = trailingMatrix A := by
    ext i j
    change A i.succ j.succ + c i.succ * A 0 j.succ = _
    simp [c, trailingMatrix]
  rw [← hDet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hFirst, hColumn, hMinor]

private def firstNonzeroBelow {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (A i.succ 0 ≠ 0)

private def addToFirstRow {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (i : Fin n) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ :=
  A.updateRow 0 (A 0 + A i.succ)

/-- Evaluate the rational determinant via row addition and pivot division. -/
private def pivotDet : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → ℚ
  | 0, _ => 1
  | n + 1, A =>
      if A 0 0 = 0 then
        match firstNonzeroBelow A with
        | none => 0
        | some i =>
            let B := addToFirstRow A i
            B 0 0 * pivotDet n (trailingMatrix B)
      else
        A 0 0 * pivotDet n (trailingMatrix A)

private theorem pivotDet_eq (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) :
    pivotDet n A = A.det := by
  induction n with
  | zero => simp [pivotDet]
  | succ n ih =>
      by_cases hz : A 0 0 = 0
      · cases hf : firstNonzeroBelow A with
        | none =>
            rw [pivotDet, if_pos hz, hf]
            symm
            apply Matrix.det_eq_zero_of_column_eq_zero 0
            refine Fin.cases hz (fun i => ?_)
            have hNone := List.find?_eq_none.mp hf
            simpa using hNone i (List.mem_finRange i)
        | some i =>
            let B := addToFirstRow A i
            have hi : A i.succ 0 ≠ 0 := by
              simpa using List.find?_some hf
            have hB : B 0 0 ≠ 0 := by
              simpa [B, addToFirstRow, Matrix.updateRow_self, Pi.add_apply, hz] using hi
            rw [pivotDet, if_pos hz, hf]
            change B 0 0 * pivotDet n (trailingMatrix B) = A.det
            rw [ih, ← det_eliminate_first_column B hB]
            exact Matrix.det_updateRow_add_self A (Fin.succ_ne_zero i).symm
      · rw [pivotDet, if_neg hz, ih, ← det_eliminate_first_column A hz]

