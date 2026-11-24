/-- Reindex the original bounded exponent enumeration by the existing exact
sum-k tuple enumeration. Only the implementation of the finite sum changes
inside the proof; every original term appears exactly once. -/
private theorem homogeneous_eq_exact_antidiagonal (nodes : Fin 9 → Nat) (k : Nat) :
    homogeneous nodes k =
      ∑ α ∈ Finset.Nat.antidiagonalTuple 9 k, ∏ i : Fin 9, nodes i ^ α i := by
  classical
  unfold homogeneous
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun (α : Fin 9 → Fin (k + 1)) _ => fun i : Fin 9 => (α i).val) ?_ ?_ ?_ ?_
  · intro α hα
    exact Finset.Nat.mem_antidiagonalTuple.mpr (Finset.mem_filter.mp hα).2
  · intro α _ β _ h
    funext i
    exact Fin.ext (congrFun h i)
  · intro β hβ
    have hsum : (∑ i : Fin 9, β i) = k :=
      Finset.Nat.mem_antidiagonalTuple.mp hβ
    have hbound (i : Fin 9) : β i ≤ k := by
      calc
        β i ≤ ∑ j : Fin 9, β j :=
          Finset.single_le_sum (fun j _ => Nat.zero_le (β j)) (Finset.mem_univ i)
        _ = k := hsum
    let α : Fin 9 → Fin (k + 1) :=
      fun i => ⟨β i, Nat.lt_succ_of_le (hbound i)⟩
    refine ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · change (∑ i : Fin 9, β i) = k
      exact hsum
    · rfl
  · intro α _
    rfl

