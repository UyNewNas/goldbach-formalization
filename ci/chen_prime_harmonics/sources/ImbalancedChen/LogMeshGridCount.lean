import ImbalancedChen.BoundaryLogMesh

/-!
# Explicit polylogarithmic rectangle counts for the logarithmic mesh

The elementary inequality `delta / 2 <= log (1 + delta)` for `0 < delta <= 1`
turns the exact finite multiplicative-grid count into a polylogarithmic
bound. For `delta = 1 / (log N)^k`, the complete grid and both actually
selected envelope families have at most `(2 * (log N)^(k+1) + 1)^2` cells.
The floor and the final endpoint cell are retained. No distribution input
or prime-counting assumption is used.
-/

namespace ImbalancedChen

open Filter

noncomputable section

/-- An elementary lower bound for the logarithm of a small mesh ratio. -/
theorem half_mesh_le_log_one_add {delta : ℝ}
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    delta / 2 ≤ Real.log (1 + delta) := by
  calc
    delta / 2 ≤ 2 * delta / (delta + 2) := by
      apply (le_div_iff₀ (by linarith : 0 < delta + 2)).mpr
      nlinarith [mul_nonneg hdelta (sub_nonneg.mpr hdelta1)]
    _ ≤ Real.log (1 + delta) := Real.le_log_one_add_of_nonneg hdelta

/-- The exact finite grid count has an explicit bound in terms of its mesh.
The `+1` retains the final cell containing the coordinate endpoint `N`. -/
theorem multiplicativeGridIndices_card_le_small_mesh
    {delta N : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (hN : 1 ≤ N) :
    ((multiplicativeGridIndices (1 + delta) N).card : ℝ) ≤
      (2 * Real.log N / delta + 1) ^ 2 := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogbase : 0 < Real.log (1 + delta) := Real.log_pos (by linarith)
  have hfloor :
      (Nat.floor (Real.log N / Real.log (1 + delta)) : ℝ) ≤
        Real.log N / Real.log (1 + delta) :=
    Nat.floor_le (div_nonneg hlogN hlogbase.le)
  have hratio : Real.log N / Real.log (1 + delta) ≤ 2 * Real.log N / delta := by
    calc
      Real.log N / Real.log (1 + delta) ≤ Real.log N / (delta / 2) :=
        div_le_div_of_nonneg_left hlogN (by positivity)
          (half_mesh_le_log_one_add hdelta.le hdelta1)
      _ = 2 * Real.log N / delta := by ring
  rw [multiplicativeGridIndices_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  exact pow_le_pow_left₀ (by positivity) (add_le_add (hfloor.trans hratio) le_rfl) 2

/-- The full grid for the literal logarithmic mesh has only polylogarithmically
many cells, without removing empty rectangles or changing grid endpoints. -/
theorem multiplicativeGridIndices_logMesh_card_le (k N : ℕ)
    (hN : 1 ≤ (N : ℝ)) (hlog : 1 ≤ Real.log (N : ℝ)) :
    ((multiplicativeGridIndices (1 + boundaryLogMesh k N) (N : ℝ)).card : ℝ) ≤
      (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 := by
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hmesh : 0 < boundaryLogMesh k N := div_pos zero_lt_one (pow_pos hlogpos k)
  have hmesh1 : boundaryLogMesh k N ≤ 1 :=
    (div_le_one (pow_pos hlogpos k)).mpr (one_le_pow₀ hlog)
  have hcount := multiplicativeGridIndices_card_le_small_mesh hmesh hmesh1 hN
  have hid : 2 * Real.log (N : ℝ) / boundaryLogMesh k N =
      2 * (Real.log (N : ℝ)) ^ (k + 1) := by
    unfold boundaryLogMesh
    rw [pow_succ]
    field_simp [hlogpos.ne'] <;> ring
  rwa [hid] at hcount

/-- Eventual polylogarithmic count of the entire literal grid. -/
theorem eventually_multiplicativeGridIndices_logMesh_card_le (k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      ((multiplicativeGridIndices (1 + boundaryLogMesh k N) (N : ℝ)).card : ℝ) ≤
        (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 := by
  filter_upwards [eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)] with N hlog hN
  exact multiplicativeGridIndices_logMesh_card_le k N (by exact_mod_cast hN) hlog

/-- Both actual envelope families obey the same count, uniformly in all
source exponents and real cutoffs. No geometric range restrictions are
needed merely to bound a selected subfamily of the complete finite grid. -/
theorem eventually_actualGrid_logMesh_card_le (k : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ num den : ℕ, ∀ T : ℝ,
      ((actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N)).card : ℝ) ≤
        (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 ∧
      ((actualGridInsideIndices num den N T (1 + boundaryLogMesh k N)).card : ℝ) ≤
        (2 * (Real.log (N : ℝ)) ^ (k + 1) + 1) ^ 2 := by
  classical
  filter_upwards [eventually_multiplicativeGridIndices_logMesh_card_le k] with N hgrid
  intro num den T
  have hinter :
      (actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N)).card ≤
        (multiplicativeGridIndices (1 + boundaryLogMesh k N) (N : ℝ)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hinside :
      (actualGridInsideIndices num den N T (1 + boundaryLogMesh k N)).card ≤
        (actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hinterR :
      ((actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N)).card : ℝ) ≤
        ((multiplicativeGridIndices (1 + boundaryLogMesh k N) (N : ℝ)).card : ℝ) := by
    exact_mod_cast hinter
  have hinsideR :
      ((actualGridInsideIndices num den N T (1 + boundaryLogMesh k N)).card : ℝ) ≤
        ((actualGridIntersectingIndices num den N T (1 + boundaryLogMesh k N)).card : ℝ) := by
    exact_mod_cast hinside
  exact ⟨hinterR.trans hgrid, hinsideR.trans (hinterR.trans hgrid)⟩

end

end ImbalancedChen
