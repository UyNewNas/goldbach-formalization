import ImbalancedChen.SelectedPrefixBoxCap
import ImbalancedChen.CompactLocalThreshold

/-!
# One refinement radius for a compact set of licensed prefixes

The strict selected-prefix license supplies a local endpoint-pair radius.
A common threshold for reciprocal natural radii follows from compactness
and the triangle inequality. The resulting single radius precedes every
center in the set and every rational endpoint pair. Empty compact sets are
included. This does not import certificate boxes or identify their coverage.
-/

namespace ImbalancedChen

open Filter Topology

/-- All sufficiently fine reciprocal meshes succeed uniformly over the
compact licensed set. The threshold is independent of the center and of
both rational endpoint functions. -/
theorem exists_selectedBoxCapCheck_uniform_mesh {n : ℕ}
    (I : Finset (Fin n)) (old nu : ℚ) (S : Set (Fin n → ℝ)) (hS : IsCompact S)
    (hlicense : ∀ t ∈ S, SelectedPrefixLicense I old nu t) :
    ∃ m₀ : ℕ, 2 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ t ∈ S,
      ∀ l u : Fin n → ℚ,
        dist (fun i => (l i : ℝ)) t < 1 / (m + 1 : ℝ) →
        dist (fun i => (u i : ℝ)) t < 1 / (m + 1 : ℝ) →
        selectedBoxCapCheck I old nu l u = true := by
  apply exists_uniform_threshold_on_compact_of_local_nhds S hS
    (fun m t => ∀ l u : Fin n → ℚ,
      dist (fun i => (l i : ℝ)) t < 1 / (m + 1 : ℝ) →
      dist (fun i => (u i : ℝ)) t < 1 / (m + 1 : ℝ) →
      selectedBoxCapCheck I old nu l u = true)
  intro t ht
  obtain ⟨delta, hd, hcheck⟩ :=
    exists_selectedBoxCapCheck_radius_of_strict I old nu t (hlicense t ht)
  obtain ⟨m₀, hm₀⟩ := exists_nat_one_div_lt (half_pos hd)
  refine ⟨m₀, ?_⟩
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨delta / 2, half_pos hd, ?_⟩
  intro x hx m hm l u hl hu
  have hden : (m₀ : ℝ) + 1 ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hm 1
  have hsmall : 1 / (m + 1 : ℝ) < delta / 2 :=
    (one_div_le_one_div_of_le (by positivity) hden).trans_lt hm₀
  apply hcheck l u
  · exact (dist_triangle _ x t).trans_lt (by linarith)
  · exact (dist_triangle _ x t).trans_lt (by linarith)

/-- A single positive radius licenses every sufficiently close rational
endpoint pair around every point of the compact set, including its boundary.
Endpoint ordering is unnecessary for the Boolean check itself. -/
theorem exists_selectedBoxCapCheck_uniform_radius {n : ℕ}
    (I : Finset (Fin n)) (old nu : ℚ) (S : Set (Fin n → ℝ)) (hS : IsCompact S)
    (hlicense : ∀ t ∈ S, SelectedPrefixLicense I old nu t) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ S, ∀ l u : Fin n → ℚ,
      dist (fun i => (l i : ℝ)) t < delta →
      dist (fun i => (u i : ℝ)) t < delta →
      selectedBoxCapCheck I old nu l u = true := by
  obtain ⟨m₀, _hm₀, hmesh⟩ :=
    exists_selectedBoxCapCheck_uniform_mesh I old nu S hS hlicense
  exact ⟨1 / (m₀ + 1 : ℝ), by positivity, hmesh m₀ le_rfl⟩

end ImbalancedChen
