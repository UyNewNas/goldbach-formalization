import ImbalancedChen.P5ZU1011LiteralH248IntervalBounds

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Literal floor interval extrema are attained by actual raw rational
queries and refine monotonically. Rational single-state guards collapse
both extrema exactly, including open cells, every marked knot, the full
clamp50 half-space and the actual zero exterior above five. No table
monotonicity or desired interval-value premise is assumed.
-/

namespace ImbalancedChen.P5Z.LiteralH248IntervalRefinement

noncomputable section

open Set Part5UpperTables Part5OriginalUpsilon5CausalDictionary
open U1011H248Clamp U1011H248Partition LiteralH248IntervalBounds

theorem lower_attained {l u : ℚ} (hlu : l ≤ u) :
    ∃ s : ℚ, l ≤ s ∧ s ≤ u ∧
      H248 (max 2 (s : ℝ)) = (profileIntervalLower l u : ℝ) := by
  have hm := Finset.min'_mem (reachableValues l u) (reachableValues_nonempty hlu)
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
  have hr := (Finset.mem_filter.mp ha).2
  obtain ⟨s, hsl, hsu, hs⟩ := state_witness_of_reachable hlu hr
  refine ⟨s, hsl, hsu, ?_⟩
  rw [H248_eq_stateValue hs, ← value_cast]
  have hq : value a = profileIntervalLower l u := by
    simpa only [profileIntervalLower, dif_pos hlu] using heq
  exact_mod_cast hq

theorem upper_attained {l u : ℚ} (hlu : l ≤ u) :
    ∃ s : ℚ, l ≤ s ∧ s ≤ u ∧
      H248 (max 2 (s : ℝ)) = (profileIntervalUpper l u : ℝ) := by
  have hm := Finset.max'_mem (reachableValues l u) (reachableValues_nonempty hlu)
  obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp hm
  have hr := (Finset.mem_filter.mp ha).2
  obtain ⟨s, hsl, hsu, hs⟩ := state_witness_of_reachable hlu hr
  refine ⟨s, hsl, hsu, ?_⟩
  rw [H248_eq_stateValue hs, ← value_cast]
  have hq : value a = profileIntervalUpper l u := by
    simpa only [profileIntervalUpper, dif_pos hlu] using heq
  exact_mod_cast hq

/-- Interval refinement is valid for the literal nonmonotone H248 array.
It follows from attained finite extrema, not from monotonicity of H248. -/
theorem refinement {l u l' u' : ℚ} (hl : l ≤ l') (hlu : l' ≤ u') (hu : u' ≤ u) :
    profileIntervalLower l u ≤ profileIntervalLower l' u' ∧
      profileIntervalUpper l' u' ≤ profileIntervalUpper l u := by
  obtain ⟨s, hsl, hsu, hs⟩ := lower_attained hlu
  obtain ⟨t, htl, htu, ht⟩ := upper_attained hlu
  have hLs := (profileInterval_bounds (l := l) (u := u) (s := (s : ℝ)) (by exact_mod_cast hl.trans hsl)
    (by exact_mod_cast hsu.trans hu)).1
  have hUt := (profileInterval_bounds (l := l) (u := u) (s := (t : ℝ)) (by exact_mod_cast hl.trans htl)
    (by exact_mod_cast htu.trans hu)).2
  rw [hs] at hLs
  rw [ht] at hUt
  exact ⟨by exact_mod_cast hLs, by exact_mod_cast hUt⟩

private theorem values_singleton_of_state {l u : ℚ} (hlu : l ≤ u) (a : AtomState)
    (hstate : ∀ s : ℚ, l ≤ s → s ≤ u → (s : ℝ) ∈ scalarCell a) :
    reachableValues l u = {value a} := by
  have ha := reachable_of_state (le_refl (l : ℝ)) (by exact_mod_cast hlu)
    (hstate l le_rfl hlu)
  have hmem : value a ∈ reachableValues l u := Finset.mem_image.mpr
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩
  ext q
  rw [Finset.mem_singleton]
  constructor
  · intro hq
    obtain ⟨b, hb, hval⟩ := Finset.mem_image.mp hq
    obtain ⟨s, hsl, hsu, hs⟩ := state_witness_of_reachable hlu (Finset.mem_filter.mp hb).2
    have hba : b = a := scalarCell_unique hs (hstate s hsl hsu)
    subst b
    exact hval.symm
  · intro hq
    simpa only [hq] using hmem

private theorem extrema_singleton_of_state {l u : ℚ} (hlu : l ≤ u) (a : AtomState)
    (hstate : ∀ s : ℚ, l ≤ s → s ≤ u → (s : ℝ) ∈ scalarCell a) :
    profileIntervalLower l u = value a ∧ profileIntervalUpper l u = value a := by
  have hset := values_singleton_of_state hlu a hstate
  simp only [profileIntervalLower, profileIntervalUpper, dif_pos hlu, hset,
    Finset.min'_singleton, Finset.max'_singleton]

theorem exact_clamp_interval {l u : ℚ} (hlu : l ≤ u) (hu : u ≤ 2) :
    profileIntervalLower l u = min (atomValue 49) (atomValue 50) ∧
      profileIntervalUpper l u = min (atomValue 49) (atomValue 50) := by
  have hs : ∀ s : ℚ, l ≤ s → s ≤ u → (s : ℝ) ∈ scalarCell (some (.inr clampKnot)) := by
    intro s _ hsu
    have hs2 : (s : ℝ) ≤ 2 := by exact_mod_cast hsu.trans hu
    change max 2 (s : ℝ) ∈ Icc (1 : ℝ) 5 ∩ {floorGrid 50}
    rw [max_eq_left hs2, floorGrid_fifty]
    norm_num
  simpa only [literal_clamp50] using extrema_singleton_of_state hlu _ hs

theorem exact_exterior_interval {l u : ℚ} (hlu : l ≤ u) (hl : 5 < l) :
    profileIntervalLower l u = 0 ∧ profileIntervalUpper l u = 0 := by
  have hs : ∀ s : ℚ, l ≤ s → s ≤ u → (s : ℝ) ∈ scalarCell none := by
    intro s hls _
    apply (mem_scalarCell_none_iff (s : ℝ)).mpr
    exact_mod_cast hl.trans_le hls
  simpa only [exterior_value] using extrema_singleton_of_state hlu none hs

/-- A strict rational open-cell guard makes both finite extrema equal
the actual serialized integer, even when the original raw interval is wide. -/
theorem exact_open_interval {l u : ℚ} (hlu : l ≤ u) (i : Fin 200)
    (hl : grid i.val < lowerQuery l) (hu : upperQuery u < grid (i.val + 1)) :
    profileIntervalLower l u = atomValue i ∧ profileIntervalUpper l u = atomValue i := by
  have hs : ∀ s : ℚ, l ≤ s → s ≤ u → (s : ℝ) ∈ scalarCell (some (.inl i)) := by
    intro s hls hsu
    have hqL : lowerQuery l ≤ max 2 s := max_le_max le_rfl hls
    have hqU : max 2 s ≤ upperQuery u := max_le_max le_rfl hsu
    have hLo : (grid i.val : ℝ) < max 2 (s : ℝ) := by exact_mod_cast hl.trans_le hqL
    have hHi : max 2 (s : ℝ) < (grid (i.val + 1) : ℝ) := by exact_mod_cast hqU.trans_lt hu
    have h5 : (grid (i.val + 1) : ℝ) ≤ 5 := by
      have hi : i.val + 1 ≤ 200 := by omega
      have hcast : (i.val : ℝ) + 1 ≤ 200 := by exact_mod_cast hi
      rw [grid_cast]
      simp only [floorGrid, Nat.cast_add, Nat.cast_one]
      linarith only [hcast]
    change max 2 (s : ℝ) ∈ Icc (1 : ℝ) 5 ∩ Ioo (floorGrid i.val) (floorGrid (i.val + 1))
    rw [← grid_cast, ← grid_cast]
    exact ⟨⟨by linarith [le_max_left (2 : ℝ) (s : ℝ)], hHi.le.trans h5⟩, hLo, hHi⟩
  exact extrema_singleton_of_state hlu _ hs

/-- Singleton query states use the actual adjacent MINIMUM at every
marked knot, including the last knot. No almost-everywhere erasure. -/
theorem exact_knot_interval {l u : ℚ} (hlu : l ≤ u) (j : Fin 201)
    (hl : lowerQuery l = grid j.val) (hu : upperQuery u = grid j.val) :
    profileIntervalLower l u = knotValue j ∧ profileIntervalUpper l u = knotValue j := by
  have hs : ∀ s : ℚ, l ≤ s → s ≤ u → (s : ℝ) ∈ scalarCell (some (.inr j)) := by
    intro s hls hsu
    have hqL : lowerQuery l ≤ max 2 s := max_le_max le_rfl hls
    have hqU : max 2 s ≤ upperQuery u := max_le_max le_rfl hsu
    have hq : max 2 s = grid j.val := le_antisymm (by simpa only [hu] using hqU)
      (by simpa only [hl] using hqL)
    have hmax : max 2 (s : ℝ) = (grid j.val : ℝ) := by exact_mod_cast hq
    have hgrid : (grid j.val : ℝ) ∈ Icc (1 : ℝ) 5 := by
      have h0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
      have h200 : (j.val : ℝ) ≤ 200 := by exact_mod_cast (show j.val ≤ 200 by omega)
      rw [grid_cast]
      unfold floorGrid
      constructor <;> linarith
    change max 2 (s : ℝ) ∈ Icc (1 : ℝ) 5 ∩ {floorGrid j.val}
    rw [hmax, ← grid_cast]
    exact ⟨hgrid, rfl⟩
  exact extrema_singleton_of_state hlu _ hs

end

end ImbalancedChen.P5Z.LiteralH248IntervalRefinement
