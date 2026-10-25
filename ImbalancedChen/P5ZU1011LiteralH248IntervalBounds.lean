import ImbalancedChen.P5ZU1011H248CommonPartition

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Finite rational enclosures of the LITERAL clamped H248 lookup. Open atoms,
all singleton knots with adjacent-min values, the full knot50 clamp
half-space, and the actual zero exterior above five are retained. Extrema
are taken over finite reachable states, not over assumed table monotonicity.
No table recurrence licence, cell-bound supplier or numeric replay.
-/

namespace ImbalancedChen.P5Z.LiteralH248IntervalBounds

noncomputable section

open Set
open scoped BigOperators
open Classical
open Part5OriginalUpsilon5CausalDictionary Part5UpperTables
open U11H248 U1011H248Clamp U1011H248Partition

def grid (j : ℕ) : ℚ := 1 + (j : ℚ) / 50
def atomValue (i : Fin 200) : ℚ := (H248Numerators i : ℚ) / 2 ^ 80
def knotValue (j : Fin 201) : ℚ :=
  if h0 : j.val = 0 then atomValue 0
  else if hlast : j.val = 200 then atomValue 199
  else min (atomValue ⟨j.val - 1, by omega⟩) (atomValue ⟨j.val, by omega⟩)
def value : AtomState → ℚ
  | none => 0
  | some (.inl i) => atomValue i
  | some (.inr j) => knotValue j

theorem grid_cast (j : ℕ) : (grid j : ℝ) = floorGrid j := by
  simp only [grid, floorGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat]

theorem value_cast (a : AtomState) : (value a : ℝ) = stateValue a := by
  cases a with
  | none => rfl
  | some a =>
    cases a with
    | inl i => simp only [value, stateValue, floorAtomValue, atomValue, floorValue,
        Rat.cast_div, Rat.cast_intCast, Rat.cast_pow, Rat.cast_ofNat]
    | inr j =>
      unfold value stateValue floorAtomValue knotValue floorKnotValue
      split_ifs <;>
        simp only [atomValue, floorValue, Rat.cast_div, Rat.cast_intCast,
          Rat.cast_pow, Rat.cast_ofNat, Rat.cast_min]

def lowerQuery (l : ℚ) : ℚ := max 2 l
def upperQuery (u : ℚ) : ℚ := max 2 u

/-- EXACT finite intersection tests. At a marked knot both endpoint
inequalities are weak. At an open atom both intersection tests are strict. -/
def Reachable (l u : ℚ) : AtomState → Prop
  | none => 5 < upperQuery u
  | some (.inl i) => lowerQuery l < grid (i.val + 1) ∧ grid i.val < upperQuery u
  | some (.inr j) => lowerQuery l ≤ grid j.val ∧ grid j.val ≤ upperQuery u

instance (l u : ℚ) (a : AtomState) : Decidable (Reachable l u a) := by
  cases a with
  | none => unfold Reachable; infer_instance
  | some a => cases a <;> unfold Reachable <;> infer_instance

def reachableStates (l u : ℚ) : Finset AtomState := Finset.univ.filter (Reachable l u)
def reachableValues (l u : ℚ) : Finset ℚ := (reachableStates l u).image value

theorem reachable_of_state {l u : ℚ} {s : ℝ} {a : AtomState}
    (hl : (l : ℝ) ≤ s) (hu : s ≤ (u : ℝ)) (ha : s ∈ scalarCell a) :
    Reachable l u a := by
  have hLow : (lowerQuery l : ℝ) ≤ max 2 s := by
    simpa only [lowerQuery, Rat.cast_max, Rat.cast_ofNat] using max_le_max le_rfl hl
  have hUp : max 2 s ≤ (upperQuery u : ℝ) := by
    simpa only [upperQuery, Rat.cast_max, Rat.cast_ofNat] using max_le_max le_rfl hu
  cases a with
  | none =>
    have hs := (mem_scalarCell_none_iff s).mp ha
    have hR : (5 : ℝ) < (upperQuery u : ℝ) := hs.trans_le
      ((le_max_right (2 : ℝ) s).trans hUp)
    exact_mod_cast hR
  | some a =>
    cases a with
    | inl i =>
      have h1 : (lowerQuery l : ℝ) < (grid (i.val + 1) : ℝ) := by
        rw [grid_cast]
        exact hLow.trans_lt ha.2.2
      have h2 : (grid i.val : ℝ) < (upperQuery u : ℝ) := by
        rw [grid_cast]
        exact ha.2.1.trans_le hUp
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    | inr j =>
      have h1 : (lowerQuery l : ℝ) ≤ (grid j.val : ℝ) := by
        rw [grid_cast]
        exact hLow.trans_eq ha.2
      have h2 : (grid j.val : ℝ) ≤ (upperQuery u : ℝ) := by
        rw [grid_cast]
        exact ha.2.symm.trans_le hUp
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

private theorem rational_open_intersection {l u a b : ℚ}
    (hlu : l ≤ u) (hab : a < b) (hlb : l < b) (hau : a < u) :
    ∃ q : ℚ, l ≤ q ∧ q ≤ u ∧ a < q ∧ q < b := by
  by_cases hal : a < l
  · exact ⟨l, le_rfl, hlu, hal, hlb⟩
  · have hla : l ≤ a := le_of_not_gt hal
    have hmin : a < min u b := lt_min hau hab
    refine ⟨(a + min u b) / 2, ?_, ?_, ?_, ?_⟩
    · linarith only [hla, hmin]
    · have hh := min_le_left u b
      linarith only [hmin, hh]
    · linarith only [hmin]
    · have hh := min_le_right u b
      linarith only [hmin, hh]

private theorem clamp_preimage {l u q : ℚ} (hlu : l ≤ u)
    (hq : lowerQuery l ≤ q ∧ q ≤ upperQuery u) :
    ∃ s : ℚ, l ≤ s ∧ s ≤ u ∧ max 2 s = q := by
  have hq2 : 2 ≤ q := (le_max_left (2 : ℚ) l).trans hq.1
  by_cases hqle : q ≤ 2
  · have hqeq : q = 2 := le_antisymm hqle hq2
    have hl2 : l ≤ 2 := (le_max_right (2 : ℚ) l).trans (hq.1.trans hqle)
    exact ⟨l, le_rfl, hlu, by rw [max_eq_left hl2, hqeq]⟩
  · have hqu : q ≤ u := by
      rcases le_max_iff.mp hq.2 with h | h
      · exact (hqle h).elim
      · exact h
    have hlq : l ≤ q := (le_max_right (2 : ℚ) l).trans hq.1
    exact ⟨q, hlq, hqu, max_eq_right hq2⟩

/-- Every enumerated state has an ACTUAL raw-query witness in [l,u].
Thus the finite extrema use the literal reachable states, not an arbitrary
interval certificate supplied by a caller. -/
theorem state_witness_of_reachable {l u : ℚ} (hlu : l ≤ u)
    {a : AtomState} (ha : Reachable l u a) :
    ∃ s : ℚ, l ≤ s ∧ s ≤ u ∧ (s : ℝ) ∈ scalarCell a := by
  have hqueries : lowerQuery l ≤ upperQuery u := max_le_max le_rfl hlu
  cases a with
  | none =>
    have hu5 : (5 : ℚ) < u := by
      have hh : 5 < max (2 : ℚ) u := ha
      rcases lt_max_iff.mp hh with h | h
      · norm_num at h
      · exact h
    refine ⟨u, hlu, le_rfl, ?_⟩
    apply (mem_scalarCell_none_iff (u : ℝ)).mpr
    exact_mod_cast hu5
  | some a =>
    cases a with
    | inl i =>
      have hgrid : grid i.val < grid (i.val + 1) := by
        unfold grid
        push_cast
        linarith
      obtain ⟨q, hql, hqu, hqg, hqg'⟩ := rational_open_intersection hqueries hgrid ha.1 ha.2
      obtain ⟨s, hsl, hsu, hsq⟩ := clamp_preimage hlu ⟨hql, hqu⟩
      have hq2 : (2 : ℚ) ≤ q := (le_max_left (2 : ℚ) l).trans hql
      have hq5 : q ≤ 5 := by
        have hi : i.val + 1 ≤ 200 := by omega
        have hcast : (i.val : ℚ) + 1 ≤ 200 := by exact_mod_cast hi
        unfold grid at hqg'
        push_cast at hqg'
        linarith only [hqg', hcast]
      refine ⟨s, hsl, hsu, ?_⟩
      change max 2 (s : ℝ) ∈ Icc (1 : ℝ) 5 ∩
        Ioo (floorGrid i.val) (floorGrid (i.val + 1))
      have hmax : max 2 (s : ℝ) = (q : ℝ) := by exact_mod_cast hsq
      rw [hmax, ← grid_cast, ← grid_cast]
      exact ⟨⟨by exact_mod_cast (show (1 : ℚ) ≤ q by linarith),
        by exact_mod_cast hq5⟩, by exact_mod_cast hqg, by exact_mod_cast hqg'⟩
    | inr j =>
      obtain ⟨s, hsl, hsu, hsq⟩ := clamp_preimage hlu ha
      have hj : j.val ≤ 200 := by omega
      have hgrid : (1 : ℚ) ≤ grid j.val ∧ grid j.val ≤ 5 := by
        have h0 : (0 : ℚ) ≤ j.val := Nat.cast_nonneg _
        have h200 : (j.val : ℚ) ≤ 200 := by exact_mod_cast hj
        unfold grid
        constructor <;> linarith
      refine ⟨s, hsl, hsu, ?_⟩
      change max 2 (s : ℝ) ∈ Icc (1 : ℝ) 5 ∩ {floorGrid j.val}
      have hmax : max 2 (s : ℝ) = (grid j.val : ℝ) := by exact_mod_cast hsq
      rw [hmax, ← grid_cast]
      exact ⟨by exact_mod_cast hgrid, rfl⟩

theorem reachableValues_nonempty {l u : ℚ} (hlu : l ≤ u) :
    (reachableValues l u).Nonempty := by
  have hs := chosenState_mem (l : ℝ)
  have hr := reachable_of_state (le_refl (l : ℝ)) (by exact_mod_cast hlu) hs
  exact ⟨value (chosenState (l : ℝ)), Finset.mem_image.mpr
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩⟩

def profileIntervalLower (l u : ℚ) : ℚ :=
  if h : l ≤ u then (reachableValues l u).min' (reachableValues_nonempty h) else 0
def profileIntervalUpper (l u : ℚ) : ℚ :=
  if h : l ≤ u then (reachableValues l u).max' (reachableValues_nonempty h) else 0

/-- Genuine directed literal floor interval enclosure, including all
marked knots, clamp50 and zero exterior. No hCellBound premise. -/
theorem profileInterval_bounds {l u : ℚ} {s : ℝ}
    (hl : (l : ℝ) ≤ s) (hu : s ≤ (u : ℝ)) :
    (profileIntervalLower l u : ℝ) ≤ H248 (max 2 s) ∧
      H248 (max 2 s) ≤ (profileIntervalUpper l u : ℝ) := by
  have hlu : l ≤ u := by exact_mod_cast hl.trans hu
  let a := chosenState s
  have ha : s ∈ scalarCell a := chosenState_mem s
  have hr := reachable_of_state hl hu ha
  have hmem : value a ∈ reachableValues l u := Finset.mem_image.mpr
    ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩, rfl⟩
  have hL : profileIntervalLower l u ≤ value a := by
    rw [profileIntervalLower, dif_pos hlu]
    exact Finset.min'_le _ _ hmem
  have hU : value a ≤ profileIntervalUpper l u := by
    rw [profileIntervalUpper, dif_pos hlu]
    exact Finset.le_max' _ _ hmem
  rw [H248_eq_stateValue ha, ← value_cast]
  exact ⟨by exact_mod_cast hL, by exact_mod_cast hU⟩

theorem literal_knot_value (j : Fin 201) :
    value (some (.inr j)) =
      if h0 : j.val = 0 then atomValue 0
      else if hlast : j.val = 200 then atomValue 199
      else min (atomValue ⟨j.val - 1, by omega⟩) (atomValue ⟨j.val, by omega⟩) := rfl

theorem literal_clamp50 : value (some (.inr clampKnot)) = min (atomValue 49) (atomValue 50) := by
  norm_num [value, knotValue, clampKnot]

theorem exterior_value : value none = 0 := rfl

theorem value_bounds (a : AtomState) : (0 : ℚ) ≤ value a ∧ value a ≤ 1 := by
  cases a with
  | none => norm_num [value]
  | some b =>
    have h := H248_atom_bounds b
    have heq := value_cast (some b)
    change (value (some b) : ℝ) = floorAtomValue H248Numerators b at heq
    rw [← heq] at h
    exact_mod_cast h

theorem profileInterval_range {l u : ℚ} (hlu : l ≤ u) :
    0 ≤ profileIntervalLower l u ∧
      profileIntervalLower l u ≤ profileIntervalUpper l u ∧
      profileIntervalUpper l u ≤ 1 := by
  have hV := reachableValues_nonempty hlu
  have hmin := Finset.min'_mem (reachableValues l u) hV
  have hmax := Finset.max'_mem (reachableValues l u) hV
  obtain ⟨a, ha, heqa⟩ := Finset.mem_image.mp hmin
  obtain ⟨b, hb, heqb⟩ := Finset.mem_image.mp hmax
  have hA := value_bounds a
  have hB := value_bounds b
  rw [heqa] at hA
  rw [heqb] at hB
  simp only [profileIntervalLower, profileIntervalUpper, dif_pos hlu]
  exact ⟨hA.1, Finset.min'_le_max' _ hV, hB.2⟩

end

end ImbalancedChen.P5Z.LiteralH248IntervalBounds
