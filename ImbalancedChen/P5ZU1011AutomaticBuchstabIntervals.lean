import ImbalancedChen.P5ZU1011AutomaticBuchstabCells

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Automatic finite rational omega interval supplier on [2,8]. The reachable
closed cells are generated from rational comparisons; every coefficient
comes from the deterministic delayed-node recurrence, without node input.
The actual width is at most (u-l)/2 + 3000/m. No numerical replay occurs.
-/

namespace ImbalancedChen.P5Z.AutomaticBuchstabIntervals

noncomputable section

open Set LiLiuPrereqBuchstab
open Certificates.P2BuchstabRationalSemantics
open AutomaticBuchstabCells

theorem grid_zero (m : ℕ) : grid m 0 = 1 := by simp [grid]

theorem grid_seven (m : ℕ) (hm : 0 < m) : grid m (7 * m) = 8 := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [grid, Nat.cast_mul, Nat.cast_ofNat]
  field_simp [hm0]
  <;> ring

/-- Finite closed grid coverage, including its final endpoint. -/
theorem closed_grid_cover (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {s : ℝ} (hs : s ∈ Icc (grid m 0 : ℝ) (grid m n : ℝ)) :
    ∃ k : ℕ, k < n ∧ s ∈ Icc (grid m k : ℝ) (grid m (k + 1) : ℝ) := by
  suffices h : ∀ n : ℕ, 0 < n → ∀ s : ℝ,
      s ∈ Icc (grid m 0 : ℝ) (grid m n : ℝ) →
        ∃ k : ℕ, k < n ∧ s ∈ Icc (grid m k : ℝ) (grid m (k + 1) : ℝ) from
    h n hn s hs
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
      intro _ s hs
      by_cases hn0 : n = 0
      · subst n
        exact ⟨0, by omega, hs⟩
      · by_cases hleft : s ≤ (grid m n : ℝ)
        · obtain ⟨k, hk, hcell⟩ := ih (by omega) s ⟨hs.1, hleft⟩
          exact ⟨k, by omega, hcell⟩
        · exact ⟨n, Nat.lt_succ_self n, (lt_of_not_ge hleft).le, hs.2⟩

def cells (m : ℕ) (l u : ℚ) : Finset ℕ :=
  (Finset.range (7 * m)).filter fun k => grid m k ≤ u ∧ l ≤ grid m (k + 1)

theorem mem_cells {m k : ℕ} {l u : ℚ} :
    k ∈ cells m l u ↔ k < 7 * m ∧ grid m k ≤ u ∧ l ≤ grid m (k + 1) := by
  simp only [cells, Finset.mem_filter, Finset.mem_range]

theorem query_cell (m : ℕ) (hm : 0 < m) {l u : ℚ}
    (hl : 1 ≤ l) (hlu : l ≤ u) (hu : u ≤ 8) {s : ℝ}
    (hs : s ∈ Icc (l : ℝ) (u : ℝ)) :
    ∃ k ∈ cells m l u, s ∈ Icc (grid m k : ℝ) (grid m (k + 1) : ℝ) := by
  have hs0 : (grid m 0 : ℝ) ≤ s := by
    rw [grid_zero]
    exact (show (1 : ℝ) ≤ (l : ℝ) by exact_mod_cast hl).trans hs.1
  have hs7 : s ≤ (grid m (7 * m) : ℝ) := by
    rw [grid_seven m hm]
    exact hs.2.trans (show (u : ℝ) ≤ 8 by exact_mod_cast hu)
  obtain ⟨k, hk, hcell⟩ := closed_grid_cover m (7 * m) hm (by omega) ⟨hs0, hs7⟩
  refine ⟨k, mem_cells.mpr ⟨hk, ?_, ?_⟩, hcell⟩
  · exact_mod_cast hcell.1.trans hs.2
  · exact_mod_cast hs.1.trans hcell.2

theorem cells_nonempty (m : ℕ) (hm : 0 < m) {l u : ℚ}
    (hl : 1 ≤ l) (hlu : l ≤ u) (hu : u ≤ 8) : (cells m l u).Nonempty := by
  obtain ⟨k, hk, _⟩ := query_cell m hm hl hlu hu
    (s := (l : ℝ)) ⟨le_rfl, by exact_mod_cast hlu⟩
  exact ⟨k, hk⟩

/-- Rational closed-intersection witness for EACH retained cell. -/
theorem cell_witness (m : ℕ) (hm : 0 < m) {l u : ℚ} (hlu : l ≤ u)
    {k : ℕ} (hk : k ∈ cells m l u) :
    ∃ x : ℚ, x ∈ Icc l u ∧ x ∈ Icc (grid m k) (grid m (k + 1)) := by
  have hh := mem_cells.mp hk
  refine ⟨max l (grid m k), ⟨le_max_left _ _, max_le hlu hh.2.1⟩,
    le_max_right _ _, max_le hh.2.2 (grid_le_next m k hm)⟩

def lowerValues (m : ℕ) (l u : ℚ) : Finset ℚ :=
  (cells m l u).image (cellLower m)
def upperValues (m : ℕ) (l u : ℚ) : Finset ℚ :=
  (cells m l u).image (cellUpper m)

def intervalLower (m : ℕ) (l u : ℚ) : ℚ :=
  if h : (cells m l u).Nonempty then
    (lowerValues m l u).min' (h.image _) else 0
def intervalUpper (m : ℕ) (l u : ℚ) : ℚ :=
  if h : (cells m l u).Nonempty then
    (upperValues m l u).max' (h.image _) else 1

theorem lower_le_cell {m k : ℕ} {l u : ℚ} (hk : k ∈ cells m l u) :
    intervalLower m l u ≤ cellLower m k := by
  have hn : (cells m l u).Nonempty := ⟨k, hk⟩
  rw [intervalLower, dif_pos hn]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem cell_le_upper {m k : ℕ} {l u : ℚ} (hk : k ∈ cells m l u) :
    cellUpper m k ≤ intervalUpper m l u := by
  have hn : (cells m l u).Nonempty := ⟨k, hk⟩
  rw [intervalUpper, dif_pos hn]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)

theorem lower_attained {m : ℕ} {l u : ℚ} (hn : (cells m l u).Nonempty) :
    ∃ k ∈ cells m l u, cellLower m k = intervalLower m l u := by
  have hh := Finset.min'_mem (lowerValues m l u) (hn.image (cellLower m))
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hh
  refine ⟨k, hk, ?_⟩
  simpa only [intervalLower, dif_pos hn] using heq

theorem upper_attained {m : ℕ} {l u : ℚ} (hn : (cells m l u).Nonempty) :
    ∃ k ∈ cells m l u, cellUpper m k = intervalUpper m l u := by
  have hh := Finset.max'_mem (upperValues m l u) (hn.image (cellUpper m))
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hh
  refine ⟨k, hk, ?_⟩
  simpa only [intervalUpper, dif_pos hn] using heq

/-- Actual automatic whole-interval omega enclosure, including knots. -/
theorem actual_interval_bounds (m : ℕ) (hm : 0 < m) {l u : ℚ}
    (hl : 1 ≤ l) (hlu : l ≤ u) (hu : u ≤ 8) {s : ℝ}
    (hs : s ∈ Icc (l : ℝ) (u : ℝ)) :
    (intervalLower m l u : ℝ) ≤ buchstab s ∧
      buchstab s ≤ (intervalUpper m l u : ℝ) := by
  obtain ⟨k, hk, hcell⟩ := query_cell m hm hl hlu hu hs
  have hb := AutomaticBuchstabCells.actual_cell_bounds m k hm hcell
  exact ⟨(show (intervalLower m l u : ℝ) ≤ (cellLower m k : ℝ) by
    exact_mod_cast lower_le_cell hk).trans hb.1,
    hb.2.trans (show (cellUpper m k : ℝ) ≤ (intervalUpper m l u : ℝ) by
      exact_mod_cast cell_le_upper hk)⟩

/-- The explicit automatic interval width. Every extremal coefficient
has an actual rational query witness, so finite maxima cannot introduce
unpaid cell oscillation. The function modulus is proved, not supplied. -/
theorem actual_interval_width (m : ℕ) (hm : 0 < m) {l u : ℚ}
    (hl : 2 ≤ l) (hlu : l ≤ u) (hu : u ≤ 8) :
    0 ≤ intervalUpper m l u - intervalLower m l u ∧
      intervalUpper m l u - intervalLower m l u ≤ (u - l) / 2 + 3000 / (m : ℚ) := by
  have hn := cells_nonempty m hm (by linarith only [hl]) hlu hu
  obtain ⟨i, hi, hei⟩ := lower_attained hn
  obtain ⟨j, hj, hej⟩ := upper_attained hn
  obtain ⟨x, hx, hxcell⟩ := cell_witness m hm hlu hi
  obtain ⟨y, hy, hycell⟩ := cell_witness m hm hlu hj
  have hxc : (x : ℝ) ∈ Icc (grid m i : ℝ) (grid m (i + 1) : ℝ) := by
    exact ⟨by exact_mod_cast hxcell.1, by exact_mod_cast hxcell.2⟩
  have hyc : (y : ℝ) ∈ Icc (grid m j : ℝ) (grid m (j + 1) : ℝ) := by
    exact ⟨by exact_mod_cast hycell.1, by exact_mod_cast hycell.2⟩
  have hbX := AutomaticBuchstabCells.actual_cell_bounds m i hm hxc
  have hbY := AutomaticBuchstabCells.actual_cell_bounds m j hm hyc
  have hwX := (actual_cell_width m i hm (by have hh := (mem_cells.mp hi).1; omega)).2
  have hwY := (actual_cell_width m j hm (by have hh := (mem_cells.mp hj).1; omega)).2
  have hwXR : (cellUpper m i : ℝ) - (cellLower m i : ℝ) ≤ 1500 / (m : ℝ) := by
    exact_mod_cast hwX
  have hwYR : (cellUpper m j : ℝ) - (cellLower m j : ℝ) ≤ 1500 / (m : ℝ) := by
    exact_mod_cast hwY
  have hxR : (l : ℝ) ≤ x ∧ (x : ℝ) ≤ u :=
    ⟨by exact_mod_cast hx.1, by exact_mod_cast hx.2⟩
  have hyR : (l : ℝ) ≤ y ∧ (y : ℝ) ≤ u :=
    ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hLip := U1011BuchstabTailLipschitz.abs_sub_le_half
    (hlR.trans hyR.1) (hlR.trans hxR.1)
  have hSpan : |(y : ℝ) - x| ≤ (u : ℝ) - l := by
    apply abs_le.mpr
    constructor <;> linarith only [hxR.1, hxR.2, hyR.1, hyR.2]
  have hOmega : buchstab (y : ℝ) - buchstab (x : ℝ) ≤ ((u : ℝ) - l) / 2 := by
    have hh := le_abs_self (buchstab (y : ℝ) - buchstab (x : ℝ))
    linarith only [hh, hLip, hSpan]
  have hNonneg := actual_interval_bounds m hm (by linarith only [hl]) hlu hu
    (s := (l : ℝ)) ⟨le_rfl, by exact_mod_cast hlu⟩
  have hR0 : (0 : ℝ) ≤ (intervalUpper m l u : ℝ) - (intervalLower m l u : ℝ) := by
    linarith only [hNonneg.1, hNonneg.2]
  have hR1 : (intervalUpper m l u : ℝ) - (intervalLower m l u : ℝ) ≤
      ((u : ℝ) - l) / 2 + 3000 / (m : ℝ) := by
    rw [← hei, ← hej]
    linarith only [hbX.2, hbY.1, hwXR, hwYR, hOmega]
  exact ⟨by exact_mod_cast hR0, by exact_mod_cast hR1⟩

end

end ImbalancedChen.P5Z.AutomaticBuchstabIntervals
