import ImbalancedChen.P5U7OriginalStraddlingCells

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
An explicit rational grid supplies a complete closed outer staircase and
disjoint open inner staircase of the literal original U7 triangle. The
mesh has no externally supplied coverage or disjointness premise.
-/

namespace ImbalancedChen.P5U7OriginalStaircaseGeometry

noncomputable section

open Set
open P5U7OriginalStraddlingCells
open scoped BigOperators
open Classical

def mesh (a b : ℚ) (m k : ℕ) : ℚ := a + (b - a) * k / m

theorem mesh_zero (a b : ℚ) (m : ℕ) : mesh a b m 0 = a := by simp [mesh]

theorem mesh_last (a b : ℚ) (m : ℕ) (hm : 0 < m) : mesh a b m m = b := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  unfold mesh
  field_simp [hm0]
  <;> ring

theorem mesh_mono (a b : ℚ) (hab : a ≤ b) (m : ℕ) (hm : 0 < m) :
    Monotone (mesh a b m) := by
  intro k l hkl
  have hklQ : (k : ℚ) ≤ l := by exact_mod_cast hkl
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  unfold mesh
  exact add_le_add_left (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hklQ (sub_nonneg.mpr hab)) hmQ.le) a

theorem mesh_bounds (a b : ℚ) (hab : a ≤ b) (m : ℕ) (hm : 0 < m)
    (k : ℕ) (hk : k ≤ m) : a ≤ mesh a b m k ∧ mesh a b m k ≤ b := by
  have hl := mesh_mono a b hab m hm (Nat.zero_le k)
  have hu := mesh_mono a b hab m hm hk
  rw [mesh_zero] at hl
  rw [mesh_last a b m hm] at hu
  exact ⟨hl, hu⟩

/-- Closed coverage includes the very last endpoint, assigned to m-1.
All other points use their actual floor index. -/
theorem mesh_closed_cover (a b : ℚ) (hab : a < b) (m : ℕ) (hm : 0 < m)
    {x : ℝ} (hx : x ∈ Icc (a : ℝ) b) :
    ∃ k : ℕ, k < m ∧ (mesh a b m k : ℝ) ≤ x ∧
      x ≤ (mesh a b m (k + 1) : ℝ) := by
  by_cases hxlast : x = (b : ℝ)
  · refine ⟨m - 1, by omega, ?_, ?_⟩
    · have h := (mesh_bounds a b hab.le m hm (m - 1) (by omega)).2
      rw [hxlast]
      exact_mod_cast h
    · rw [show m - 1 + 1 = m by omega, mesh_last a b m hm, hxlast]
  · have hxlt : x < (b : ℝ) := lt_of_le_of_ne hx.2 hxlast
    have hw : (0 : ℝ) < (b : ℝ) - a := by exact_mod_cast sub_pos.mpr hab
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    let z : ℝ := (x - (a : ℝ)) * m / ((b : ℝ) - a)
    have hz : 0 ≤ z := div_nonneg (mul_nonneg (sub_nonneg.mpr hx.1) hmR.le) hw.le
    have hzm : z < (m : ℝ) := by
      apply (div_lt_iff₀ hw).mpr
      nlinarith [mul_lt_mul_of_pos_right (sub_lt_sub_right hxlt (a : ℝ)) hmR]
    let k : ℕ := ⌊z⌋₊
    have hk : k < m := (Nat.floor_lt hz).mpr hzm
    have hl := (le_div_iff₀ hw).mp (Nat.floor_le hz : (k : ℝ) ≤ z)
    have hr := (lt_div_iff₀ hw).mp (Nat.lt_floor_add_one z : z < (k : ℝ) + 1)
    refine ⟨k, hk, ?_, ?_⟩
    · have hdiv : ((b : ℝ) - a) * k / (m : ℝ) ≤ x - (a : ℝ) := by
        apply (div_le_iff₀ hmR).mpr
        nlinarith only [hl]
      dsimp [mesh]
      push_cast
      linarith only [hdiv]
    · have hdiv : x - (a : ℝ) < ((b : ℝ) - a) * ((k : ℝ) + 1) / (m : ℝ) := by
        apply (lt_div_iff₀ hmR).mpr
        nlinarith only [hr]
      dsimp [mesh]
      push_cast
      linarith only [hdiv]

def tlo : ℚ := 59 / 250
def thi : ℚ := 1 / 3
def ulo : ℚ := 59 / 250
def uhi : ℚ := (1 - 59 / 250) / 2

abbrev Index (m : ℕ) := Fin m × Fin m

def cell (m : ℕ) (i : Index m) : Box :=
  ⟨mesh tlo thi m i.1, mesh tlo thi m (i.1.val + 1),
    mesh ulo uhi m i.2, mesh ulo uhi m (i.2.val + 1)⟩

def outer (m : ℕ) : Finset (Index m) := Finset.univ.filter fun i =>
  (cell m i).a ≤ (cell m i).d ∧ (cell m i).a + 2 * (cell m i).c ≤ 1

def inner (m : ℕ) : Finset (Index m) := Finset.univ.filter fun i =>
  (cell m i).b ≤ (cell m i).c ∧ (cell m i).b + 2 * (cell m i).d ≤ 1

theorem cell_valid (m : ℕ) (hm : 0 < m) (i : Index m) : (cell m i).Valid := by
  have ht := mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm i.1 i.1.isLt.le
  have ht' := mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm
    (i.1.val + 1) (by omega)
  have hu := mesh_bounds ulo uhi (by norm_num [ulo, uhi]) m hm i.2 i.2.isLt.le
  have htm := mesh_mono tlo thi (by norm_num [tlo, thi]) m hm (Nat.le_succ i.1.val)
  have hum := mesh_mono ulo uhi (by norm_num [ulo, uhi]) m hm (Nat.le_succ i.2.val)
  change 0 < mesh tlo thi m i.1 ∧ _ ∧ _ ∧ 0 < mesh ulo uhi m i.2 ∧ _
  exact ⟨(by norm_num [tlo] at ht; linarith only [ht.1]), htm,
    (by simpa only [thi] using ht'.2),
    (by norm_num [ulo] at hu; linarith only [hu.1]), hum⟩

/-- Every point of the CLOSED literal original triangle lies in one of
the explicitly generated outer staircase cells. -/
theorem original_triangle_outer_cover (m : ℕ) (hm : 0 < m)
    {p : ℝ × ℝ} (hp : p ∈ p5U7OmegaTriangle) :
    ∃ i ∈ outer m, p ∈ (cell m i).closed := by
  have hg := p5U7Omega_closed_geometry hp
  have ht : p.1 ∈ Icc (tlo : ℝ) thi := ⟨hp.1, hg.2.2.2.1⟩
  have hu : p.2 ∈ Icc (ulo : ℝ) uhi := by
    refine ⟨hp.1.trans hp.2.1, ?_⟩
    change p.2 ≤ ((1 - 59 / 250 : ℚ) / 2 : ℝ)
    push_cast
    linarith only [hp.1, hp.2.2]
  obtain ⟨k, hk, hkl, hkr⟩ := mesh_closed_cover tlo thi
    (by norm_num [tlo, thi]) m hm ht
  obtain ⟨j, hj, hjl, hjr⟩ := mesh_closed_cover ulo uhi
    (by norm_num [ulo, uhi]) m hm hu
  let i : Index m := (⟨k, hk⟩, ⟨j, hj⟩)
  have hc : p ∈ (cell m i).closed := ⟨⟨hkl, hkr⟩, ⟨hjl, hjr⟩⟩
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hc⟩
  have h1 : ((cell m i).a : ℝ) ≤ (cell m i).d :=
    hc.1.1.trans (hp.2.1.trans hc.2.2)
  have h2 : ((cell m i).a : ℝ) + 2 * (cell m i).c ≤ 1 := by
    linarith only [hc.1.1, hc.2.1, hp.2.2]
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem inner_cell_subset_triangle (m : ℕ) (hm : 0 < m)
    {i : Index m} (hi : i ∈ inner m) : (cell m i).closed ⊆ p5U7OmegaTriangle := by
  have hinner := (Finset.mem_filter.mp hi).2
  have horder : ((cell m i).b : ℝ) ≤ (cell m i).c := by exact_mod_cast hinner.1
  have hcap : ((cell m i).b : ℝ) + 2 * (cell m i).d ≤ 1 := by
    exact_mod_cast hinner.2
  have hlo := (mesh_bounds tlo thi (by norm_num [tlo, thi]) m hm i.1 i.1.isLt.le).1
  have hloR : (59 / 250 : ℝ) ≤ (cell m i).a := by exact_mod_cast hlo
  intro p hp
  refine ⟨hloR.trans hp.1.1, hp.1.2.trans (horder.trans hp.2.1), ?_⟩
  linarith only [hp.1.2, hp.2.2, hcap]

theorem opened_subset_closed (B : Box) : B.opened ⊆ B.closed := by
  intro p hp
  exact ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩

/-- Open cell interiors have exact finite ownership even on the two
triangular staircase boundaries. Grid-edge points are omitted only by
the inner approximation; each omitted edge has zero rectangular area. -/
theorem opened_cells_disjoint (m : ℕ) (hm : 0 < m) :
    Pairwise fun i j : Index m => Disjoint (cell m i).opened (cell m j).opened := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro p hpi hpj
  have hneq : i.1 ≠ j.1 ∨ i.2 ≠ j.2 := by
    by_contra h
    push_neg at h
    exact hij (Prod.ext h.1 h.2)
  rcases hneq with ht | hu
  · rcases lt_or_gt_of_ne ht with h | h
    · have hnat : i.1.val + 1 ≤ j.1.val := by
        have hlt : i.1.val < j.1.val := h
        omega
      have hg := mesh_mono tlo thi (by norm_num [tlo, thi]) m hm hnat
      have hgR : ((cell m i).b : ℝ) ≤ (cell m j).a := by exact_mod_cast hg
      exact (not_lt_of_ge (hpi.1.2.le.trans hgR)) hpj.1.1
    · have hnat : j.1.val + 1 ≤ i.1.val := by
        have hlt : j.1.val < i.1.val := h
        omega
      have hg := mesh_mono tlo thi (by norm_num [tlo, thi]) m hm hnat
      have hgR : ((cell m j).b : ℝ) ≤ (cell m i).a := by exact_mod_cast hg
      exact (not_lt_of_ge (hpj.1.2.le.trans hgR)) hpi.1.1
  · rcases lt_or_gt_of_ne hu with h | h
    · have hnat : i.2.val + 1 ≤ j.2.val := by
        have hlt : i.2.val < j.2.val := h
        omega
      have hg := mesh_mono ulo uhi (by norm_num [ulo, uhi]) m hm hnat
      have hgR : ((cell m i).d : ℝ) ≤ (cell m j).c := by exact_mod_cast hg
      exact (not_lt_of_ge (hpi.2.2.le.trans hgR)) hpj.2.1
    · have hnat : j.2.val + 1 ≤ i.2.val := by
        have hlt : j.2.val < i.2.val := h
        omega
      have hg := mesh_mono ulo uhi (by norm_num [ulo, uhi]) m hm hnat
      have hgR : ((cell m j).d : ℝ) ≤ (cell m i).c := by exact_mod_cast hg
      exact (not_lt_of_ge (hpj.2.2.le.trans hgR)) hpi.2.1

end

end ImbalancedChen.P5U7OriginalStaircaseGeometry
