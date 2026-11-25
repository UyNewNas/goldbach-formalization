import ImbalancedChen.P2FiniteMarkedGamma5SelectedAtlasStrips

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual finite positive-product family is also indexed by RootCode.
This intersection retains that exact code, rather than choosing only its
frozen lower endpoint. Its boundary uses the already fixed fullWalls.
One mesh works for every code and every allowed root loss before N.
-/
namespace ImbalancedChen.P2FiniteMarkedGamma5SelectedCellAtlasStrips
noncomputable section
open Finset Set Filter Topology
open scoped Classical BigOperators Topology
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430NativeQueryPaths
open Part5OriginalCausalSmoothAtlas Part5OriginalH430JointQueryEnclosure
open P2FiniteMarkedGamma5FixedNativeItinerary
open P2FiniteMarkedGamma5SelectedWallCatalogue
open P2FiniteMarkedGamma5SelectedNativeStrips
open P2FiniteMarkedGamma5SelectedRootStrips

variable {d : ℕ} (sh : Fin d → P2EnhancedLowerPhysicalTransition.StepShape)

/-- The root-code condition is on the original total level of sourceRoot.
It is independent of N and is not a comparison on the root prime itself. -/
def cellSelected (n : ℕ) (k : Root) (tau : ℝ) (labels : Fin d → ReadLabel)
    (c : RootCode n) : Set (Space sh) :=
  {x | x ∈ bandSelected sh n k tau labels ∧
    rootCode n (sourceRoot k tau (x (.inl ()))).physical.total = c}

/-- Selecting one original root code introduces no new wall family. -/
theorem changed_cell_selected_strip (n : ℕ) (k : Root) (tau : ℝ)
    (labels : Fin d → ReadLabel) (c : RootCode n) (x y : Space sh)
    (ht : 0≤tau) (ht' : tau≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (hchange : ¬ (x ∈ cellSelected sh n k tau labels c ↔
      y ∈ cellSelected sh n k tau labels c)) :
    ∃ r ∈ fullWalls sh n k labels, r.2 ≠ 0 ∧
      |r.1+r.2 x| ≤ ‖r.2‖*‖x-y‖ := by
  classical
  by_contra hall
  have hs : ∀ r ∈ fullWalls sh n k labels, agree (ev x) (ev y) r := by
    intro r hr
    by_contra h
    exact hall ⟨r,hr,proper_crossing r h⟩
  have hb : x ∈ bandSelected sh n k tau labels ↔
      y ∈ bandSelected sh n k tau labels := by
    by_contra h
    exact hall (changed_band_selected_strip sh n k tau labels x y ht ht' hn h)
  by_cases hx : x ∈ bandSelected sh n k tau labels
  · have hy := hb.mp hx
    have hc := rootCode_eq_of_agree sh n k tau x y labels ht ht' hx.1 hy.1
      (fun r hr => hs r (by
        simp only [fullWalls,List.mem_cons]
        exact Or.inr (Or.inr hr)))
    apply hchange
    change (x ∈ bandSelected sh n k tau labels ∧
      rootCode n (sourceRoot k tau (x (.inl ()))).physical.total = c) ↔
      (y ∈ bandSelected sh n k tau labels ∧
      rootCode n (sourceRoot k tau (y (.inl ()))).physical.total = c)
    exact and_congr hb (by rw [hc])
  · have hy : y ∉ bandSelected sh n k tau labels := mt hb.mpr hx
    exact hchange (by simp [cellSelected,hx,hy])

private theorem opposite {P : Plan} (D : Set (Space sh))
    (j : NativeSlot sh → Code P) (x : Space sh) (hm : mixed P D j) :
    ∃ y, Cube y ∧ atom P j y ≠ 0 ∧ ¬ (x ∈ D ↔ y ∈ D) := by
  by_cases hx : x ∈ D
  · obtain ⟨y,hy,hat,hn⟩ := hm.2
    exact ⟨y,hy,hat,fun h => hn (h.mp hx)⟩
  · obtain ⟨y,hy,hat,hin⟩ := hm.1
    exact ⟨y,hy,hat,fun h => hx (h.mpr hin)⟩

/-- The original mixed-atom argument is applied to the code intersection;
the witness is a strip at the current counted point x. -/
theorem mixed_at_point (n m : ℕ) (k : Root) (tau : ℝ)
    (labels : Fin d → ReadLabel) (c : RootCode n)
    (ht : 0≤tau) (ht' : tau≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (j : NativeSlot sh → Code (.mesh m)) (x : Space sh)
    (hat : atom (.mesh m) j x ≠ 0)
    (hm : mixed (.mesh m) (cellSelected sh n k tau labels c) j) :
    ∃ r ∈ fullWalls sh n k labels, r.2 ≠ 0 ∧
      |r.1+r.2 x| ≤ ‖r.2‖*(4*width m) := by
  obtain ⟨y,_,hy,H⟩ := opposite sh _ j x hm
  obtain ⟨r,hr,hnz,he⟩ :=
    changed_cell_selected_strip sh n k tau labels c x y ht ht' hn H
  refine ⟨r,hr,hnz,he.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))⟩
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by norm_num) (width_pos m).le)).2
  intro i
  change ‖x i-y i‖ ≤ _
  rw [Real.norm_eq_abs]
  exact (mesh_diameter m (j i)
    (fun hz => hat (Finset.prod_eq_zero (Finset.mem_univ i) hz))
    (fun hz => hy (Finset.prod_eq_zero (Finset.mem_univ i) hz))).le

theorem outer_at_point (n m : ℕ) (k : Root) (tau : ℝ)
    (labels : Fin d → ReadLabel) (c : RootCode n)
    (ht : 0≤tau) (ht' : tau≤1/12) (hn : 1/((n:ℝ)+1)≤11/384)
    (x : Space sh) (hCube : Cube x)
    (hout : x ∉ cellSelected sh n k tau labels c)
    (h : readout (.mesh m)
      (hit (.mesh m) (cellSelected sh n k tau labels c)) x ≠ 0) :
    ∃ r ∈ fullWalls sh n k labels, r.2 ≠ 0 ∧
      |r.1+r.2 x| ≤ ‖r.2‖*(4*width m) := by
  classical
  have hex : ∃ j, hit (.mesh m) (cellSelected sh n k tau labels c) j ∧
      atom (.mesh m) j x ≠ 0 := by
    by_contra hn'
    apply h
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hj
    · by_contra ha
      exact hn' ⟨j,hj,ha⟩
    · rfl
  obtain ⟨j,hj,hx⟩ := hex
  exact mixed_at_point sh n m k tau labels c ht ht' hn j x hx
    ⟨hj,x,hCube,hx,hout⟩

/-- The norm budget uses fullWalls only. In particular, the mesh is
chosen before c, tau, the point and the arithmetic target. -/
theorem fine_outer_strip (n : ℕ) (k : Root) (labels : Fin d → ReadLabel)
    {delta : ℝ} (hd : 0<delta) (hn : 1/((n:ℝ)+1)≤11/384) :
    ∃ m : ℕ, ∀ tau : ℝ, 0≤tau → tau≤1/12 → ∀ c : RootCode n,
      ∀ x : Space sh, Cube x → x ∉ cellSelected sh n k tau labels c →
      readout (.mesh m) (hit (.mesh m) (cellSelected sh n k tau labels c)) x ≠ 0 →
      ∃ r ∈ fullWalls sh n k labels, r.2 ≠ 0 ∧ |r.1+r.2 x| ≤ delta := by
  classical
  let S := (fullWalls sh n k labels).toFinset
  let B : ℝ := 1+∑ r ∈ S, ‖r.2‖
  have hsum : 0 ≤ ∑ r ∈ S, ‖r.2‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hB : 0<B := by dsimp [B]; linarith
  obtain ⟨m,hm⟩ := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually
    (gt_mem_nhds (by positivity : 0<delta/(4*B)))).exists
  change width m < delta/(4*B) at hm
  refine ⟨m,?_⟩
  intro tau ht ht' c x hCube hout hne
  obtain ⟨r,hr,hnz,H⟩ :=
    outer_at_point sh n m k tau labels c ht ht' hn x hCube hout hne
  have hr' : r ∈ S := List.mem_toFinset.mpr hr
  have hnorm : ‖r.2‖≤B := by
    have hh := Finset.single_le_sum (f:=fun q : Form (Space sh) => ‖q.2‖)
      (fun q _ => norm_nonneg _) hr'
    dsimp [B]
    linarith
  refine ⟨r,hr,hnz,H.trans ?_⟩
  calc
    ‖r.2‖*(4*width m) ≤ B*(4*width m) :=
      mul_le_mul_of_nonneg_right hnorm (mul_nonneg (by norm_num) (width_pos m).le)
    _ ≤ delta := by
      nlinarith [(lt_div_iff₀ (by positivity : 0<4*B)).mp hm]

end
end ImbalancedChen.P2FiniteMarkedGamma5SelectedCellAtlasStrips
