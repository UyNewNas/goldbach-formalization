import ImbalancedChen.LogPrimeBoxMesh
import ImbalancedChen.SelectedPrefixCompactCaps

/-!
# Rational meshes selecting all cells that meet a licensed compact set

The rational endpoints cast to the existing real half-open mesh exactly.
All cells meeting the compact set form a finite family, with unique Ico
ownership at every point of the set inside the ambient box. A common fine
mesh makes every such cell's rational cap check succeed. No certificate
coverage, mask choice or admissibility of a manuscript policy is assumed.
-/

namespace ImbalancedChen

noncomputable section

open Filter Set
open scoped Classical Topology

def qLogPrimeMeshPoint (a b : ℚ) (m i : ℕ) : ℚ :=
  a + (i : ℚ) * ((b - a) / (m + 1 : ℚ))

def qLogPrimeMeshLo {d : ℕ} (a b : ℚ) (m : ℕ)
    (j : Fin d → Fin (m + 1)) : Fin d → ℚ :=
  fun i => qLogPrimeMeshPoint a b m (j i).val

def qLogPrimeMeshHi {d : ℕ} (a b : ℚ) (m : ℕ)
    (j : Fin d → Fin (m + 1)) : Fin d → ℚ :=
  fun i => qLogPrimeMeshPoint a b m ((j i).val + 1)

@[simp] theorem cast_qLogPrimeMeshPoint (a b : ℚ) (m i : ℕ) :
    (qLogPrimeMeshPoint a b m i : ℝ) = logPrimeMeshPoint a b m i := by
  simp [qLogPrimeMeshPoint, logPrimeMeshPoint, logPrimeMeshStep]

theorem cast_qLogPrimeMeshLo {d : ℕ} (a b : ℚ) (m : ℕ)
    (j : Fin d → Fin (m + 1)) :
    (fun i => (qLogPrimeMeshLo a b m j i : ℝ)) = logPrimeMeshLo a b m j := by
  funext i
  exact cast_qLogPrimeMeshPoint a b m (j i).val

theorem cast_qLogPrimeMeshHi {d : ℕ} (a b : ℚ) (m : ℕ)
    (j : Fin d → Fin (m + 1)) :
    (fun i => (qLogPrimeMeshHi a b m j i : ℝ)) = logPrimeMeshHi a b m j := by
  funext i
  exact cast_qLogPrimeMeshPoint a b m ((j i).val + 1)

/-- Both endpoint vectors are within one mesh step of every point of the
cell. The nonnegative radius version of the Pi metric covers dimension zero. -/
theorem logPrimeMesh_endpoints_dist_le_step {d m : ℕ} {a b : ℝ} (hab : a ≤ b)
    {j : Fin d → Fin (m + 1)} {t : Fin d → ℝ}
    (ht : t ∈ logPrimeMeshCell a b m j) :
    dist (logPrimeMeshLo a b m j) t ≤ logPrimeMeshStep a b m ∧
      dist (logPrimeMeshHi a b m j) t ≤ logPrimeMeshStep a b m := by
  have hstep : 0 ≤ logPrimeMeshStep a b m :=
    div_nonneg (sub_nonneg.mpr hab) (by positivity)
  constructor
  · apply (dist_pi_le_iff hstep).mpr
    intro i
    obtain ⟨hlo, hhi⟩ := mem_logPrimeMeshCell.mp ht i
    have he := logPrimeMeshHi_eq_lo_add_step a b m j i
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · apply (dist_pi_le_iff hstep).mpr
    intro i
    obtain ⟨hlo, hhi⟩ := mem_logPrimeMeshCell.mp ht i
    have he := logPrimeMeshHi_eq_lo_add_step a b m j i
    rw [Real.dist_eq]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem logPrimeMeshCell_dist_le_step {d m : ℕ} {a b : ℝ} (hab : a ≤ b)
    {j : Fin d → Fin (m + 1)} {x t : Fin d → ℝ}
    (hx : x ∈ logPrimeMeshCell a b m j) (ht : t ∈ logPrimeMeshCell a b m j) :
    dist x t ≤ logPrimeMeshStep a b m := by
  have hstep : 0 ≤ logPrimeMeshStep a b m :=
    div_nonneg (sub_nonneg.mpr hab) (by positivity)
  apply (dist_pi_le_iff hstep).mpr
  intro i
  obtain ⟨hxl, hxh⟩ := mem_logPrimeMeshCell.mp hx i
  obtain ⟨htl, hth⟩ := mem_logPrimeMeshCell.mp ht i
  have he := logPrimeMeshHi_eq_lo_add_step a b m j i
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The finite mesh family is selected by actual intersection with `S`. -/
def selectedPrefixMeetingCells {d : ℕ} (a b : ℚ) (m : ℕ)
    (S : Set (Fin d → ℝ)) : Finset (Fin d → Fin (m + 1)) :=
  Finset.univ.filter (fun j => ∃ t ∈ S, t ∈ logPrimeMeshCell a b m j)

@[simp] theorem mem_selectedPrefixMeetingCells {d m : ℕ} {a b : ℚ}
    {S : Set (Fin d → ℝ)} {j : Fin d → Fin (m + 1)} :
    j ∈ selectedPrefixMeetingCells a b m S ↔
      ∃ t ∈ S, t ∈ logPrimeMeshCell a b m j := by
  simp [selectedPrefixMeetingCells]

/-- Every point of the set has exactly one selected cell, at every mesh
scale. The ambient upper endpoint remains excluded by the Ico convention. -/
theorem selectedPrefixMeetingCells_unique_cover {d : ℕ} (a b : ℚ) (hab : a ≤ b)
    (m : ℕ) (S : Set (Fin d → ℝ))
    (hbox : S ⊆ logPrimeBox (fun _ => (a : ℝ)) (fun _ => (b : ℝ)))
    {t : Fin d → ℝ} (ht : t ∈ S) :
    ∃! j : Fin d → Fin (m + 1),
      j ∈ selectedPrefixMeetingCells a b m S ∧ t ∈ logPrimeMeshCell a b m j := by
  obtain ⟨j, hj⟩ := exists_logPrimeMeshCell (a : ℝ) (b : ℝ) m (hbox ht)
  refine ⟨j, ⟨mem_selectedPrefixMeetingCells.mpr ⟨t, ht, hj⟩, hj⟩, ?_⟩
  intro k hk
  exact logPrimeMeshCell_unique (by exact_mod_cast hab) hk.2 hj

theorem selectedPrefixMeetingCells_pairwiseDisjoint {d : ℕ}
    (a b : ℚ) (hab : a ≤ b) (m : ℕ) (S : Set (Fin d → ℝ)) :
    (selectedPrefixMeetingCells a b m S : Set (Fin d → Fin (m + 1))).PairwiseDisjoint
      (logPrimeMeshCell (a : ℝ) (b : ℝ) m) := by
  intro j _ k _ hjk
  exact logPrimeMeshCell_pairwiseDisjoint (by exact_mod_cast hab) m
    (Set.mem_univ j) (Set.mem_univ k) hjk

/-- The selected union contains no point farther than one mesh step from
an actual witness in `S`; intersection alone does not assert cell containment. -/
theorem selectedPrefixMeetingCells_point_near {d m : ℕ} {a b : ℚ} (hab : a ≤ b)
    {S : Set (Fin d → ℝ)} {j : Fin d → Fin (m + 1)}
    (hj : j ∈ selectedPrefixMeetingCells a b m S) {x : Fin d → ℝ}
    (hx : x ∈ logPrimeMeshCell a b m j) :
    ∃ t ∈ S, dist x t ≤ logPrimeMeshStep a b m := by
  obtain ⟨t, ht, htj⟩ := mem_selectedPrefixMeetingCells.mp hj
  exact ⟨t, ht, logPrimeMeshCell_dist_le_step (by exact_mod_cast hab) hx htj⟩

/-- Endpoint witnesses for each selected cell, using the literal rational
endpoint definitions that the cap checker consumes. -/
theorem selectedPrefixMeetingCells_endpoints_near {d m : ℕ} {a b : ℚ} (hab : a ≤ b)
    {S : Set (Fin d → ℝ)} {j : Fin d → Fin (m + 1)}
    (hj : j ∈ selectedPrefixMeetingCells a b m S) :
    ∃ t ∈ S,
      dist (fun i => (qLogPrimeMeshLo a b m j i : ℝ)) t ≤ logPrimeMeshStep a b m ∧
      dist (fun i => (qLogPrimeMeshHi a b m j i : ℝ)) t ≤ logPrimeMeshStep a b m := by
  obtain ⟨t, ht, htj⟩ := mem_selectedPrefixMeetingCells.mp hj
  refine ⟨t, ht, ?_⟩
  rw [cast_qLogPrimeMeshLo, cast_qLogPrimeMeshHi]
  exact logPrimeMesh_endpoints_dist_le_step (by exact_mod_cast hab) htj

/-- All cells meeting the strictly licensed compact set pass the rational
cap check from one mesh threshold onward. The threshold precedes every
selected cell, and no coverage assumption is needed for this implication. -/
theorem exists_selectedPrefixMeetingCells_check_threshold {d : ℕ}
    (I : Finset (Fin d)) (old nu a b : ℚ) (hab : a ≤ b)
    (S : Set (Fin d → ℝ)) (hS : IsCompact S)
    (hlicense : ∀ t ∈ S, SelectedPrefixLicense I old nu t) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ j ∈ selectedPrefixMeetingCells a b m S,
      selectedBoxCapCheck I old nu (qLogPrimeMeshLo a b m j)
        (qLogPrimeMeshHi a b m j) = true := by
  obtain ⟨delta, hd, hcheck⟩ :=
    exists_selectedBoxCapCheck_uniform_radius I old nu S hS hlicense
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp
    ((tendsto_logPrimeMeshStep (a : ℝ) (b : ℝ)).eventually (gt_mem_nhds hd))
  refine ⟨m₀, ?_⟩
  intro m hm j hj
  obtain ⟨t, ht, hl, hu⟩ := selectedPrefixMeetingCells_endpoints_near hab hj
  exact hcheck t ht _ _ (hl.trans_lt (hm₀ m hm)) (hu.trans_lt (hm₀ m hm))

end

end ImbalancedChen
