import ImbalancedChen.P1FifthWireGeometry

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Exact complete geometric cover for every saved grid400 fifth row on the
original 0..19/96 mesh with475 cells (step1/2400). Each saved1/400 interval
has exactly six aligned subintervals, possibly clipped by the ambient box.
Signed lower indices are arbitrary. No full finite family is enumerated,
and no parent/history/licence/gate/cap/gain is inferred from this cover.
-/

namespace ImbalancedChen.P1OriginalFifthGrid400FullBoxCover
noncomputable section
open Set
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation

abbrev MeshCell := Fin 5 → Fin (474 + 1)

theorem mesh475_qlo (j : MeshCell) (i : Fin 5) :
    qLogPrimeMeshLo 0 (19 / 96) 474 j i = ((j i).val : ℚ) / 2400 := by
  norm_num [qLogPrimeMeshLo, qLogPrimeMeshPoint, div_eq_mul_inv] <;> ring

theorem mesh475_qhi (j : MeshCell) (i : Fin 5) :
    qLogPrimeMeshHi 0 (19 / 96) 474 j i = (((j i).val : ℚ) + 1) / 2400 := by
  norm_num [qLogPrimeMeshHi, qLogPrimeMeshPoint, div_eq_mul_inv] <;> ring

theorem mesh475_lo (j : MeshCell) (i : Fin 5) :
    logPrimeMeshLo 0 (19 / 96) 474 j i = ((j i).val : ℝ) / 2400 := by
  norm_num [logPrimeMeshLo, logPrimeMeshPoint, logPrimeMeshStep, div_eq_mul_inv] <;> ring

theorem mesh475_hi (j : MeshCell) (i : Fin 5) :
    logPrimeMeshHi 0 (19 / 96) 474 j i = (((j i).val : ℝ) + 1) / 2400 := by
  norm_num [logPrimeMeshHi, logPrimeMeshPoint, logPrimeMeshStep, div_eq_mul_inv] <;> ring

/-- A mesh interval meeting a saved interval is contained in it, because
both saved endpoints are integer multiples of six mesh steps. The strict
upper endpoints are essential; arbitrary signed saved indices are allowed. -/
theorem aligned_grid400_interval (k : ℤ) (j : ℕ) (x : ℝ)
    (hrawlo : (k : ℝ) / 400 ≤ x) (hrawhi : x < ((k : ℝ) + 1) / 400)
    (hmeshlo : (j : ℝ) / 2400 ≤ x) (hmeshhi : x < ((j : ℝ) + 1) / 2400) :
    (k : ℚ) / 400 ≤ (j : ℚ) / 2400 ∧
      ((j : ℚ) + 1) / 2400 ≤ ((k : ℚ) + 1) / 400 := by
  have hloR : (6 : ℝ) * (k : ℝ) < (j : ℝ) + 1 := by linarith
  have hhiR : (j : ℝ) < (6 : ℝ) * ((k : ℝ) + 1) := by linarith
  have hloZ : (6 : ℤ) * k < (j : ℤ) + 1 := by exact_mod_cast hloR
  have hhiZ : (j : ℤ) < (6 : ℤ) * (k + 1) := by exact_mod_cast hhiR
  have hloInt : (6 : ℤ) * k ≤ (j : ℤ) := by omega
  have hhiInt : (j : ℤ) + 1 ≤ (6 : ℤ) * (k + 1) := by omega
  have hloQ : (6 : ℚ) * (k : ℚ) ≤ (j : ℚ) := by exact_mod_cast hloInt
  have hhiQ : (j : ℚ) + 1 ≤ (6 : ℚ) * ((k : ℚ) + 1) := by exact_mod_cast hhiInt
  constructor <;> linarith

/-- The unique ambient mesh owner of a saved-box point passes the exact
rational containment predicate used by the conservative decoder. -/
theorem owner_is_contained (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (t : Fin 5 → ℝ) (ht : t ∈ raw.originalBox) (j : MeshCell)
    (hj : t ∈ logPrimeMeshCell 0 (19 / 96) 474 j) :
    fifthCellContained raw 474 j := by
  intro i
  have hraw := ht i
  have hrawlo : (raw.lo i : ℝ) / 400 ≤ t i := by
    simpa [FifthWireRow.lower, hgrid] using hraw.1
  have hrawhi : t i < ((raw.lo i : ℝ) + 1) / 400 := by
    simpa [FifthWireRow.upper, hgrid] using hraw.2
  have hmesh := mem_logPrimeMeshCell.mp hj i
  rw [mesh475_lo, mesh475_hi] at hmesh
  have hcontained := aligned_grid400_interval (raw.lo i) (j i).val (t i)
    hrawlo hrawhi hmesh.1 hmesh.2
  simpa [FifthWireRow.lower, FifthWireRow.upper, hgrid, mesh475_qlo, mesh475_qhi]
    using hcontained

/-- COMPLETE cover of the authenticated row's entire half-open box after
ambient clipping. This is not a single representative subcell, and it
requires no nonnegative-endpoint assumption or numerical enumeration. -/
theorem originalBox_inter_ambient_eq_decode_union (raw : FifthWireRow)
    (hgrid : raw.grid = 400) (hmask : 0 ≤ raw.mask) :
    raw.originalBox ∩ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows raw 474, logPrimeMeshCell 0 (19 / 96) 474 r.cell := by
  ext t
  constructor
  · intro ht
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) 474 ht.2
    let r : FifthRow 474 := ⟨j, maskSlots 5 raw.mask.toNat⟩
    have hr : r ∈ decodeFifthRows raw 474 := by
      apply (mem_decodeFifthRows_iff raw 474 r).mpr
      refine ⟨?_, hmask, j, owner_is_contained raw hgrid t ht.1 j hj, rfl⟩
      rw [hgrid]
      norm_num
    exact mem_iUnion₂.mpr ⟨r, hr, hj⟩
  · intro ht
    obtain ⟨r, hr, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨(decodeFifthRows_source_geometry raw 474 r hr t ht).2.2.2,
      logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) 474 r.cell ht⟩

/-- The cover retains unique Ico ownership, including all saved and mesh
faces. Duplicate labels are not introduced by the mask annotation. -/
theorem unique_decoded_owner (raw : FifthWireRow) (hgrid : raw.grid = 400)
    (hmask : 0 ≤ raw.mask) (t : Fin 5 → ℝ)
    (ht : t ∈ raw.originalBox ∩
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    ∃! r : FifthRow 474, r ∈ decodeFifthRows raw 474 ∧
      t ∈ logPrimeMeshCell 0 (19 / 96) 474 r.cell := by
  have hmem : t ∈ ⋃ r ∈ decodeFifthRows raw 474, logPrimeMeshCell 0 (19 / 96) 474 r.cell := by
    rw [← originalBox_inter_ambient_eq_decode_union raw hgrid hmask]
    exact ht
  obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp hmem
  refine ⟨r, ⟨hr, htr⟩, ?_⟩
  intro s hs
  have hc : s.cell = r.cell :=
    logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hs.2 htr
  have hm : s.selected = r.selected :=
    (decodeFifthRows_selected_eq raw 474 s hs.1).trans
      (decodeFifthRows_selected_eq raw 474 r hr).symm
  cases s with
  | mk sc ss =>
    cases r with
    | mk rc rs =>
      cases hc
      cases hm
      rfl

/-- Finite-family coverage without enumerating any decoded cells. A
concrete full-table grid/mask field witness remains separate from this
mathematical theorem and is not claimed executed here. -/
theorem family_originalBox_inter_ambient_eq_decode_union (records : Finset FifthWireRow)
    (hgrid : ∀ raw ∈ records, raw.grid = 400)
    (hmask : ∀ raw ∈ records, 0 ≤ raw.mask) :
    (⋃ raw ∈ records, raw.originalBox) ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ raw ∈ records, ⋃ r ∈ decodeFifthRows raw 474,
        logPrimeMeshCell 0 (19 / 96) 474 r.cell := by
  ext t
  constructor
  · intro ht
    obtain ⟨raw, hraw, htRaw⟩ := mem_iUnion₂.mp ht.1
    have hpoint : t ∈ raw.originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := ⟨htRaw, ht.2⟩
    rw [originalBox_inter_ambient_eq_decode_union raw (hgrid raw hraw) (hmask raw hraw)] at hpoint
    exact mem_iUnion₂.mpr ⟨raw, hraw, hpoint⟩
  · intro ht
    obtain ⟨raw, hraw, htRaw⟩ := mem_iUnion₂.mp ht
    have hpoint : t ∈ raw.originalBox ∩
        logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) := by
      rw [originalBox_inter_ambient_eq_decode_union raw (hgrid raw hraw) (hmask raw hraw)]
      exact htRaw
    exact ⟨mem_iUnion₂.mpr ⟨raw, hraw, hpoint.1⟩, hpoint.2⟩
/-- The decoded row keeps the same variable selected endpoint M_I(t).
Coverage itself supplies no gateCheck or original-parent licence. -/
theorem decoded_candidate_mask (raw : FifthWireRow) (r : FifthRow 474)
    (hr : r ∈ decodeFifthRows raw 474) (e : ℝ) (t : Fin 5 → ℝ) :
    candidate e r.selected t =
      VariableEnvelope.v (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) - 2 * e := by
  rw [decodeFifthRows_selected_eq raw 474 r hr, candidate, envelope_eq_v]

end
end ImbalancedChen.P1OriginalFifthGrid400FullBoxCover