import ImbalancedChen.P1OriginalFifthGrid400FullBoxCover

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Complete grid400 box coverage at every positive refinement q, with
m=475*q-1 and step1/(2400*q). Each saved interval has6*q aligned mesh
intervals before ambient clipping. Arbitrarily small positive omega is
compatible with this COMPLETE cover. No enormous decoded family is
executed, and original history/licence/gate/cap witnesses remain separate.
-/

namespace ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover
noncomputable section
open Set
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation

def refinedMesh (q : ℕ) : ℕ := 475 * q - 1
abbrev RefinedCell (q : ℕ) := Fin 5 → Fin (refinedMesh q + 1)

theorem refinedMesh_size (q : ℕ) (hq : 0 < q) : refinedMesh q + 1 = 475 * q := by
  unfold refinedMesh
  omega

theorem refined_step (q : ℕ) (hq : 0 < q) :
    logPrimeMeshStep 0 (19 / 96) (refinedMesh q) = 1 / ((2400 : ℝ) * (q : ℝ)) := by
  have hs : (refinedMesh q : ℝ) + 1 = (475 : ℝ) * (q : ℝ) := by
    exact_mod_cast refinedMesh_size q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold logPrimeMeshStep
  rw [hs]
  field_simp [ne_of_gt hqR] <;> ring

theorem refined_qlo (q : ℕ) (hq : 0 < q) (j : RefinedCell q) (i : Fin 5) :
    qLogPrimeMeshLo 0 (19 / 96) (refinedMesh q) j i =
      ((j i).val : ℚ) / ((2400 : ℚ) * (q : ℚ)) := by
  have hs : (refinedMesh q : ℚ) + 1 = (475 : ℚ) * (q : ℚ) := by
    exact_mod_cast refinedMesh_size q hq
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  unfold qLogPrimeMeshLo qLogPrimeMeshPoint
  rw [hs]
  field_simp [ne_of_gt hqQ] <;> ring

theorem refined_qhi (q : ℕ) (hq : 0 < q) (j : RefinedCell q) (i : Fin 5) :
    qLogPrimeMeshHi 0 (19 / 96) (refinedMesh q) j i =
      (((j i).val : ℚ) + 1) / ((2400 : ℚ) * (q : ℚ)) := by
  have hs : (refinedMesh q : ℚ) + 1 = (475 : ℚ) * (q : ℚ) := by
    exact_mod_cast refinedMesh_size q hq
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  unfold qLogPrimeMeshHi qLogPrimeMeshPoint
  rw [hs]
  push_cast
  field_simp [ne_of_gt hqQ] <;> ring

theorem refined_lo (q : ℕ) (hq : 0 < q) (j : RefinedCell q) (i : Fin 5) :
    logPrimeMeshLo 0 (19 / 96) (refinedMesh q) j i =
      ((j i).val : ℝ) / ((2400 : ℝ) * (q : ℝ)) := by
  unfold logPrimeMeshLo logPrimeMeshPoint
  rw [refined_step q hq] <;> ring

theorem refined_hi (q : ℕ) (hq : 0 < q) (j : RefinedCell q) (i : Fin 5) :
    logPrimeMeshHi 0 (19 / 96) (refinedMesh q) j i =
      (((j i).val : ℝ) + 1) / ((2400 : ℝ) * (q : ℝ)) := by
  unfold logPrimeMeshHi logPrimeMeshPoint
  rw [refined_step q hq]
  push_cast
  ring

/-- Integer endpoint alignment preserves the whole saved interval at
any positive refinement. No sign condition on the saved index is needed. -/
theorem aligned_refined_grid400_interval (q : ℕ) (hq : 0 < q)
    (k : ℤ) (j : ℕ) (x : ℝ)
    (hrawlo : (k : ℝ) / 400 ≤ x) (hrawhi : x < ((k : ℝ) + 1) / 400)
    (hmeshlo : (j : ℝ) / ((2400 : ℝ) * (q : ℝ)) ≤ x)
    (hmeshhi : x < ((j : ℝ) + 1) / ((2400 : ℝ) * (q : ℝ))) :
    (k : ℚ) / 400 ≤ (j : ℚ) / ((2400 : ℚ) * (q : ℚ)) ∧
      ((j : ℚ) + 1) / ((2400 : ℚ) * (q : ℚ)) ≤ ((k : ℚ) + 1) / 400 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (0 : ℝ) < (2400 : ℝ) * (q : ℝ) := by positivity
  have hrawlo' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 400)).mp hrawlo
  have hrawhi' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 400)).mp hrawhi
  have hloScaled : (6 : ℝ) * (q : ℝ) * (k : ℝ) ≤ x * ((2400 : ℝ) * (q : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hrawlo' (by positivity : (0 : ℝ) ≤ 6 * (q : ℝ))
    nlinarith
  have hhiScaled : x * ((2400 : ℝ) * (q : ℝ)) < (6 : ℝ) * (q : ℝ) * ((k : ℝ) + 1) := by
    have hh := mul_lt_mul_of_pos_left hrawhi' (by positivity : (0 : ℝ) < 6 * (q : ℝ))
    nlinarith
  have hloR : (6 : ℝ) * (q : ℝ) * (k : ℝ) < (j : ℝ) + 1 :=
    hloScaled.trans_lt ((lt_div_iff₀ hdR).mp hmeshhi)
  have hhiR : (j : ℝ) < (6 : ℝ) * (q : ℝ) * ((k : ℝ) + 1) :=
    ((div_le_iff₀ hdR).mp hmeshlo).trans_lt hhiScaled
  have hloZ : (6 : ℤ) * (q : ℤ) * k < (j : ℤ) + 1 := by exact_mod_cast hloR
  have hhiZ : (j : ℤ) < (6 : ℤ) * (q : ℤ) * (k + 1) := by exact_mod_cast hhiR
  have hloInt : (6 : ℤ) * (q : ℤ) * k ≤ (j : ℤ) := by omega
  have hhiInt : (j : ℤ) + 1 ≤ (6 : ℤ) * (q : ℤ) * (k + 1) := by omega
  have hloQ : (6 : ℚ) * (q : ℚ) * (k : ℚ) ≤ (j : ℚ) := by exact_mod_cast hloInt
  have hhiQ : (j : ℚ) + 1 ≤ (6 : ℚ) * (q : ℚ) * ((k : ℚ) + 1) := by exact_mod_cast hhiInt
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hdQ : (0 : ℚ) < (2400 : ℚ) * (q : ℚ) := by positivity
  constructor
  · apply (le_div_iff₀ hdQ).mpr
    nlinarith
  · apply (div_le_iff₀ hdQ).mpr
    nlinarith

/-- The actual ambient Ico owner is accepted by the lawful conservative
decoder, at every positive q. -/
theorem refined_owner_is_contained (q : ℕ) (hq : 0 < q)
    (raw : FifthWireRow) (hgrid : raw.grid = 400) (t : Fin 5 → ℝ)
    (ht : t ∈ raw.originalBox) (j : RefinedCell q)
    (hj : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j) :
    fifthCellContained raw (refinedMesh q) j := by
  intro i
  have hraw := ht i
  have hrawlo : (raw.lo i : ℝ) / 400 ≤ t i := by
    simpa [FifthWireRow.lower, hgrid] using hraw.1
  have hrawhi : t i < ((raw.lo i : ℝ) + 1) / 400 := by
    simpa [FifthWireRow.upper, hgrid] using hraw.2
  have hmesh := mem_logPrimeMeshCell.mp hj i
  rw [refined_lo q hq, refined_hi q hq] at hmesh
  have hs := aligned_refined_grid400_interval q hq (raw.lo i) (j i).val (t i)
    hrawlo hrawhi hmesh.1 hmesh.2
  simpa [FifthWireRow.lower, FifthWireRow.upper, hgrid, refined_qlo q hq, refined_qhi q hq]
    using hs

/-- COMPLETE saved-box cover at arbitrary positive refinement, including
all Ico faces and arbitrary signed lo values after ambient clipping. -/
theorem refined_originalBox_inter_ambient_eq_decode_union (q : ℕ) (hq : 0 < q)
    (raw : FifthWireRow) (hgrid : raw.grid = 400) (hmask : 0 ≤ raw.mask) :
    raw.originalBox ∩ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
      ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
        logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell := by
  ext t
  constructor
  · intro ht
    obtain ⟨j, hj⟩ := exists_logPrimeMeshCell 0 (19 / 96) (refinedMesh q) ht.2
    let r : FifthRow (refinedMesh q) := ⟨j, maskSlots 5 raw.mask.toNat⟩
    have hr : r ∈ decodeFifthRows raw (refinedMesh q) := by
      apply (mem_decodeFifthRows_iff raw (refinedMesh q) r).mpr
      refine ⟨?_, hmask, j, refined_owner_is_contained q hq raw hgrid t ht.1 j hj, rfl⟩
      rw [hgrid]
      norm_num
    exact mem_iUnion₂.mpr ⟨r, hr, hj⟩
  · intro ht
    obtain ⟨r, hr, ht⟩ := mem_iUnion₂.mp ht
    exact ⟨(decodeFifthRows_source_geometry raw (refinedMesh q) r hr t ht).2.2.2,
      logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19 / 96) (refinedMesh q) r.cell ht⟩

/-- Refinement never creates ambiguous Ico ownership. -/
theorem refined_unique_decoded_owner (q : ℕ) (hq : 0 < q)
    (raw : FifthWireRow) (hgrid : raw.grid = 400) (hmask : 0 ≤ raw.mask)
    (t : Fin 5 → ℝ) (ht : t ∈ raw.originalBox ∩
      logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ))) :
    ∃! r : FifthRow (refinedMesh q), r ∈ decodeFifthRows raw (refinedMesh q) ∧
      t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell := by
  have hmem : t ∈ ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
      logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell := by
    rw [← refined_originalBox_inter_ambient_eq_decode_union q hq raw hgrid hmask]
    exact ht
  obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp hmem
  refine ⟨r, ⟨hr, htr⟩, ?_⟩
  intro s hs
  have hc : s.cell = r.cell :=
    logPrimeMeshCell_unique (by norm_num : (0 : ℝ) ≤ 19 / 96) hs.2 htr
  have hm : s.selected = r.selected :=
    (decodeFifthRows_selected_eq raw _ s hs.1).trans (decodeFifthRows_selected_eq raw _ r hr).symm
  cases s with
  | mk sc ss =>
    cases r with
    | mk rc rs =>
      cases hc
      cases hm
      rfl

/-- The original source permits arbitrarily small positive omega; a
sufficient refinement supplies its required meshstep<=omega/2 primitive. -/
theorem exists_refinement_step_le_half (omega : ℝ) (homega : 0 < omega) :
    ∃ q : ℕ, 0 < q ∧ logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 := by
  obtain ⟨q, hq⟩ := exists_nat_gt (max (1 : ℝ) (2 / ((2400 : ℝ) * omega)))
  have hqOne : (1 : ℝ) < q := (le_max_left _ _).trans_lt hq
  have hqR : (0 : ℝ) < q := by linarith
  have hqNat : 0 < q := by exact_mod_cast hqR
  have hbound : 2 / ((2400 : ℝ) * omega) < q := (le_max_right _ _).trans_lt hq
  have hmul : (2 : ℝ) < (q : ℝ) * ((2400 : ℝ) * omega) :=
    (div_lt_iff₀ (by positivity : (0 : ℝ) < 2400 * omega)).mp hbound
  refine ⟨q, hqNat, ?_⟩
  rw [refined_step q hqNat]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2400 * (q : ℝ))).mpr
  nlinarith

/-- One refinement simultaneously meets the actual small-omega mesh
condition and covers EVERY saved grid400 row, with unchanged mask slots. -/
theorem exists_small_step_complete_cover (omega : ℝ) (homega : 0 < omega) :
    ∃ q : ℕ, 0 < q ∧ logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ omega / 2 ∧
      ∀ raw : FifthWireRow, raw.grid = 400 → 0 ≤ raw.mask →
        raw.originalBox ∩ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19 / 96 : ℝ)) =
          ⋃ r ∈ decodeFifthRows raw (refinedMesh q),
            logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell := by
  obtain ⟨q, hq, hs⟩ := exists_refinement_step_le_half omega homega
  exact ⟨q, hq, hs, fun raw hgrid hmask =>
    refined_originalBox_inter_ambient_eq_decode_union q hq raw hgrid hmask⟩

theorem refined_decoded_candidate_mask (q : ℕ) (raw : FifthWireRow)
    (r : FifthRow (refinedMesh q)) (hr : r ∈ decodeFifthRows raw (refinedMesh q))
    (e : ℝ) (t : Fin 5 → ℝ) :
    candidate e r.selected t =
      VariableEnvelope.v (∑ i ∈ maskSlots 5 raw.mask.toNat, t i) - 2 * e := by
  rw [decodeFifthRows_selected_eq raw _ r hr, candidate, envelope_eq_v]

end
end ImbalancedChen.P1OriginalFifthGrid400RefinedFullBoxCover