import ImbalancedChen.P5ActualFifthGateStripVolume

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The canonical owner FILTER loss is localized relative to the SAME actual
unfiltered zero-buffer source domain. The original history-invalid part of
the clipped raw parent is separate. No complete raw box is presumed valid.
-/
namespace ImbalancedChen.P5CanonicalOwnerFilterStrips
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalCoarseFifthContinuation P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalFifthQuantitativeGateRefinement P1FifthUnitBoxGainDecomposition
open P1OriginalFifthAdoptedOwnerBank
open P1OriginalFifthCorrelatedRawBoxGates
open P5ActualFifthGateStripLocalization P5ActualFifthGateStripVolume

def unfilteredZeroDomain (raw : FifthWireRow) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  ownerUnion raw 0 chi (refinedMesh q) omega (decodedLabels raw q)

def canonicalFilterRejection (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  unfilteredZeroDomain raw q chi omega \ adoptedDomain raw e q chi omega 0

def canonicalInvalidHistory (raw : FifthWireRow) (q : ℕ) (chi omega : ℝ) : Set (Fin 5 → ℝ) :=
  fixedParent raw \ unfilteredZeroDomain raw q chi omega

theorem adoptedDomain_subset_unfiltered (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    adoptedDomain raw e q chi omega 0 ⊆ unfilteredZeroDomain raw q chi omega := by
  intro t ht
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht
  obtain ⟨r, hr, hrj⟩ := adoptedOwners_original_decoded raw e q chi omega j hj
  exact mem_iUnion₂.mpr ⟨j, Finset.mem_image.mpr ⟨r, hr, hrj⟩, htj⟩

theorem unfilteredZeroDomain_subset_parent (raw : FifthWireRow) (q : ℕ) (chi omega : ℝ) :
    unfilteredZeroDomain raw q chi omega ⊆ fixedParent raw := by
  intro t ht
  obtain ⟨_j, _hj, htj⟩ := mem_iUnion₂.mp ht
  exact ⟨htj.1, htj.2.2.1⟩

theorem canonical_omitted_exact_history_filter_partition (raw : FifthWireRow)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    omittedParent raw e q chi omega = canonicalInvalidHistory raw q chi omega ∪
      canonicalFilterRejection raw e q chi omega := by
  ext t
  constructor
  · intro ht
    by_cases hu : t ∈ unfilteredZeroDomain raw q chi omega
    · exact Or.inr ⟨hu, ht.2⟩
    · exact Or.inl ⟨ht.1, hu⟩
  · rintro (ht | ht)
    · exact ⟨ht.1, fun ha => ht.2 (adoptedDomain_subset_unfiltered raw e q chi omega ha)⟩
    · exact ⟨unfilteredZeroDomain_subset_parent raw q chi omega ht.1, ht.2⟩

theorem canonical_history_filter_disjoint (raw : FifthWireRow) (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    Disjoint (canonicalInvalidHistory raw q chi omega) (canonicalFilterRejection raw e q chi omega) :=
  Set.disjoint_left.mpr (fun _ hh hf => hh.2 hf.1)

/-- The three actual owner-filter walls: the first two order comparisons
and the fixed original rho-stop. Rough activation is paid by the positive
raw lower key below, rather than deleting an entire child projection. -/
def filterWall (k : Fin 3) : Affine5 :=
  if k = 0 then ⟨0, fun i => if i = 0 then 1 else if i = 1 then -1 else 0⟩
  else if k = 1 then ⟨0, fun i => if i = 1 then 1 else if i = 2 then -1 else 0⟩
  else ⟨19 / 96, fun i => if i = 0 then -1 else 0⟩

theorem filterWall_eval (t : Fin 5 → ℝ) :
    (filterWall 0).eval t = t 0 - t 1 ∧ (filterWall 1).eval t = t 1 - t 2 ∧
      (filterWall 2).eval t = 19 / 96 - t 0 := by
  constructor
  · norm_num [filterWall, Affine5.eval, Fin.sum_univ_succ] <;> ring
  · constructor <;> norm_num [filterWall, Affine5.eval, Fin.sum_univ_succ] <;> ring

def filterStrips (delta : ℝ) : Set (Fin 5 → ℝ) :=
  unitCube ∩ {t | ∃ k : Fin 3, |(filterWall k).eval t| ≤ delta}

/-- Direct actual endpoint proof: no raw-wide thirdOwnerKeyCheck or
desired selected verdict is supplied. -/
theorem decoder_label_adopted_of_point_margins (raw : FifthWireRow)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ) (hw : 0 ≤ omega)
    (j : Label5 (refinedMesh q)) (hj : j ∈ decodedLabels raw q)
    (t : Fin 5 → ℝ) (ht : t ∈ logPrimeMeshCell 0 (19 / 96) (refinedMesh q) j)
    (h01 : 2 * (meshStepQ (refinedMesh q) : ℝ) ≤ t 0 - t 1)
    (h12 : 2 * (meshStepQ (refinedMesh q) : ℝ) ≤ t 1 - t 2)
    (hstop : t 0 + (meshStepQ (refinedMesh q) : ℝ) ≤ 19 / 96 - 4 * (e : ℝ))
    (hrough : omega + (meshStepQ (refinedMesh q) : ℝ) ≤ t 2)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    j ∈ adoptedOwners raw e q chi omega := by
  let m := refinedMesh q
  let l := qLogPrimeMeshLo 0 (19 / 96) m j
  let u := qLogPrimeMeshHi 0 (19 / 96) m j
  have hlo (i : Fin 5) : (l i : ℝ) ≤ t i := by
    rw [show l i = qLogPrimeMeshLo 0 (19 / 96) m j i from rfl,
      congrFun (cast_qLogPrimeMeshLo 0 (19 / 96) m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).1
  have hu_eq (i : Fin 5) : u i = l i + meshStepQ m := by exact mesh_upper_eq_lower_add_step m j i
  have htupper (i : Fin 5) : t i ≤ (u i : ℝ) := by
    rw [show u i = qLogPrimeMeshHi 0 (19 / 96) m j i from rfl,
      congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) i]
    exact (mem_logPrimeMeshCell.mp ht i).2.le
  have hwide (i : Fin 5) : (u i : ℝ) = (l i : ℝ) + (meshStepQ m : ℝ) := by exact_mod_cast hu_eq i
  have hlu (i : Fin 5) : l i ≤ u i := by rw [hu_eq]; linarith [meshStepQ_pos m]
  have hthird (z : ℚ) (hz : z ≤ e) : historicalPrefixProject (by omega : 3 ≤ 5) j ∈ cells (z : ℝ) chi m := by
    apply (mem_cells (z : ℝ) chi m _).mpr
    have hwidth : (box m (historicalPrefixProject (by omega : 3 ≤ 5) j)).width = meshStepQ m := by
      change max 0 (max (u 0 - l 0) (max (u 1 - l 1) (u 2 - l 2))) = meshStepQ m
      have hs (i : Fin 5) : u i - l i = meshStepQ m := by rw [hu_eq]; ring
      rw [hs 0, hs 1, hs 2]
      simp only [max_self, max_eq_right (meshStepQ_pos m).le]
    refine ⟨⟨hlu 0, hlu 1, hlu 2⟩, ?_, ?_, ?_, ?_, ?_⟩
    · change 0 ≤ l 2
      have h : (0 : ℝ) ≤ (l 2 : ℝ) := by linarith [htupper 2, hwide 2]
      exact_mod_cast h
    · change u 2 ≤ l 1
      have h : (u 2 : ℝ) ≤ (l 1 : ℝ) := by linarith [hlo 2, htupper 1, hwide 1, hwide 2]
      exact_mod_cast h
    · change u 1 ≤ l 0
      have h : (u 1 : ℝ) ≤ (l 0 : ℝ) := by linarith [hlo 1, htupper 0, hwide 0, hwide 1]
      exact_mod_cast h
    · change (u 0 : ℝ) ≤ extendedFirstStop - 4 * (z : ℝ)
      have hzR : (z : ℝ) ≤ e := by exact_mod_cast hz
      norm_num [extendedFirstStop] at *
      linarith [hlo 0, hwide 0]
    · rw [hwidth, cast_meshStepQ]
      exact hstep
  have hselected (z : ℚ) (hz : z ≤ e) : j ∈ selectedFifthCells z chi m omega (decodedLabels raw q) := by
    apply (mem_selectedFifthCells z chi m omega (decodedLabels raw q) j).mpr
    refine ⟨hj, hthird z hz, ?_⟩
    change omega ≤ (l 2 : ℝ)
    linarith [htupper 2, hwide 2]
  have hfirst (z : ℚ) (hz : z ≤ e) :
      P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (z : ℝ) m j = true := by
    apply (P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck_iff (z : ℝ) m j).mpr
    rw [← congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m j) 0]
    change (u 0 : ℝ) ≤ extendedFirstStop - 4 * (z : ℝ)
    have hzR : (z : ℝ) ≤ e := by exact_mod_cast hz
    norm_num [extendedFirstStop] at *
    linarith [hlo 0, hwide 0]
  exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hselected 0 he, hselected e le_rfl⟩,
    hfirst 0 he, hfirst e le_rfl⟩

theorem canonicalFilterRejection_subset_three_actual_strips (raw : FifthWireRow)
    (hg : raw.grid = 400) (hpos : 1 ≤ raw.lo 2)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    canonicalFilterRejection raw e q chi omega ⊆
      filterStrips (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ)) := by
  intro t ht
  obtain ⟨j, hj, htj⟩ := mem_iUnion₂.mp ht.1
  have hmesh := htj.2.2.2.1
  have hparent := unfilteredZeroDomain_subset_parent raw q chi omega ht.1
  have hunit : t ∈ unitCube := by
    intro k _
    have hk := mem_logPrimeBox.mp hparent.2 k
    exact ⟨hk.1, by linarith [hk.2]⟩
  refine ⟨hunit, ?_⟩
  by_contra hn
  have hfar (k : Fin 3) : 4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ) < |(filterWall k).eval t| := by
    exact lt_of_not_ge (fun hk => hn ⟨k, hk⟩)
  have hanti := ((mem_jointRegion 0 chi (refinedMesh q) omega j t).mp htj.2.2.2.2).2.1
  have h01pos : 0 < t 0 - t 1 := sub_pos.mpr (hanti (by decide : (0 : Fin 5) < 1))
  have h12pos : 0 < t 1 - t 2 := sub_pos.mpr (hanti (by decide : (1 : Fin 5) < 2))
  have hstoppos : 0 < (19 / 96 : ℝ) - t 0 := sub_pos.mpr (mem_logPrimeBox.mp hparent.2 0).2
  have h0 := hfar 0
  have h1 := hfar 1
  have h2 := hfar 2
  rw [(filterWall_eval t).1, abs_of_pos h01pos] at h0
  rw [(filterWall_eval t).2.1, abs_of_pos h12pos] at h1
  rw [(filterWall_eval t).2.2, abs_of_pos hstoppos] at h2
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hhR : (0 : ℝ) < (meshStepQ (refinedMesh q) : ℝ) := by exact_mod_cast meshStepQ_pos (refinedMesh q)
  have hlast : (1 / 400 : ℝ) ≤ t 2 := by
    have hk : (1 : ℝ) ≤ (raw.lo 2 : ℝ) := by exact_mod_cast hpos
    have hl := (htj.1 2).1
    simp only [FifthWireRow.lower, hg] at hl
    norm_num at hl
    linarith
  have hjAdopt := decoder_label_adopted_of_point_margins raw e he q chi omega hw0 j hj t hmesh
    (by linarith) (by linarith) (by linarith)
    (by linarith) hstep
  exact ht.2 (mem_iUnion₂.mpr ⟨j, hjAdopt, htj⟩)

theorem filterStrips_volume (delta : ℝ) (hd : 0 ≤ delta) :
    volume (filterStrips delta) ≤ ENNReal.ofReal (12 * delta) := by
  have hrow (k : Fin 3) : volume (unitCube ∩ {t | |(filterWall k).eval t| ≤ delta}) ≤ ENNReal.ofReal (4 * delta) := by
    have hcoeff : ∃ j : Fin 5, (1 / 2 : ℝ) ≤ |((filterWall k).coefficient j : ℝ)| := by
      fin_cases k
      · exact ⟨0, by norm_num [filterWall]⟩
      · exact ⟨1, by norm_num [filterWall]⟩
      · exact ⟨0, by norm_num [filterWall]⟩
    obtain ⟨j, hj⟩ := hcoeff
    exact affine_half_gap_strip_volume _ j delta hd hj
  have heq : filterStrips delta = ⋃ k : Fin 3, unitCube ∩ {t | |(filterWall k).eval t| ≤ delta} := by
    ext t
    simp [filterStrips, and_exists]
  rw [heq]
  calc
    _ ≤ ∑ k : Fin 3, volume (unitCube ∩ {t | |(filterWall k).eval t| ≤ delta}) := measure_iUnion_fintype_le volume _
    _ ≤ ∑ _k : Fin 3, ENNReal.ofReal (4 * delta) := Finset.sum_le_sum (fun k _ => hrow k)
    _ = (3 : ℝ≥0∞) * ENNReal.ofReal (4 * delta) := by simp [nsmul_eq_mul]
    _ = ENNReal.ofReal ((3 : ℝ) * (4 * delta)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    _ = ENNReal.ofReal (12 * delta) := by congr 1; ring

theorem canonicalFilterRejection_volume (raw : FifthWireRow)
    (hg : raw.grid = 400) (hpos : 1 ≤ raw.lo 2)
    (e : ℚ) (he : 0 ≤ e) (q : ℕ) (chi omega : ℝ)
    (hw0 : 0 ≤ omega) (hw : omega ≤ 1 / 800)
    (hh : (meshStepQ (refinedMesh q) : ℝ) ≤ 1 / 800)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi) :
    volume (canonicalFilterRejection raw e q chi omega) ≤
      ENNReal.ofReal (12 * (4 * (e : ℝ) + 2 * (meshStepQ (refinedMesh q) : ℝ))) := by
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hhR : (0 : ℝ) < (meshStepQ (refinedMesh q) : ℝ) := by exact_mod_cast meshStepQ_pos (refinedMesh q)
  exact (measure_mono (canonicalFilterRejection_subset_three_actual_strips raw hg hpos e he q chi omega hw0 hw hh hstep)).trans
    (filterStrips_volume _ (by positivity))

end
end ImbalancedChen.P5CanonicalOwnerFilterStrips
