import ImbalancedChen.P5HistoricalActualThirdHistoryTransport
import ImbalancedChen.P5ActualFifthGateStripVolume

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The additional history rejection caused by the actual coarse third rule
has weighted full-archive cost at most 198 * sourceMassSum * chi. The
independent IDEAL source failure (order or nonpositive original six-branch
third gap) remains explicit; it is not assumed null or called a strip.
The eleven analytic affine pieces below are formulas, not archive data.
-/
namespace ImbalancedChen.P5HistoricalThirdTransportStripPayment
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalPrefixRowDecodeSoundness P1OriginalVariableFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover P1OriginalFifthAdoptedOwnerBank
open P1OriginalFifthCorrelatedRawBoxGates P1OriginalFifthLiteralKernelModulus
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthIndexedBankError
open P1HistoricalFifthTypedBaseGeometry P5HistoricalIndexedTrimGeometry
open P5CanonicalOwnerFilterStrips P5HistoricalCanonicalFilterReserve
open P5ActualFifthGateStripLocalization P5ActualFifthGateStripVolume
open P5HistoricalRejectedCoreReserve P5HistoricalActualThirdHistoryTransport

def thirdCube (t : Fin 5 → ℝ) : ℝ := t 0 + t 1 + 3 * t 2

/-- Original five tent branches (two planes each) and the one W plane,
each minus the actual inherited third cube. Their first coefficient never
vanishes, so none of these rows is an identity or an open inherit region. -/
def historyGapPlane : Fin 11 → Affine5 :=
  ![⟨1 / 2, ![-1 / 2, -1, -3, 0, 0]⟩,
    ⟨57 / 64, ![-5 / 2, -1, -3, 0, 0]⟩,
    ⟨1 / 2, ![-1 / 2, -1 / 2, -3, 0, 0]⟩,
    ⟨57 / 64, ![-5 / 2, -5 / 2, -3, 0, 0]⟩,
    ⟨1 / 2, ![-1 / 2, -1 / 2, -5 / 2, 0, 0]⟩,
    ⟨57 / 64, ![-5 / 2, -5 / 2, -9 / 2, 0, 0]⟩,
    ⟨153 / 256, ![-1, -1, -27 / 8, 0, 0]⟩,
    ⟨1 / 2, ![-1 / 2, -1, -5 / 2, 0, 0]⟩,
    ⟨57 / 64, ![-5 / 2, -1, -9 / 2, 0, 0]⟩,
    ⟨1 / 2, ![-1, -1 / 2, -5 / 2, 0, 0]⟩,
    ⟨57 / 64, ![-1, -5 / 2, -9 / 2, 0, 0]⟩]

theorem historyGapPlane_eval (k : Fin 11) (t : Fin 5 → ℝ) :
    (historyGapPlane k).eval t =
      ![A (t 0) - thirdCube t, C (t 0) - thirdCube t,
        A (t 0 + t 1) - thirdCube t, C (t 0 + t 1) - thirdCube t,
        A (t 0 + t 1 + t 2) - thirdCube t,
        C (t 0 + t 1 + t 2) - thirdCube t, B (t 2) - thirdCube t,
        A (t 0 + t 2) - thirdCube t, C (t 0 + t 2) - thirdCube t,
        A (t 1 + t 2) - thirdCube t, C (t 1 + t 2) - thirdCube t] k := by
  fin_cases k <;>
    norm_num [historyGapPlane, Affine5.eval, Fin.sum_univ_succ,
      A, C, B, cap, thirdCube] <;> ring

theorem historyGapPlane_half_coordinate (k : Fin 11) :
    (1 / 2 : ℝ) ≤ |((historyGapPlane k).coefficient 0 : ℝ)| := by
  fin_cases k <;> norm_num [historyGapPlane]

private theorem max_mem_range {f : Fin 11 → ℝ} {a b : ℝ}
    (ha : a ∈ Set.range f) (hb : b ∈ Set.range f) : max a b ∈ Set.range f := by
  by_cases h : a ≤ b
  · simpa only [max_eq_right h] using hb
  · simpa only [max_eq_left (le_of_not_ge h)] using ha

private theorem min_mem_range {f : Fin 11 → ℝ} {a b : ℝ}
    (ha : a ∈ Set.range f) (hb : b ∈ Set.range f) : min a b ∈ Set.range f := by
  by_cases h : a ≤ b
  · simpa only [min_eq_left h] using ha
  · simpa only [min_eq_right (le_of_not_ge h)] using hb

/-- A maximizing branch followed by a minimizing tent plane yields an
actual affine row, including every tie. No unique winner is required. -/
theorem six_gap_is_actual_plane (t : Fin 5 → ℝ) :
    ∃ k : Fin 11, (historyGapPlane k).eval t =
      six (t 0) (t 1) (t 2) - thirdCube t := by
  let f : Fin 11 → ℝ := fun k => (historyGapPlane k).eval t
  have hm : max (min (f 0) (f 1))
      (max (min (f 2) (f 3)) (max (min (f 4) (f 5))
        (max (f 6) (max (min (f 7) (f 8)) (min (f 9) (f 10)))))) ∈ Set.range f :=
    max_mem_range (min_mem_range ⟨0, rfl⟩ ⟨1, rfl⟩)
      (max_mem_range (min_mem_range ⟨2, rfl⟩ ⟨3, rfl⟩)
        (max_mem_range (min_mem_range ⟨4, rfl⟩ ⟨5, rfl⟩)
          (max_mem_range ⟨6, rfl⟩
            (max_mem_range (min_mem_range ⟨7, rfl⟩ ⟨8, rfl⟩)
              (min_mem_range ⟨9, rfl⟩ ⟨10, rfl⟩)))))
  have heq : max (min (f 0) (f 1))
      (max (min (f 2) (f 3)) (max (min (f 4) (f 5))
        (max (f 6) (max (min (f 7) (f 8)) (min (f 9) (f 10)))))) =
      six (t 0) (t 1) (t 2) - thirdCube t := by
    simp only [f, historyGapPlane_eval, Matrix.cons_val_zero, Matrix.cons_val_succ]
    simp only [six, v_eq_min, min_sub_sub_right, max_sub_sub_right]
  rw [heq] at hm
  exact hm

def historyStrips (delta : ℝ) : Set (Fin 5 → ℝ) :=
  unitCube ∩ {t | ∃ k : Fin 11, |(historyGapPlane k).eval t| ≤ delta}

theorem historyStrips_volume (delta : ℝ) (hd : 0 ≤ delta) :
    volume (historyStrips delta) ≤ ENNReal.ofReal (44 * delta) := by
  have hrow (k : Fin 11) :
      volume (unitCube ∩ {t | |(historyGapPlane k).eval t| ≤ delta}) ≤
        ENNReal.ofReal (4 * delta) :=
    affine_half_gap_strip_volume _ 0 delta hd (historyGapPlane_half_coordinate k)
  have heq : historyStrips delta = ⋃ k : Fin 11,
      unitCube ∩ {t | |(historyGapPlane k).eval t| ≤ delta} := by
    ext t
    simp [historyStrips, and_exists]
  rw [heq]
  calc
    _ ≤ ∑ k : Fin 11,
        volume (unitCube ∩ {t | |(historyGapPlane k).eval t| ≤ delta}) :=
      measure_iUnion_fintype_le volume _
    _ ≤ ∑ _k : Fin 11, ENNReal.ofReal (4 * delta) :=
      Finset.sum_le_sum (fun k _ => hrow k)
    _ = (11 : ℝ≥0∞) * ENNReal.ofReal (4 * delta) := by simp [nsmul_eq_mul]
    _ = ENNReal.ofReal ((11 : ℝ) * (4 * delta)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 11)]
      norm_num
    _ = ENNReal.ofReal (44 * delta) := by congr 1; ring

/-- Independently fixed source failure. It has no mesh, rough cutoff,
buffer, currentExponent or desired integral estimate in its definition. -/
def idealHistoryInvalid (i : ArchiveIndex) : Set (Fin 5 → ℝ) :=
  fixedParent (archiveRow i) ∩
    {t | ¬StrictAnti t ∨ six (t 0) (t 1) (t 2) ≤ thirdCube t}

def idealHistoryCost (i : ArchiveIndex) : ℝ :=
  rowMassBound (archiveRow i) * (volume (idealHistoryInvalid i)).toReal

def idealHistoryBankCost : ℝ := ∑ i ∈ licensedIndices, idealHistoryCost i

def historyTransportRejected (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ) :
    Set (Fin 5 → ℝ) :=
  canonicalInvalidHistory (archiveRow i) q chi omega \ idealHistoryInvalid i

def historyTransportCost (i : ArchiveIndex) (q : ℕ) (chi omega : ℝ) : ℝ :=
  rowMassBound (archiveRow i) * (volume (historyTransportRejected i q chi omega)).toReal

def historyTransportBankCost (q : ℕ) (chi omega : ℝ) : ℝ :=
  ∑ i ∈ licensedIndices, historyTransportCost i q chi omega

theorem fixedParent_subset_unit (i : ArchiveIndex) :
    fixedParent (archiveRow i) ⊆ unitCube := by
  intro t ht k _
  have hk := mem_logPrimeBox.mp ht.2 k
  exact ⟨hk.1, by linarith [hk.2]⟩

/-- Genuine coarse-history rejection outside the independently fixed
ideal failure is contained in eleven PROPER affine strips. Complete
decoder coverage is used before choosing the same owner as in I. -/
theorem canonicalHistory_subset_ideal_union_strips
    (i : ArchiveIndex) (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256) :
    canonicalInvalidHistory (archiveRow i) q chi omega ⊆
      idealHistoryInvalid i ∪ historyStrips ((9 / 2 : ℝ) * chi) := by
  intro t ht
  by_cases hi : t ∈ idealHistoryInvalid i
  · exact Or.inl hi
  · have hp : t ∈ fixedParent (archiveRow i) := ht.1
    have hgood : StrictAnti t ∧ thirdCube t < six (t 0) (t 1) (t 2) := by
      have hn : ¬(¬StrictAnti t ∨ six (t 0) (t 1) (t 2) ≤ thirdCube t) :=
        fun hf => hi ⟨hp, hf⟩
      simpa only [not_or, not_not, not_le] using hn
    have hcover := refined_originalBox_inter_ambient_eq_decode_union q hq
      (archiveRow i) (archiveRow_grid i) (archiveRow_mask_nonnegative i)
    have htcover : t ∈ ⋃ r ∈ decodeFifthRows (archiveRow i) (refinedMesh q),
        logPrimeMeshCell 0 (19 / 96) (refinedMesh q) r.cell := by
      rw [← hcover]
      exact hp
    obtain ⟨r, hr, htr⟩ := mem_iUnion₂.mp htcover
    have hfail := (mem_canonicalInvalidHistory_iff_order_or_third
      i q chi omega r hr t htr).mp ht
    have hthird : currentExponent 0 chi (refinedMesh q) omega r.cell t ≤ thirdCube t := by
      rcases hfail with ho | hc
      · exact (ho hgood.1).elim
      · exact hc
    have happrox := archive_current_third_lower i q chi omega hchi hfine r hr t htr
    obtain ⟨k, hk⟩ := six_gap_is_actual_plane t
    refine Or.inr ⟨fixedParent_subset_unit i hp, k, ?_⟩
    rw [hk, abs_of_pos (sub_pos.mpr hgood.2)]
    linarith

theorem historyTransportRejected_subset_strips
    (i : ArchiveIndex) (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256) :
    historyTransportRejected i q chi omega ⊆ historyStrips ((9 / 2 : ℝ) * chi) := by
  intro t ht
  rcases canonicalHistory_subset_ideal_union_strips i q hq chi omega hchi hfine ht.1 with
    hi | hs
  · exact (ht.2 hi).elim
  · exact hs

theorem historyTransportCost_le
    (i : ArchiveIndex) (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256) :
    historyTransportCost i q chi omega ≤ rowMassBound (archiveRow i) * (198 * chi) := by
  have hv := (measure_mono
    (historyTransportRejected_subset_strips i q hq chi omega hchi hfine)).trans
      (historyStrips_volume ((9 / 2 : ℝ) * chi) (by positivity))
  have hrate : (44 : ℝ) * ((9 / 2 : ℝ) * chi) = 198 * chi := by ring
  rw [hrate] at hv
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ 198 * chi)] at hr
  exact mul_le_mul_of_nonneg_left hr (by linarith [one_le_rowMassBound (archiveRow i)])

/-- Direct payment of the actual additional rejected subset on all
original source positions. No bound on the independent ideal core is used. -/
theorem historyTransportBankCost_le
    (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256) :
    historyTransportBankCost q chi omega ≤ 198 * sourceMassSum licensedIndices * chi := by
  calc
    _ ≤ ∑ i ∈ licensedIndices, rowMassBound (archiveRow i) * (198 * chi) :=
      Finset.sum_le_sum (fun i _ => historyTransportCost_le i q hq chi omega hchi hfine)
    _ = _ := by rw [← Finset.sum_mul]; unfold sourceMassSum; ring

theorem canonicalHistoryCost_le_ideal_add_transport
    (i : ArchiveIndex) (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256) :
    canonicalHistoryCost i q chi omega ≤
      idealHistoryCost i + rowMassBound (archiveRow i) * (198 * chi) := by
  have hunit : volume unitCube = 1 := by simp [unitCube, volume_pi_pi, Real.volume_Icc]
  have hfinite : volume (idealHistoryInvalid i) ≠ ∞ := by
    have hs : idealHistoryInvalid i ⊆ unitCube :=
      fun _ ht => fixedParent_subset_unit i ht.1
    exact ((measure_mono hs).trans_lt (by rw [hunit]; simp)).ne
  have hs := (measure_mono
    (canonicalHistory_subset_ideal_union_strips i q hq chi omega hchi hfine)).trans
      (measure_union_le _ _)
  have hstrip := historyStrips_volume ((9 / 2 : ℝ) * chi) (by positivity)
  have hrate : (44 : ℝ) * ((9 / 2 : ℝ) * chi) = 198 * chi := by ring
  rw [hrate] at hstrip
  have hvolume : volume (canonicalInvalidHistory (archiveRow i) q chi omega) ≤
      volume (idealHistoryInvalid i) + ENNReal.ofReal (198 * chi) := by
    exact hs.trans (add_le_add_left hstrip (volume (idealHistoryInvalid i)))
  have hv := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite, ENNReal.ofReal_ne_top⟩) hvolume
  rw [ENNReal.toReal_add hfinite ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 198 * chi)] at hv
  have hm : 0 ≤ rowMassBound (archiveRow i) := by
    linarith [one_le_rowMassBound (archiveRow i)]
  have hmul := mul_le_mul_of_nonneg_left hv hm
  simpa only [canonicalHistoryCost, idealHistoryCost, mul_add] using hmul

/-- All original source positions are summed once, before any decoded
cell count. This is a quantitative payment of the actual mesh-induced
history loss; no ideal source-cost bound is among the premises. -/
theorem canonicalHistoryBankCost_le_ideal_add_transport
    (q : ℕ) (hq : 0 < q) (chi omega : ℝ)
    (hchi : 0 ≤ chi) (hfine : 7 * chi ≤ 3 / 256) :
    canonicalHistoryBankCost q chi omega ≤
      idealHistoryBankCost + 198 * sourceMassSum licensedIndices * chi := by
  calc
    _ ≤ ∑ i ∈ licensedIndices,
        (idealHistoryCost i + rowMassBound (archiveRow i) * (198 * chi)) :=
      Finset.sum_le_sum (fun i _ =>
        canonicalHistoryCost_le_ideal_add_transport i q hq chi omega hchi hfine)
    _ = _ := by
      simp only [idealHistoryBankCost, sourceMassSum,
        Finset.sum_add_distrib, Finset.sum_mul]
      ring

end
end ImbalancedChen.P5HistoricalThirdTransportStripPayment
