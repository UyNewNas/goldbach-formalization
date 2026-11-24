import ImbalancedChen.P5OriginalHistoryGapCorner

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

An unconditional quantitative payment of the actual original ideal core
in terms of the SAME raw keys. No core-nullness or small-cost hypothesis
is used. Rows with failed adjacent-key ordering retain their entire raw
volume charge. On an ordered row the third-gap core lies in a corner box
of widths 2d,2d,2d/5,1/400,1/400, where d is the actual negative corner
deficit. A negative corner deficit is not renamed a thin moving wall.

The full indexed source sum remains unevaluated and is NOT asserted to
fit an original reserve. All original positions and masks are retained.
-/
namespace ImbalancedChen.P5OriginalHistoryCorePayment
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open VariableEnvelope P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthCorrelatedRawBoxGates P1OriginalFifthLiteralKernelModulus
open P1OriginalFifthAdoptedOwnerBank
open P1HistoricalFifthIndexedOwnerArchive P1HistoricalFifthTypedBaseGeometry
open P5HistoricalCanonicalFilterReserve P5HistoricalThirdTransportStripPayment
open P5OriginalHistoryGapCorner

def cornerDeficit (raw : FifthWireRow) : ℝ := max 0 (-(rawThirdGapQ raw : ℝ))

theorem cornerDeficit_nonneg (raw : FifthWireRow) : 0 ≤ cornerDeficit raw :=
  le_max_left _ _

/-- Exact original integer keys determine the charge. The three saved
Jensen statistics and the selected fifth mask are never reinterpreted. -/
theorem archive_cornerDeficit_integer (i : ArchiveIndex) :
    cornerDeficit (archiveRow i) =
      ((max 0 (-producerThirdGap400 (archiveRow i)) : ℤ) : ℝ) / 12800 := by
  rw [cornerDeficit, ← producerThirdGap400_exact _ (archiveRow_grid i)]
  simp only [Int.cast_max, Int.cast_zero, Int.cast_neg]
  rw [← max_div_div_right (by norm_num : (0 : ℝ) ≤ 12800)]
  simp only [zero_div, neg_div]

def coreWidths (d : ℝ) : Fin 5 → ℝ := ![2*d, 2*d, 2*d/5, 1/400, 1/400]

def cornerCoreBox (raw : FifthWireRow) (d : ℝ) : Set (Fin 5 → ℝ) :=
  Set.univ.pi (fun k => Icc (upperPoint raw k - coreWidths d k) (upperPoint raw k))

theorem cornerCoreBox_volume (raw : FifthWireRow) (d : ℝ) (hd : 0 ≤ d) :
    volume (cornerCoreBox raw d) = ENNReal.ofReal ((8 / 5 : ℝ) * d^3 / 400^2) := by
  have h0 : 0 ≤ 2*d := by positivity
  have h2 : 0 ≤ 2*d/5 := by positivity
  have h4 : (0 : ℝ) ≤ 1/400 := by norm_num
  simp only [cornerCoreBox, volume_pi_pi, Real.volume_Icc, sub_sub_cancel,
    Fin.prod_univ_succ, coreWidths, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one]
  rw [← ENNReal.ofReal_mul h4, ← ENNReal.ofReal_mul h2,
    ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h0]
  congr 1
  ring

/-- The real five-dimensional raw box has its actual 400^-5 volume.
The ambient clipping may only decrease that volume. -/
theorem rawClosedBox_volume400 (raw : FifthWireRow) (hg : raw.grid = 400) :
    volume (rawClosedBox raw) = ENNReal.ofReal ((1 / 400 : ℝ)^5) := by
  have heq : rawClosedBox raw = Set.univ.pi
      (fun k => Icc (raw.lower k : ℝ) (raw.upper k : ℝ)) := by
    ext t
    simp only [rawClosedBox, mem_setOf_eq, mem_pi, mem_univ, true_implies, mem_Icc]
  have hwidth (k : Fin 5) : (raw.upper k : ℝ) - (raw.lower k : ℝ) = 1/400 := by
    simp only [FifthWireRow.upper, FifthWireRow.lower, hg]
    push_cast
    ring
  rw [heq, volume_pi_pi]
  simp_rw [Real.volume_Icc, hwidth]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/400),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/400),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/400),
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/400)]
  congr 1
  ring

/-- Original third-gap failure implies simultaneous closeness in THREE
coordinates to the fixed worst corner. The two later coordinates keep
their exact raw widths; no child-to-parent projection is removed. -/
theorem nonpositive_gap_subset_cornerCoreBox
    (raw : FifthWireRow) (hg : raw.grid = 400) (t : Fin 5 → ℝ)
    (ht : t ∈ raw.originalBox)
    (hgap : six (t 0) (t 1) (t 2) ≤ thirdCube t) :
    t ∈ cornerCoreBox raw (cornerDeficit raw) := by
  have hclosed : t ∈ rawClosedBox raw := fun k => ⟨(ht k).1, (ht k).2.le⟩
  have he := rawThirdGapQ_le_point_gap raw t hclosed
  have hd : -(rawThirdGapQ raw : ℝ) ≤ cornerDeficit raw := le_max_right _ _
  have h0 : 0 ≤ upperPoint raw 0 - t 0 := sub_nonneg.mpr (ht 0).2.le
  have h1 : 0 ≤ upperPoint raw 1 - t 1 := sub_nonneg.mpr (ht 1).2.le
  have h2 : 0 ≤ upperPoint raw 2 - t 2 := sub_nonneg.mpr (ht 2).2.le
  have hescape : cornerEscape t (upperPoint raw) ≤ cornerDeficit raw := by linarith
  have hwidth (k : Fin 5) : upperPoint raw k - 1/400 = (raw.lower k : ℝ) := by
    simp only [upperPoint, FifthWireRow.upper, FifthWireRow.lower, hg]
    push_cast
    ring
  intro k _
  refine ⟨?_, (ht k).2.le⟩
  fin_cases k
  · change upperPoint raw 0 - 2 * cornerDeficit raw ≤ t 0
    dsimp only [cornerEscape] at hescape
    linarith
  · change upperPoint raw 1 - 2 * cornerDeficit raw ≤ t 1
    dsimp only [cornerEscape] at hescape
    linarith
  · change upperPoint raw 2 - 2 * cornerDeficit raw / 5 ≤ t 2
    dsimp only [cornerEscape] at hescape
    linarith
  · change upperPoint raw 3 - 1/400 ≤ t 3
    rw [hwidth]
    exact (ht 3).1
  · change upperPoint raw 4 - 1/400 ≤ t 4
    rw [hwidth]
    exact (ht 4).1

/-- A genuine source licence: weak nonnegative corner gap already
suffices on the original half-open box, together with its integer order.
This theorem does not assert that the full archive has that licence. -/
theorem idealHistoryInvalid_empty_of_source_corner (i : ArchiveIndex)
    (ho : rawKeyOrdered (archiveRow i)) (hg : 0 ≤ rawThirdGapQ (archiveRow i)) :
    idealHistoryInvalid i = ∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro t ht
  have hraw : t ∈ (archiveRow i).originalBox := ht.1.1
  have horder := rawKeyOrdered_strictAnti (archiveRow i)
    (by rw [archiveRow_grid]; norm_num) ho t hraw
  have hpoint := rawThirdGapQ_lt_point_gap (archiveRow i) t hraw
  have hgR : (0 : ℝ) ≤ rawThirdGapQ (archiveRow i) := by exact_mod_cast hg
  rcases ht.2 with hbad | hbad
  · exact hbad horder
  · linarith

/-- Unordered rows retain the full source-volume debt. Ordered rows
receive an explicit cubic payment for their actual negative corner gap.
There is no mesh or desired cost estimate in this definition. -/
def sourceCoreVolumeCharge (i : ArchiveIndex) : ℝ :=
  if rawKeyOrdered (archiveRow i) then
    (8 / 5 : ℝ) * (cornerDeficit (archiveRow i))^3 / 400^2
  else (1 / 400 : ℝ)^5

theorem sourceCoreVolumeCharge_nonneg (i : ArchiveIndex) :
    0 ≤ sourceCoreVolumeCharge i := by
  have hd := cornerDeficit_nonneg (archiveRow i)
  unfold sourceCoreVolumeCharge
  split_ifs <;> positivity

/-- UNCONDITIONAL bound on the original ideal core at every original
position. The bad source is paid, not assumed absent. -/
theorem idealHistoryInvalid_volume_le_sourceCoreVolumeCharge (i : ArchiveIndex) :
    volume (idealHistoryInvalid i) ≤ ENNReal.ofReal (sourceCoreVolumeCharge i) := by
  by_cases ho : rawKeyOrdered (archiveRow i)
  · have hs : idealHistoryInvalid i ⊆
        cornerCoreBox (archiveRow i) (cornerDeficit (archiveRow i)) := by
      intro t ht
      have hraw : t ∈ (archiveRow i).originalBox := ht.1.1
      have horder := rawKeyOrdered_strictAnti (archiveRow i)
        (by rw [archiveRow_grid]; norm_num) ho t hraw
      have hgap : six (t 0) (t 1) (t 2) ≤ thirdCube t := by
        rcases ht.2 with hbad | hbad
        · exact (hbad horder).elim
        · exact hbad
      exact nonpositive_gap_subset_cornerCoreBox _ (archiveRow_grid i) t hraw hgap
    have hm := measure_mono hs
    rw [cornerCoreBox_volume _ _ (cornerDeficit_nonneg _)] at hm
    simpa only [sourceCoreVolumeCharge, if_pos ho] using hm
  · have hs : idealHistoryInvalid i ⊆ rawClosedBox (archiveRow i) := by
      intro t ht k
      exact ⟨(ht.1.1 k).1, (ht.1.1 k).2.le⟩
    have hm := measure_mono hs
    rw [rawClosedBox_volume400 _ (archiveRow_grid i)] at hm
    simpa only [sourceCoreVolumeCharge, if_neg ho] using hm

def sourceCoreCost (i : ArchiveIndex) : ℝ :=
  rowMassBound (archiveRow i) * sourceCoreVolumeCharge i

def sourceCoreBankCost : ℝ := ∑ i ∈ licensedIndices, sourceCoreCost i

theorem idealHistoryCost_le_sourceCoreCost (i : ArchiveIndex) :
    idealHistoryCost i ≤ sourceCoreCost i := by
  have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (idealHistoryInvalid_volume_le_sourceCoreVolumeCharge i)
  rw [ENNReal.toReal_ofReal (sourceCoreVolumeCharge_nonneg i)] at hv
  exact mul_le_mul_of_nonneg_left hv (by linarith [one_le_rowMassBound (archiveRow i)])

theorem idealHistoryBankCost_le_sourceCoreBankCost :
    idealHistoryBankCost ≤ sourceCoreBankCost := by
  exact Finset.sum_le_sum (fun i _ => idealHistoryCost_le_sourceCoreCost i)

/-- No position, repeated row or saved mask is deleted by the payment. -/
theorem sourceCoreBankCost_eq_full_index_sum :
    sourceCoreBankCost = ∑ i : ArchiveIndex, sourceCoreCost i := by
  rw [sourceCoreBankCost, licensedIndices_eq_univ]

/-- Exact point at which an original integer admission witness removes
this row's charge. No full-bank witness is manufactured here. -/
theorem sourceCoreCost_zero_of_producer_admission (i : ArchiveIndex)
    (ho : rawKeyOrdered (archiveRow i)) (hp : 0 < producerThirdGap400 (archiveRow i)) :
    sourceCoreCost i = 0 := by
  have hpR : (0 : ℝ) < producerThirdGap400 (archiveRow i) := by exact_mod_cast hp
  have hg := producerThirdGap400_exact (archiveRow i) (archiveRow_grid i)
  have hgap : (0 : ℝ) ≤ rawThirdGapQ (archiveRow i) := by linarith
  have hd : cornerDeficit (archiveRow i) = 0 := max_eq_left (neg_nonpos.mpr hgap)
  simp only [sourceCoreCost, sourceCoreVolumeCharge, if_pos ho, hd,
    zero_pow (by norm_num : 3 ≠ 0), mul_zero, zero_div]

end
end ImbalancedChen.P5OriginalHistoryCorePayment
