import ImbalancedChen.P1OriginalFifthAdoptedOwnerBank
import ImbalancedChen.P1FifthRawKeyThirdOwnerPersistence
import ImbalancedChen.P1FifthMask5RawOwnerLicence
import ImbalancedChen.P1FifthMask6RawOwnerLicence

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Original Gamma gate loss is compared on the SAME physical rational box.
The original zero/positive-buffer owner filters and firstStop predicates
are then proved for actual decoded labels from primitive integer keys.
No target trim, owner coverage or original archive pass is assumed.
-/
namespace ImbalancedChen.P5OriginalBufferOwnerGeometry
noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
open VariableEnvelope HistoricalThirdCoarse
open HistoricalThirdCoarse.P1OriginalCoarseFifth
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalVariableFifthContinuation
open P1OriginalCoarseFifthContinuation
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1FifthUnitBoxGainDecomposition
open P1FifthRawKeyThirdOwnerPersistence
open P1OriginalFifthAdoptedOwnerBank

/-- Relaxing the literal xz gate may only add a real Gamma entry. -/
theorem xz_entry_le_fullGamma {a : ℝ} (b : RationalBox) (h : a ≤ xzGap b) :
    qVLo (b.lx + b.lz) (b.ux + b.uz) ≤ fullGamma a b := by
  unfold fullGamma
  rw [if_pos h]
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_left _ _))))

theorem yz_entry_le_fullGamma {a : ℝ} (b : RationalBox) (h : a ≤ yzGap b) :
    qVLo (b.ly + b.lz) (b.uy + b.uz) ≤ fullGamma a b := by
  unfold fullGamma
  rw [if_pos h]
  exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right
    (le_max_of_le_right (le_max_right _ _))))

/-- The complete gated max retains the baseline when either pair fails.
This is not a monotonicity claim about unrelated ideal density caps. -/
theorem fullGamma_antitone_loss {a z : ℝ} (haz : a ≤ z) (b : RationalBox) :
    fullGamma z b ≤ fullGamma a b := by
  have hbase := baseline_le_fullGamma a b
  have hxy : qVLo (b.lx + b.ly) (b.ux + b.uy) ≤ fullGamma a b := by
    exact le_max_of_le_right (le_max_left _ _)
  have hxyz : qVLo (b.lx + b.ly + b.lz) (b.ux + b.uy + b.uz) ≤ fullGamma a b := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_left _ _))
  have hres : rescue b ≤ fullGamma a b := by
    exact le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hxz : (if z ≤ xzGap b then qVLo (b.lx + b.lz) (b.ux + b.uz)
      else qVLo b.lx b.ux) ≤ fullGamma a b := by
    split_ifs with hz
    · exact xz_entry_le_fullGamma b (haz.trans hz)
    · exact hbase
  have hyz : (if z ≤ yzGap b then qVLo (b.ly + b.lz) (b.uy + b.uz)
      else qVLo b.lx b.ux) ≤ fullGamma a b := by
    split_ifs with hz
    · exact yz_entry_le_fullGamma b (haz.trans hz)
    · exact hbase
  exact max_le hbase (max_le hxy (max_le hxyz (max_le hres (max_le hxz hyz))))

theorem gamma_antitone_loss {a z : ℝ} (haz : a ≤ z) (b : RationalBox) :
    gamma z b ≤ gamma a b := by
  by_cases hz : (b.ux : ℝ) ≤ mu - 4 * z
  · have ha : (b.ux : ℝ) ≤ mu - 4 * a := by linarith
    simpa only [gamma, if_pos hz, if_pos ha] using fullGamma_antitone_loss haz b
  · simpa only [gamma, if_neg hz] using baseline_le_gamma a b

theorem levelExponent_antitone_loss {a z : ℝ} (haz : a ≤ z) (b : RationalBox) :
    levelExponent z b ≤ levelExponent a b := by
  have hg : (gamma z b : ℝ) ≤ (gamma a b : ℝ) := by
    exact_mod_cast gamma_antitone_loss haz b
  dsimp [levelExponent]
  linarith

/-- Keep the true selected owner at both losses. Then all actual original
parent cubes and firstStop at positive buffer imply their zero-buffer
versions on the same half-open cell. Both source exponents remain visible. -/
theorem fullCell_buffer_subset_zero
    (e : ℚ) (he : 0 ≤ e) (chi : ℝ) (m : ℕ) (omega : ℝ)
    (J : Finset (Label5 m)) (j : Label5 m)
    (hsel0 : j ∈ selectedFifthCells 0 chi m omega J)
    (hselE : j ∈ selectedFifthCells e chi m omega J) :
    P1OriginalFifthUntruncatedIntegral.fullCell e chi m omega j ⊆
      P1OriginalFifthUntruncatedIntegral.fullCell 0 chi m omega j := by
  intro t ht
  have hmesh := ht.2.2.1
  have hj := (mem_jointRegion (e : ℝ) chi m omega j t).mp ht.2.2.2
  have heR : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hstop0 : t ∈ firstLabelRegion 0 m := by
    obtain ⟨i, hlo, hhi, hstop⟩ := hj.1
    exact ⟨i, hlo, hhi, by linarith⟩
  have hinit : initial (e : ℝ) ≤ initial 0 := by dsimp [initial]; linarith
  have hcurrent : currentExponent (e : ℝ) chi m omega j t ≤
      currentExponent 0 chi m omega j t := by
    rw [P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
        e chi m omega J j hselE hmesh,
      P1OriginalHistoricalFifthOwnCubeAffineGates.selected_currentExponent
        0 chi m omega J j hsel0 hmesh]
    exact levelExponent_antitone_loss heR _
  refine ⟨ht.1, ht.2.1, hmesh, (mem_jointRegion 0 chi m omega j t).mpr ?_⟩
  exact ⟨hstop0, hj.2.1, hj.2.2.1.trans_le hinit,
    hj.2.2.2.1.trans_le hcurrent, hj.2.2.2.2.trans_le hcurrent⟩

/-- Actual primitive saved key endpoints, not a selected-owner result,
force each contained decoded upper first coordinate below firstStop. -/
theorem decoded_firstStop_of_key (raw : FifthWireRow)
    (hc : thirdOwnerKeyCheck raw = true) (z : ℚ) (hz : z ≤ 3 / 51200)
    (m : ℕ) (r : FifthRow m) (hr : r ∈ decodeFifthRows raw m) :
    P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck (z : ℝ) m r.cell = true := by
  have hk := thirdOwnerKeyCheck_sound raw hc
  have hcontained : fifthCellContained raw m r.cell := by
    obtain ⟨_, _, j, hj, heq⟩ := (mem_decodeFifthRows_iff raw m r).mp hr
    cases heq
    exact hj
  have htop : raw.upper 0 ≤ (79 / 400 : ℚ) := by
    have hi : (raw.lo 0 : ℚ) ≤ 78 := by exact_mod_cast hk.2.2.2.2.2
    simp only [FifthWireRow.upper, hk.1]
    push_cast
    linarith
  have hstopQ : qLogPrimeMeshHi 0 (19 / 96) m r.cell 0 ≤ 19 / 96 - 4 * z :=
    ((hcontained 0).2.trans htop).trans (by linarith [positive_stop_surplus z hz])
  apply (P1OriginalHistoricalFifthOwnCubeAffineGates.firstStopCellCheck_iff (z : ℝ) m r.cell).mpr
  rw [← congrFun (cast_qLogPrimeMeshHi 0 (19 / 96) m r.cell) 0]
  have hcast : (qLogPrimeMeshHi 0 (19 / 96) m r.cell 0 : ℝ) ≤ (19 / 96 : ℝ) - 4 * (z : ℝ) := by
    exact_mod_cast hstopQ
  simpa only [VariableEnvelope.extendedFirstStop] using hcast

/-- Both selected filters and both firstStop checks are derived from the
independent integer key test on every actual decoded row. -/
theorem adoptedOwners_eq_decodedLabels_of_key (raw : FifthWireRow)
    (hc : thirdOwnerKeyCheck raw = true)
    (e : ℚ) (hemax : e ≤ 3 / 51200) (q : ℕ) (chi omega : ℝ)
    (hstep : logPrimeMeshStep 0 (19 / 96) (refinedMesh q) ≤ chi)
    (hw : omega ≤ 1 / 400) :
    adoptedOwners raw e q chi omega = decodedLabels raw q := by
  ext j
  constructor
  · intro hj
    obtain ⟨r, hr, heq⟩ := adoptedOwners_original_decoded raw e q chi omega j hj
    exact Finset.mem_image.mpr ⟨r, hr, heq⟩
  · intro hj
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
    have h0 := decoded_third_owner_selected raw hc 0 (by norm_num) chi omega (refinedMesh q)
      hstep hw (decodedLabels raw q) r hr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    have hE := decoded_third_owner_selected raw hc e hemax chi omega (refinedMesh q)
      hstep hw (decodedLabels raw q) r hr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨h0, hE⟩,
      decoded_firstStop_of_key raw hc 0 (by norm_num) (refinedMesh q) r hr,
      decoded_firstStop_of_key raw hc e hemax (refinedMesh q) r hr⟩

end
end ImbalancedChen.P5OriginalBufferOwnerGeometry
