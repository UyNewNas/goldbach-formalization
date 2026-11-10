import ImbalancedChen.P4AOriginalNewFifthMean
import ImbalancedChen.P5HistoricalRectangularGammaTransport
import ImbalancedChen.P2OriginalSaving16HistoricalMesh

/-! Both archive grids tile the existing m=475q-1 mesh. The original
positive thirds and full/selected gate buffers apply uniformly on every
retained source box, prior to N and independently of the previous bank. -/
namespace ImbalancedChen.P4AOriginalNewFifthCoverage
noncomputable section
open Set
open scoped Classical BigOperators
open P4AOriginalNewFifthArchiveData P4AOriginalNewFifthArchive P4AOriginalNewFifthUnion
open P1OriginalPrefixRowDecodeSoundness
open P1OriginalFifthGrid400RefinedFullBoxCover
open P1OriginalVariableFifthContinuation (FifthRow eligible gateCheck candidate)
open P1OriginalCoarseFifthContinuation (selectedFifthCells mem_selectedFifthCells)
open P1OriginalFifthAdoptedOwnerBank (adoptedOwners decodedLabels)
open P1OriginalFifthCorrelatedRawBoxGates
open P1OriginalFifthQuantitativeGateRefinement
open HistoricalThirdCoarse HistoricalThirdCoarse.P1OriginalCoarseFifth VariableEnvelope
open P1OriginalHistoricalFifthOwnCubeAffineGates (firstStopCellCheck firstStopCellCheck_iff
  firstLabelRegion_on_cell selected_currentExponent)
open P1OriginalFifthUntruncatedIntegral (fullCell)

theorem aligned800 (q : ℕ) (hq : 0 < q)
    (k : ℤ) (j : ℕ) (x : ℝ)
    (hrawlo : (k : ℝ) / 800 ≤ x) (hrawhi : x < ((k : ℝ) + 1) / 800)
    (hmeshlo : (j : ℝ) / ((2400 : ℝ) * (q : ℝ)) ≤ x)
    (hmeshhi : x < ((j : ℝ) + 1) / ((2400 : ℝ) * (q : ℝ))) :
    (k : ℚ) / 800 ≤ (j : ℚ) / ((2400 : ℚ) * (q : ℚ)) ∧
      ((j : ℚ) + 1) / ((2400 : ℚ) * (q : ℚ)) ≤ ((k : ℚ) + 1) / 800 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (0 : ℝ) < (2400 : ℝ) * (q : ℝ) := by positivity
  have hrawlo' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 800)).mp hrawlo
  have hrawhi' := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 800)).mp hrawhi
  have hloScaled : (3 : ℝ) * (q : ℝ) * (k : ℝ) ≤ x * ((2400 : ℝ) * (q : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hrawlo' (by positivity : (0 : ℝ) ≤ 3 * (q : ℝ))
    nlinarith
  have hhiScaled : x * ((2400 : ℝ) * (q : ℝ)) < (3 : ℝ) * (q : ℝ) * ((k : ℝ) + 1) := by
    have hh := mul_lt_mul_of_pos_left hrawhi' (by positivity : (0 : ℝ) < 3 * (q : ℝ))
    nlinarith
  have hloR : (3 : ℝ) * (q : ℝ) * (k : ℝ) < (j : ℝ) + 1 :=
    hloScaled.trans_lt ((lt_div_iff₀ hdR).mp hmeshhi)
  have hhiR : (j : ℝ) < (3 : ℝ) * (q : ℝ) * ((k : ℝ) + 1) :=
    ((div_le_iff₀ hdR).mp hmeshlo).trans_lt hhiScaled
  have hloZ : (3 : ℤ) * (q : ℤ) * k < (j : ℤ) + 1 := by exact_mod_cast hloR
  have hhiZ : (j : ℤ) < (3 : ℤ) * (q : ℤ) * (k + 1) := by exact_mod_cast hhiR
  have hloInt : (3 : ℤ) * (q : ℤ) * k ≤ (j : ℤ) := by omega
  have hhiInt : (j : ℤ) + 1 ≤ (3 : ℤ) * (q : ℤ) * (k + 1) := by omega
  have hloQ : (3 : ℚ) * (q : ℚ) * (k : ℚ) ≤ (j : ℚ) := by exact_mod_cast hloInt
  have hhiQ : (j : ℚ) + 1 ≤ (3 : ℚ) * (q : ℚ) * ((k : ℚ) + 1) := by exact_mod_cast hhiInt
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hdQ : (0 : ℚ) < (2400 : ℚ) * (q : ℚ) := by positivity
  constructor
  · apply (le_div_iff₀ hdQ).mpr
    nlinarith
  · apply (div_le_iff₀ hdQ).mpr
    nlinarith


theorem whole_point_decoded (i : Position) (q : ℕ) (hq : 0 < q) (t : Fin 5 → ℝ)
    (ht : t ∈ (rawRow i).originalBox) (j : RefinedCell q)
    (hj : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) j) :
    rowAt i q j ∈ decodeFifthRows (rawRow i) (refinedMesh q) := by
  have hg := row_grid i
  apply (mem_decodeFifthRows_iff _ _ _).mpr
  refine ⟨(facts i).1, (by linarith [(geometry i).2.2.2.2.1] : 0 ≤ (rawRow i).mask),
    j, ?_, rfl⟩
  cases hi : i.1.1
  · have h400 : (rawRow i).grid = 400 := by simpa [grid, hi] using hg
    exact refined_owner_is_contained q hq _ h400 t ht j hj
  · have h800 : (rawRow i).grid = 800 := by simpa [grid, hi] using hg
    intro k
    have hh := mem_logPrimeMeshCell.mp hj k
    rw [refined_lo q hq, refined_hi q hq] at hh
    have hlo : ((rawRow i).lo k : ℝ) / 800 ≤ t k := by
      simpa [FifthWireRow.lower,h800] using (ht k).1
    have hhi : t k < (((rawRow i).lo k : ℝ)+1)/800 := by
      simpa [FifthWireRow.upper,h800] using (ht k).2
    simpa [FifthWireRow.lower,FifthWireRow.upper,h800,refined_qlo q hq,refined_qhi q hq] using
      aligned800 q hq ((rawRow i).lo k) (j k).val (t k) hlo hhi hh.1 hh.2

theorem row_gate (i : Position) (e z : ℚ) (hze : z ≤ e) (hcap : e ≤ 1/64000) (q : ℕ)
    (hstep : logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ (e : ℝ)/20) :
    ∀ r ∈ decodeFifthRows (rawRow i) (refinedMesh q), gateCheck z (refinedMesh q) r = true := by
  obtain ⟨_,_,_,_,_,_,_,_,hg,hm,_⟩ := geometry i
  have hq : meshStepQ (refinedMesh q) ≤ e/20 := by
    have hR : (meshStepQ (refinedMesh q) : ℝ) ≤ (e : ℝ)/20 := by simpa only [cast_meshStepQ] using hstep
    exact_mod_cast hR
  apply all_decoded_gateCheck_eq_true_of_uniform_margin z (1/1600 - 2*z) _ _ (by linarith)
  intro t ht
  have H := (correlatedRawBoxGateCheck_uniform_margin 0 _ hg).2 t ht
  have hdelta : (1/1600 : ℝ) ≤ (gateMarginQ 0 (rawRow i) : ℝ) := by exact_mod_cast hm
  have hc : candidate (z : ℝ) (maskSlots 5 (rawRow i).mask.toNat) t =
      candidate 0 (maskSlots 5 (rawRow i).mask.toNat) t - 2*(z : ℝ) := by simp [candidate]
  simp only [Rat.cast_zero] at H
  push_cast
  rw [hc]
  refine ⟨by linarith [H.1], ?_, ?_⟩
  · intro j
    linarith [H.2.1 j]
  · intro j hj
    linarith [H.2.2 j hj]

/-- Conditions expressed purely in the pre-N scalar mesh parameters. -/
def Schedule (e : ℚ) (q : ℕ) (a : ℝ) : Prop :=
  0 ≤ e ∧ e ≤ 1/64000 ∧ 0 < q ∧
    logPrimeMeshStep 0 (19/96) (refinedMesh q) ≤ (e : ℝ)/20 ∧ a ≤ 1/800

private theorem decoded_containment (i : Position) (q : ℕ) (j : RefinedCell q)
    (hr : rowAt i q j ∈ decodeFifthRows (rawRow i) (refinedMesh q)) :
    fifthCellContained (rawRow i) (refinedMesh q) j := by
  obtain ⟨_,_,j',hc,he⟩ := (mem_decodeFifthRows_iff _ _ _).mp hr
  have hj : j = j' := congrArg FifthRow.cell he
  exact hj.symm ▸ hc

theorem support_geometry (i : Position) (e z : ℚ) (q : ℕ) (a : ℝ) (hs : Schedule e q a)
    (hz : 0 ≤ z) (hze : z ≤ e) (j : RefinedCell q) (t : Fin 5 → ℝ)
    (hr : rowAt i q j ∈ decodeFifthRows (rawRow i) (refinedMesh q))
    (ht : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) j) :
    j ∈ selectedFifthCells z ((e : ℝ)/20) (refinedMesh q) a (decodedLabels (rawRow i) q) ∧
      firstStopCellCheck (z : ℝ) (refinedMesh q) j = true ∧
      t ∈ fullCell z ((e : ℝ)/20) (refinedMesh q) a j := by
  let m := refinedMesh q
  let b := box m (thirdOwner j)
  have hc := decoded_containment i q j hr
  have hx := (decodeFifthRows_source_geometry _ _ _ hr t ht).2.2.2
  obtain ⟨_,hlo,hmax,horder,_,_,_,_,_,_,hthird⟩ := geometry i
  have zR : 0 ≤ (z : ℝ) := by exact_mod_cast hz
  have eR : (e : ℝ) ≤ 1/64000 := by exact_mod_cast hs.2.1
  have zeR : (z : ℝ) ≤ (e : ℝ) := by exact_mod_cast hze
  have hb : b.InBox (t 0) (t 1) (t 2) := by
    have hp := mem_logPrimeMeshCell_historicalPrefixProject (by decide : 3 ≤ 5) ht
    simpa only [b,thirdOwner,historicalPrefixProject] using inBox_of_cell hp
  have hw : (b.width : ℝ) ≤ (e : ℝ)/20 := by
    simpa only [b,m,P2OriginalSaving16HistoricalMesh.mesh_box_width] using hs.2.2.2.1
  have hux : b.ux ≤ 39/200 := (hc 0).2.trans hmax
  have hxR : (b.ux : ℝ) ≤ 39/200 := by exact_mod_cast hux
  have hly : b.uz ≤ b.ly := (hc 2).2.trans ((horder 1).trans (hc 1).1)
  have hlx : b.uy ≤ b.lx := (hc 1).2.trans ((horder 0).trans (hc 0).1)
  have hlz : (1/50 : ℚ) ≤ b.lz := (hlo 2).trans (hc 2).1
  have hlzR : (1/50 : ℝ) ≤ (b.lz : ℝ) := by exact_mod_cast hlz
  have hmu : (b.ux : ℝ) ≤ mu - 4 * (z : ℝ) := by dsimp [mu]; linarith
  have hstop : (b.ux : ℝ) ≤ extendedFirstStop - 4 * (z : ℝ) := by dsimp [extendedFirstStop]; linarith
  have hstop' : firstStopCellCheck (z : ℝ) m j = true := by
    apply (firstStopCellCheck_iff _ _ _).mpr
    have hv := congrFun (cast_qLogPrimeMeshHi 0 (19/96) m j) 0
    change (qLogPrimeMeshHi 0 (19/96) m j 0 : ℝ) ≤ _ at hstop
    simpa only [hv] using hstop
  have hphys : thirdOwner j ∈ cells (z : ℝ) ((e : ℝ)/20) m :=
    (mem_cells _ _ _ _).mpr ⟨RationalBox.wellFormed_of_inBox hb, by linarith,
      hly,hlx,hstop,hw⟩
  have hsRough : a ≤ (b.lz : ℝ) := by linarith [hs.2.2.2.2]
  have hdecoded : j ∈ decodedLabels (rawRow i) q := Finset.mem_image.mpr ⟨rowAt i q j,hr,rfl⟩
  have hsel := (mem_selectedFifthCells z ((e : ℝ)/20) m a _ j).mpr ⟨hdecoded,hphys,hsRough⟩
  have hanti : StrictAnti t := by
    apply Fin.strictAnti_iff_succ_lt.mpr
    intro k
    have hR : ((rawRow i).upper k.succ : ℝ) ≤ ((rawRow i).lower k.castSucc : ℝ) := by
      exact_mod_cast horder k
    exact ((hx k.succ).2.trans_le hR).trans_le (hx k.castSucc).1
  have hpos (k : Fin 5) : 0 < t k :=
    (by norm_num : (0 : ℝ) < 1/50).trans_le ((show (1/50 : ℝ) ≤ ((rawRow i).lower k : ℝ)
      by exact_mod_cast hlo k).trans (hx k).1)
  have hord : Ordered (t 0) (t 1) (t 2) := ⟨(hpos 2).le,
    (hanti (by decide : (1 : Fin 5) < 2)).le,(hanti (by decide : (0 : Fin 5) < 1)).le,
    by linarith [hb.2.1]⟩
  have hGamma := (P5HistoricalRectangularGammaTransport.fullGamma_error (z : ℝ) ((e : ℝ)/20)
    b (by linarith) hw hb hord (by linarith)).2
  have hcur : currentExponent (z : ℝ) ((e : ℝ)/20) m a j t = (fullGamma (z : ℝ) b : ℝ) - 2*(z : ℝ) := by
    rw [selected_currentExponent z ((e : ℝ)/20) m a _ j hsel ht]
    simp only [levelExponent, gamma, b, hmu, if_true]
  have hGap := (P5OriginalHistoryGapCorner.rawThirdGapQ_attained_minimum (rawRow i) (facts i).1).1 t
    (fun k => ⟨(hx k).1, (hx k).2.le⟩)
  have hgap : (1/1600 : ℝ) ≤ (P5OriginalHistoryGapCorner.rawThirdGapQ (rawRow i) : ℝ) := by
    exact_mod_cast hthird
  have hfirst : v (t 0) ≤ six (t 0) (t 1) (t 2) := le_max_left _ _
  rw [v_eq_A hord.2.2.2] at hfirst
  have htop : t 0 ≤ 39/200 := hb.2.1.trans hxR
  have hJoint : t ∈ jointRegion (z : ℝ) ((e : ℝ)/20) m a j := by
    apply (mem_jointRegion _ _ _ _ _ _).mpr
    refine ⟨(firstLabelRegion_on_cell _ _ _ _ ht).mpr ((firstStopCellCheck_iff _ _ _).mp hstop'),
      hanti, ?_, ?_, ?_⟩
    · dsimp [initial,extendedDistributionCap]
      linarith
    · rw [hcur]
      dsimp [A] at hfirst
      linarith
    · rw [hcur]
      dsimp only [P5HistoricalThirdTransportStripPayment.thirdCube] at hGap
      linarith
  exact ⟨hsel,hstop',hpos,logPrimeMeshCell_subset_box (by norm_num : (0 : ℝ) < 19/96) m j ht,ht,hJoint⟩

theorem complete_owner (i : Position) (e : ℚ) (q : ℕ) (a : ℝ) (hs : Schedule e q a)
    (t : Fin 5 → ℝ) (ht : t ∈ (rawRow i).originalBox) (j : RefinedCell q)
    (hj : t ∈ logPrimeMeshCell 0 (19/96) (refinedMesh q) j) :
    j ∈ owners i e q a ∧ t ∈ fullCell e ((e : ℝ)/20) (refinedMesh q) a j := by
  have hr := whole_point_decoded i q hs.2.2.1 t ht j hj
  have h0 := support_geometry i e 0 q a hs le_rfl hs.1 j t hr hj
  have he := support_geometry i e e q a hs hs.1 le_rfl j t hr hj
  have hown : j ∈ adoptedOwners (rawRow i) e q ((e : ℝ)/20) a :=
    Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨h0.1,he.1⟩,h0.2.1,he.2.1⟩
  exact ⟨Finset.mem_filter.mpr ⟨hown,row_gate i e 0 hs.1 hs.2.1 q hs.2.2.2.1 _ hr,
    row_gate i e e le_rfl hs.2.1 q hs.2.2.2.1 _ hr⟩,he.2.2⟩

theorem source_box_eq_full_owner_union (i : Position) (e : ℚ) (q : ℕ) (a : ℝ) (hs : Schedule e q a) :
    (rawRow i).originalBox = ⋃ j ∈ owners i e q a, fullCell e ((e : ℝ)/20) (refinedMesh q) a j := by
  ext t
  constructor
  · intro ht
    have hamb : t ∈ logPrimeBox (fun _ : Fin 5 => (0 : ℝ)) (fun _ => (19/96 : ℝ)) := by
      apply mem_logPrimeBox.mpr
      intro k
      have hc := ((facts i).2.1 k)
      exact ⟨(show (0 : ℝ) ≤ ((rawRow i).lower k : ℝ) by
          exact_mod_cast (le_trans (by norm_num : (0 : ℚ) ≤ 1/400) hc.1)).trans (ht k).1,
        (ht k).2.trans_le (by exact_mod_cast hc.2)⟩
    obtain ⟨j,hj⟩ := exists_logPrimeMeshCell 0 (19/96) (refinedMesh q) hamb
    obtain ⟨ho,hcell⟩ := complete_owner i e q a hs t ht j hj
    exact mem_iUnion₂.mpr ⟨j,ho,hcell⟩
  · intro h
    obtain ⟨j,hj,hfull⟩ := mem_iUnion₂.mp h
    exact (decodeFifthRows_source_geometry _ _ _ (rowAt_decodes i e q a j hj) t hfull.2.2.1).2.2.2

end
end ImbalancedChen.P4AOriginalNewFifthCoverage
