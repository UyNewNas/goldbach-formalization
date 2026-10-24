import ImbalancedChen.P4BPhysicalRampMassReserve
import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp

/-!
# P4B smooth physical mass from genuine arithmetic supported strips

SOURCE-ONLY / YELLOW / UNCOMPILED, 2026-10-24.

The finite mass transfer needs only an upper bound of one and nonzero
support inside every softened physical margin. The smooth construction
separately proves positivity, actual source domination and smoothness.
No comparison between smooth and linear ramp values is assumed or used.

The final reserve invokes the four concrete arithmetic strip suppliers,
shrinks their widths by a common minimum, and takes one common threshold.
There is no mass-reserve hypothesis or arithmetic-reserve hypothesis.
Imports are future normal module names of companion source-only drafts.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P4BLabelledPairDictionary

/-- Any bounded physical tuple weight with the genuine joint support has
its surplus paid by the same supported strips, regardless of its shape. -/
theorem supported_tupleWeight_sub_W_le_strip_union
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (hupper : ∀ t ∈ labelledPrimeTuples 2 N, V t ≤ 1)
    (hsupport : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 →
      ∀ i : Fin 4, -width < physicalPairMargins b N T t i)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N) :
    V t - W b N T t ≤ ∑ i : Fin 4, if
      (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
        (∀ j : Fin 4, -width < physicalPairMargins b N T t j)
      then (1 : ℝ) else 0 := by
  have hWnonneg : 0 ≤ W b N T t := by
    unfold W
    split_ifs <;> norm_num
  by_cases hresidual : 0 < V t - W b N T t
  · have hnonzero : V t ≠ 0 := by
      intro hz
      rw [hz] at hresidual
      linarith only [hresidual, hWnonneg]
    have hsoft := hsupport t ht hnonzero
    have hnotStrict : ¬ ∀ i : Fin 4, 0 < physicalPairMargins b N T t i := by
      intro hall
      have hWlower : 1 ≤ W b N T t := by
        simpa only [if_pos hall] using allStrictPhysicalMargins_indicator_le_W hN hT ht
      have hVupper := hupper t ht
      linarith only [hresidual, hWlower, hVupper]
    obtain ⟨i, hbad⟩ : ∃ i : Fin 4, physicalPairMargins b N T t i ≤ 0 := by
      simpa only [not_forall, not_lt] using hnotStrict
    have hjoint :
        (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
          (∀ j : Fin 4, -width < physicalPairMargins b N T t j) :=
      ⟨⟨hsoft i, hbad⟩, hsoft⟩
    calc
      V t - W b N T t ≤ 1 := by linarith only [hupper t ht, hWnonneg]
      _ = (if
          (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
            (∀ j : Fin 4, -width < physicalPairMargins b N T t j)
          then (1 : ℝ) else 0) := (if_pos hjoint).symm
      _ ≤ _ := Finset.single_le_sum
        (fun j _hj => by split_ifs <;> norm_num) (Finset.mem_univ i)
  · apply (le_of_not_gt hresidual).trans
    apply Finset.sum_nonneg
    intro i _hi
    split_ifs <;> norm_num

/-- Shape-independent genuine tuple mass transfer. The source term is
the exact W sum, so the mixed closed/strict source is unchanged. -/
theorem sum_supported_tupleWeight_le_source_card_add_strip_cards
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (hupper : ∀ t ∈ labelledPrimeTuples 2 N, V t ≤ 1)
    (hsupport : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 →
      ∀ i : Fin 4, -width < physicalPairMargins b N T t i) :
    (∑ t ∈ labelledPrimeTuples 2 N, V t) ≤
      ((realHalfProductSource b N T).card : ℝ) +
        ∑ i : Fin 4, ((physicalSupportedStrip width b N T i).card : ℝ) := by
  have hstrips :
      (∑ t ∈ labelledPrimeTuples 2 N, ∑ i : Fin 4, if
        (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
          (∀ j : Fin 4, -width < physicalPairMargins b N T t j)
        then (1 : ℝ) else 0) =
      ∑ i : Fin 4, ((physicalSupportedStrip width b N T i).card : ℝ) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [physicalSupportedStrip, ← Finset.sum_filter]
    simp
  calc
    (∑ t ∈ labelledPrimeTuples 2 N, V t) ≤
        ∑ t ∈ labelledPrimeTuples 2 N, (W b N T t + ∑ i : Fin 4, if
          (-width < physicalPairMargins b N T t i ∧ physicalPairMargins b N T t i ≤ 0) ∧
            (∀ j : Fin 4, -width < physicalPairMargins b N T t j)
          then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro t ht
      have hp := supported_tupleWeight_sub_W_le_strip_union hN hT V hupper hsupport ht
      linarith only [hp]
    _ = _ := by
      rw [Finset.sum_add_distrib, sum_actual_labelled_W_eq_source_card, hstrips]

/-- Smooth and linear ramps share the actual arithmetic support and the
same supported-strip budget; their values are never compared. -/
theorem sum_smoothPhysicalPairOuterRamp_le_source_card_add_supported_strip_cards
    {b T width : ℝ} {N : ℕ} (hN : (1 : ℝ) < N) (hT : 0 < T)
    (hwidth : 0 < width) :
    (∑ t ∈ labelledPrimeTuples 2 N, smoothPhysicalPairOuterRamp b N T width t) ≤
      ((realHalfProductSource b N T).card : ℝ) +
        ∑ i : Fin 4, ((physicalSupportedStrip width b N T i).card : ℝ) := by
  exact sum_supported_tupleWeight_le_source_card_add_strip_cards hN hT
    (smoothPhysicalPairOuterRamp b N T width)
    (fun t _ht => (smoothPhysicalPairOuterRamp_bounds b N T width t).2)
    (fun t _ht hn => smoothPhysicalPairOuterRamp_nonzero_margin_support hwidth hn)

/-- Reusable total arithmetic strip reserve, proved directly from all
four concrete wall suppliers. One width and threshold cover every wall. -/
theorem exists_physical_supported_strip_sum_reserve
    {b kappa : ℝ} (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (eta widthMax : ℝ) (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        (∑ i : Fin 4, ((physicalSupportedStrip width b N
          (manuscriptHalfProductCutoff kappa N) i).card : ℝ)) ≤
            eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hb : 0 < b := by linarith only [hbLower]
  have heta4 : 0 < eta / 4 := by linarith only [heta]
  obtain ⟨orderWidth, horderWidth, _horderMax, Norder, _hNorder, horder⟩ :=
    P4BSupportedOrderStripMass.exists_supported_order_strip_mass_reserve
      (eta := eta / 4) (widthMax := widthMax) hkappa hkappaOne heta4 hwidthMax
  obtain ⟨badnessWidth, hbadnessWidth, _hbadnessMax, _hbadnessLog,
      Nbadness, _hNbadness, hbadness⟩ :=
    P4BSupportedBadnessStripMass.exists_supported_badness_strip_mass_reserve
      (eta := eta / 4) (widthMax := widthMax)
      hbLower hbUpper hkappa hkappaOne heta4 hwidthMax
  obtain ⟨Nlower, _hNlower, hlower⟩ :=
    P4BLowerProductStripMass.physicalSupportedLowerStrip_mass_reserve
      (eta := eta / 4) hkappa heta4
  obtain ⟨upperWidth, hupperWidth, _hupperMax, Nupper, hupper⟩ :=
    P4BSupportedUpperProductStripMass.exists_width_eventually_supported_upper_strip_le
      hb hbUpper hkappa hkappaOne (eta / 4) widthMax heta4 hwidthMax
  let width : ℝ := min orderWidth (min badnessWidth (min widthMax upperWidth))
  have hwidth : 0 < width :=
    lt_min horderWidth (lt_min hbadnessWidth (lt_min hwidthMax hupperWidth))
  have hwidthOrder : width ≤ orderWidth := min_le_left _ _
  have hwidthBadness : width ≤ badnessWidth :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hwidthMaxLe : width ≤ widthMax :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hwidthUpper : width ≤ upperWidth :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  let N0 : ℕ := max 2 (max Norder (max Nbadness (max Nlower Nupper)))
  have hN0 : 2 ≤ N0 := le_max_left _ _
  refine ⟨width, hwidth, hwidthMaxLe, N0, hN0, ?_⟩
  intro N hNN0 hEven
  have hthresholds : Norder ≤ N ∧ Nbadness ≤ N ∧ Nlower ≤ N ∧ Nupper ≤ N := by
    dsimp only [N0] at hNN0
    omega
  have h0 : ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) 0).card : ℝ) ≤
      (eta / 4) * ((N : ℝ) / Real.log (N : ℝ)) := by
    exact (physicalSupportedStrip_cast_card_mono hwidthOrder 0).trans
      (horder N hthresholds.1 b (manuscriptHalfProductCutoff kappa N))
  have h1 : ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) 1).card : ℝ) ≤
      (eta / 4) * ((N : ℝ) / Real.log (N : ℝ)) := by
    exact (physicalSupportedStrip_cast_card_mono hwidthBadness 1).trans
      (hbadness N hthresholds.2.1)
  have h2 : ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) 2).card : ℝ) ≤
      (eta / 4) * ((N : ℝ) / Real.log (N : ℝ)) :=
    hlower N hthresholds.2.2.1 width b
  have h3 : ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) 3).card : ℝ) ≤
      (eta / 4) * ((N : ℝ) / Real.log (N : ℝ)) := by
    exact (physicalSupportedStrip_cast_card_mono hwidthUpper 3).trans
      (hupper N hthresholds.2.2.2 hEven)
  have hsum : (∑ i : Fin 4, ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) i).card : ℝ)) =
      ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 0).card : ℝ) +
      ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 1).card : ℝ) +
      ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 2).card : ℝ) +
      ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card : ℝ) := by
    simp [Fin.sum_univ_succ, add_assoc]
  rw [hsum]
  nlinarith only [h0, h1, h2, h3]

/-- True smooth physical mass reserve, parallel to the linear API. Every
arithmetic reserve is discharged by the concrete four-wall suppliers. -/
theorem exists_smooth_physical_ramp_mass_reserve
    {b kappa : ℝ} (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (eta widthMax : ℝ) (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        (∑ t ∈ labelledPrimeTuples 2 N,
          smoothPhysicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width t) ≤
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
            eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  obtain ⟨width, hwidth, hwidthMaxLe, N0, hN0, hcards⟩ :=
    exists_physical_supported_strip_sum_reserve
      hbLower hbUpper hkappa hkappaOne eta widthMax heta hwidthMax
  refine ⟨width, hwidth, hwidthMaxLe, N0, hN0, ?_⟩
  intro N hNN0 hEven
  have hN : 2 ≤ N := hN0.trans hNN0
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hT : 0 < manuscriptHalfProductCutoff kappa N := by
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hNreal) _)
  exact (sum_smoothPhysicalPairOuterRamp_le_source_card_add_supported_strip_cards
    hNreal hT hwidth).trans (add_le_add_left (hcards N hNN0 hEven) _)

end

end ImbalancedChen.P4B
