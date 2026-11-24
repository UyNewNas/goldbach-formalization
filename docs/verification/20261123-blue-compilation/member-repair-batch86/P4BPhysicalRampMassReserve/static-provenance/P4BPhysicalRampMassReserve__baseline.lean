import ImbalancedChen.P4BSupportedRampStripUnion
import ImbalancedChen.P4BSupportedOrderStripMass
import ImbalancedChen.P4BSupportedBadnessStripMass
import ImbalancedChen.P4BLowerProductStripMass
import ImbalancedChen.P4BSupportedUpperProductStripMass

/-!
# Physical four-wall ramp mass from concrete arithmetic reserves

SOURCE ONLY / YELLOW / UNCOMPILED.
The finite monotonicity lemmas below concern the actual labelled prime
carrier and actual physical margins. They hold for every real width.
The final theorem invokes the four concrete proved arithmetic suppliers at
eta/4, takes one common positive width and one eventual natural threshold,
and pays the actual four-wall physical ramp surplus. No boundary reserve
or final mass conclusion is introduced as an assumption in this module.
All imports name future normal modules of source-complete yellow drafts.
-/

namespace ImbalancedChen.P4B

noncomputable section

open scoped Classical BigOperators
open ImbalancedChen.Part3

/-- Every actual softened physical half-space grows with its width. -/
theorem physicalSoftenedMargins_mono
    {small large b T : ℝ} {N : ℕ} (hle : small ≤ large)
    {t : Fin 2 → Fin (N + 1)}
    (hsoft : ∀ i : Fin 4, -small < physicalPairMargins b N T t i) :
    ∀ i : Fin 4, -large < physicalPairMargins b N T t i := by
  intro i
  have hi := hsoft i
  linarith only [hle, hi]

/-- Joint softened support is nested on the unchanged actual prime carrier. -/
theorem physicalSoftenedSupport_mono
    {small large b T : ℝ} {N : ℕ} (hle : small ≤ large) :
    (labelledPrimeTuples 2 N).filter (fun t =>
      ∀ i : Fin 4, -small < physicalPairMargins b N T t i) ⊆
      (labelledPrimeTuples 2 N).filter (fun t =>
        ∀ i : Fin 4, -large < physicalPairMargins b N T t i) := by
  intro t ht
  obtain ⟨hprime, hsoft⟩ := Finset.mem_filter.mp ht
  exact Finset.mem_filter.mpr ⟨hprime, physicalSoftenedMargins_mono hle hsoft⟩

/-- The full single-wall arithmetic strip is also nested, preserving its
strict left endpoint and weak zero endpoint. -/
theorem physicalPairArithmeticStrip_mono
    {small large b T : ℝ} {N : ℕ} (hle : small ≤ large) (i : Fin 4) :
    physicalPairArithmeticStrip b N T small i ⊆
      physicalPairArithmeticStrip b N T large i := by
  intro t ht
  obtain ⟨hprime, hstrip⟩ := Finset.mem_filter.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨hprime, ?_, hstrip.2⟩
  linarith only [hle, hstrip.1]

/-- A jointly supported strip grows with the common physical width, for
every wall. Both the selected wall and all remaining softened gates grow. -/
theorem physicalSupportedStrip_mono
    {small large b T : ℝ} {N : ℕ} (hle : small ≤ large) (i : Fin 4) :
    physicalSupportedStrip small b N T i ⊆ physicalSupportedStrip large b N T i := by
  intro t ht
  obtain ⟨hprime, hstrip, hsoft⟩ := (mem_physicalSupportedStrip small b N T i t).mp ht
  apply (mem_physicalSupportedStrip large b N T i t).mpr
  refine ⟨hprime, ⟨?_, hstrip.2⟩, physicalSoftenedMargins_mono hle hsoft⟩
  linarith only [hle, hstrip.1]

/-- Natural cardinality monotonicity of every actual supported wall. -/
theorem physicalSupportedStrip_card_mono
    {small large b T : ℝ} {N : ℕ} (hle : small ≤ large) (i : Fin 4) :
    (physicalSupportedStrip small b N T i).card ≤
      (physicalSupportedStrip large b N T i).card := by
  exact Finset.card_le_card (physicalSupportedStrip_mono hle i)

/-- The same monotonicity at the real-valued arithmetic mass scale. -/
theorem physicalSupportedStrip_cast_card_mono
    {small large b T : ℝ} {N : ℕ} (hle : small ≤ large) (i : Fin 4) :
    ((physicalSupportedStrip small b N T i).card : ℝ) ≤
      ((physicalSupportedStrip large b N T i).card : ℝ) := by
  exact_mod_cast physicalSupportedStrip_card_mono hle i

/-- All four arithmetic reserves are supplied by their concrete proofs.
Only the fixed original b,kappa domain and positive eta,widthMax are inputs.
One common width and one threshold control the actual labelled ramp mass. -/
theorem exists_physical_ramp_mass_reserve
    {b kappa : ℝ} (hbLower : (1 / 2 : ℝ) < b) (hbUpper : b < 1)
    (hkappa : 0 < kappa) (hkappa1 : kappa < 1)
    (eta widthMax : ℝ) (heta : 0 < eta) (hwidthMax : 0 < widthMax) :
    ∃ width : ℝ, 0 < width ∧ width ≤ widthMax ∧
      ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → Even N →
        (∑ t ∈ labelledPrimeTuples 2 N,
          physicalPairOuterRamp b N (manuscriptHalfProductCutoff kappa N) width t) ≤
          ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) +
            eta * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hb : 0 < b := by linarith only [hbLower]
  have heta4 : 0 < eta / 4 := by linarith only [heta]
  obtain ⟨orderWidth, horderWidth, _horderMax, Norder, _hNorder, horder⟩ :=
    P4BSupportedOrderStripMass.exists_supported_order_strip_mass_reserve
      (eta := eta / 4) (widthMax := widthMax) hkappa hkappa1 heta4 hwidthMax
  obtain ⟨badnessWidth, hbadnessWidth, _hbadnessMax, _hbadnessLog,
      Nbadness, _hNbadness, hbadness⟩ :=
    P4BSupportedBadnessStripMass.exists_supported_badness_strip_mass_reserve
      (eta := eta / 4) (widthMax := widthMax)
      hbLower hbUpper hkappa hkappa1 heta4 hwidthMax
  obtain ⟨Nlower, _hNlower, hlower⟩ :=
    P4BLowerProductStripMass.physicalSupportedLowerStrip_mass_reserve
      (eta := eta / 4) hkappa heta4
  obtain ⟨upperWidth, hupperWidth, _hupperMax, Nupper, hupper⟩ :=
    P4BSupportedUpperProductStripMass.exists_width_eventually_supported_upper_strip_le
      hb hbUpper hkappa hkappa1 (eta / 4) widthMax heta4 hwidthMax
  -- The lower-product supplier is uniform in width, so its candidate is widthMax.
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
  have hN : 2 ≤ N := hN0.trans hNN0
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
  have hcards : (∑ i : Fin 4, ((physicalSupportedStrip width b N
      (manuscriptHalfProductCutoff kappa N) i).card : ℝ)) ≤
      eta * ((N : ℝ) / Real.log (N : ℝ)) := by
    have hsum : (∑ i : Fin 4, ((physicalSupportedStrip width b N
        (manuscriptHalfProductCutoff kappa N) i).card : ℝ)) =
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 0).card : ℝ) +
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 1).card : ℝ) +
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 2).card : ℝ) +
        ((physicalSupportedStrip width b N (manuscriptHalfProductCutoff kappa N) 3).card : ℝ) := by
      simp [Fin.sum_univ_succ, add_assoc]
    rw [hsum]
    nlinarith only [h0, h1, h2, h3]
  have hNreal : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hT : 0 < manuscriptHalfProductCutoff kappa N := by
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (zero_lt_one.trans hNreal) _)
  exact (sum_physicalPairOuterRamp_le_source_card_add_supported_strip_cards
    hNreal hT hwidth).trans (add_le_add_left hcards _)

end

end ImbalancedChen.P4B
