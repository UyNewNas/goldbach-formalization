import ImbalancedChen.P4AOriginalFull87EighthKernelControl
import ImbalancedChen.ActualPrimeBoxTestFunctions
import ImbalancedChen.AffinePrimeGates

/-! Continuous lower approximations on the original strict sources. A
single trim index precedes all policies and all prime targets. No finite
atom whose contribution has unknown sign is discarded by this argument. -/
namespace ImbalancedChen.P4AOriginalFull87SourcePrimeTests
noncomputable section
open scoped Classical BigOperators Topology
open Filter Set MeasureTheory VariableEnvelope
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto slack)
open P4AOriginalFull87StrictActionTrim
open P4AOriginalFull87EighthKernelControl

abbrev box : Set Point := logPrimeBox (fun _ => cutoff) (fun _ => mu)
def cellIntegral (c : Cell) : ℝ := ∫ t in sourceSet c, kernel c t

theorem source_subset_box (c : Cell) : sourceSet c ⊆ box := by
  intro t ht
  have hs := source_basic ht
  have ha := (Fin.strictAnti_iff_succ_lt.mpr hs.2.2.2).antitone
  exact mem_logPrimeBox.mpr (fun i =>
    ⟨(source_coordinate_lower ht i).le, (ha (Fin.zero_le i)).trans_lt hs.1⟩)

/-- The three lists are exactly those entering the existing licensed eighth trim. -/
abbrev Gate (c : Cell) := Fin 7 ⊕ (Fin (rowCount c) ⊕ Margin)

def gate (c : Cell) : Gate c → Point → ℝ
  | .inl j => fun t => slack t j
  | .inr (.inl j) => rowValue c j
  | .inr (.inr j) => fun t => actionSlack c t j

theorem continuous_gate (c : Cell) (g : Gate c) : Continuous (gate c g) := by
  rcases g with j | (j | j)
  · exact P4AOriginalFull87HistoryCore.slack_continuous j
  · exact rowValue_continuous c j
  · exact actionSlack_continuous c j

theorem source_gate_pos {c : Cell} {t : Point} (hs : Source c t) (g : Gate c) :
    0 < gate c g t := by
  rcases g with j | (j | j)
  · exact P4AOriginalFull87HistoryCore.source_slack_pos hs j
  · exact (source_iff_rows _ _).mp hs j
  · exact source_actionSlack_pos hs j

private theorem mem_trim_of_gates {r : ℕ} {c : Cell} {t : Point} (ht : t ∈ box)
    (h : ∀ g : Gate c, width r ≤ gate c g t) : t ∈ trim c (width r) := by
  have hb := mem_logPrimeBox.mp ht
  apply (mem_trim c _ t).mpr
  refine ⟨(P4AOriginalFull87HistoryCore.mem_core _ t).mpr
    ⟨fun i => cutoff_pos.le.trans (hb i).1, fun i => (hb i).2.le,
      fun j => h (.inl j)⟩, fun j => h (.inr (.inl j)), fun j => h (.inr (.inr j))⟩

def ramp (r : ℕ) (c : Cell) (t : Point) : ℝ :=
  ∏ g : Gate c, affinePrimeClamp (gate c g t / width r - 1)

theorem continuous_ramp (r : ℕ) (c : Cell) : Continuous (ramp r c) :=
  continuous_finsetProd _ (fun g _ => continuous_affinePrimeClamp.comp
    (((continuous_gate c g).div_const _).sub continuous_const))

theorem ramp_bounds (r : ℕ) (c : Cell) (t : Point) :
    0 ≤ ramp r c t ∧ ramp r c t ≤ 1 :=
  ⟨Finset.prod_nonneg (fun _ _ => (affinePrimeClamp_bounds _).1),
    Finset.prod_le_one (fun _ _ => (affinePrimeClamp_bounds _).1)
      (fun _ _ => (affinePrimeClamp_bounds _).2)⟩

theorem ramp_off_trim (r : ℕ) (c : Cell) {t : Point} (hb : t ∈ box)
    (ht : t ∉ trim c (width r)) : ramp r c t = 0 := by
  obtain ⟨g, hg⟩ : ∃ g : Gate c, gate c g t < width r := by
    by_contra! h
    exact ht (mem_trim_of_gates hb h)
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  apply affinePrimeClamp_eq_zero
  have h := (div_lt_one (width_pos r)).mpr hg
  linarith

theorem ramp_eventually_one {c : Cell} {t : Point} (hs : Source c t) :
    ∀ᶠ r in atTop, ramp r c t = 1 := by
  have h : ∀ᶠ r : ℕ in atTop, ∀ g : Gate c, width r < gate c g t / 2 := by
    apply eventually_all.mpr
    intro g
    exact width_tendsto.eventually (gt_mem_nhds (half_pos (source_gate_pos hs g)))
  filter_upwards [h] with r hr
  apply Finset.prod_eq_one
  intro g _
  apply affinePrimeClamp_eq_one
  have hg : 2 ≤ gate c g t / width r := (le_div_iff₀ (width_pos r)).mpr (by linarith [hr g])
  linarith

/-- Ordinary profile before the reciprocal coordinates. Clamping extends
it continuously off the sources without changing its value on them. -/
def profile (c : Cell) (t : Point) : ℝ :=
  max 0 (4 / max cutoff (comparison c t - total t) - 4 / max cutoff (newCap c t - total t))

theorem continuous_profile (c : Cell) : Continuous (profile c) := by
  have hS : Continuous total := by unfold total; fun_prop
  exact continuous_const.max ((continuous_const.div
    (continuous_const.max ((comparison_continuous c).sub hS))
    (fun _ => (cutoff_pos.trans_le (le_max_left _ _)).ne')).sub
    (continuous_const.div (continuous_const.max ((newCap_continuous c).sub hS))
      (fun _ => (cutoff_pos.trans_le (le_max_left _ _)).ne')))

theorem profile_eq_on_source {c : Cell} {t : Point} (hs : Source c t) :
    profile c t = 4 / (comparison c t - total t) - 4 / (newCap c t - total t) := by
  have h := source_residual_range hs
  have hR := h.1.trans h.2.1
  have hM := hR.trans (sub_lt_sub_right h.2.2.1 _)
  have hle := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 4)
    (cutoff_pos.trans hR) (sub_le_sub_right h.2.2.1.le _)
  rw [profile, max_eq_right hR.le, max_eq_right hM.le, max_eq_right (sub_nonneg.mpr hle)]

theorem profile_density {c : Cell} {t : Point} (hs : Source c t) :
    profile c t * (∏ i, 1 / t i) = kernel c t := by
  have h := source_residual_range hs
  have hR := cutoff_pos.trans (h.1.trans h.2.1)
  have hM := hR.trans (sub_lt_sub_right h.2.2.1 _)
  rw [profile_eq_on_source hs, kernel, residual_eq_reciprocal _ _ _ _ hR.ne' hM.ne'
    (source_product_lower hs).2.ne']
  simp only [one_div, Finset.prod_inv_distrib, product, div_eq_mul_inv]
  ring

def test (r : ℕ) (c : Cell) (t : Point) : ℝ := profile c t * ramp r c t
def testIntegral (r : ℕ) (c : Cell) : ℝ := ∫ t in box, test r c t * ∏ i, 1 / t i
def testSum (N r : ℕ) (c : Cell) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 8 => cutoff) (fun _ => mu) (test r c)

theorem test_bounds (r : ℕ) (c : Cell) (t : Point) : 0 ≤ test r c t ∧ test r c t ≤ profile c t :=
  ⟨mul_nonneg (le_max_left _ _) (ramp_bounds r c t).1,
    (mul_le_mul_of_nonneg_left (ramp_bounds r c t).2 (le_max_left _ _)).trans_eq (mul_one _)⟩

theorem continuous_test (r : ℕ) (c : Cell) : Continuous (test r c) :=
  (continuous_profile c).mul (continuous_ramp r c)

theorem test_off_trim (r : ℕ) (c : Cell) {t : Point} (hb : t ∈ box)
    (ht : t ∉ trim c (width r)) : test r c t = 0 := by
  rw [test, ramp_off_trim r c hb ht, mul_zero]

theorem testIntegral_tendsto (c : Cell) : Tendsto (fun r => testIntegral r c) atTop (𝓝 (cellIntegral c)) := by
  let dens := fun t : Point => ∏ i, 1 / t i
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict box)
    (F := fun r t => test r c t * dens t)
    (f := (sourceSet c).indicator (kernel c)) (fun t => profile c t * dens t)
    (fun r => (integrableOn_logPrimeBox_test_cube cutoff_pos (test r c)
      (continuous_test r c).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_test_cube cutoff_pos (profile c) (continuous_profile c).continuousOn)
    (fun r => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin 8 => cutoff) (fun _ => mu))] with t ht
      have hd : 0 ≤ dens t := Finset.prod_nonneg (fun i _ =>
        (one_div_pos.mpr (cutoff_pos.trans_le ((mem_logPrimeBox.mp ht i).1))).le)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (test_bounds r c t).1 hd)]
      exact mul_le_mul_of_nonneg_right (test_bounds r c t).2 hd)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin 8 => cutoff) (fun _ => mu))] with t ht
      apply tendsto_const_nhds.congr'
      by_cases hs : Source c t
      · filter_upwards [ramp_eventually_one hs] with r hr
        rw [indicator_of_mem (show t ∈ sourceSet c from hs), test, hr, mul_one]
        exact (profile_density hs).symm
      · filter_upwards with r
        have htrim : t ∉ trim c (width r) := fun hm => hs (trim_subset_source c (width_pos r) hm)
        rw [indicator_of_notMem (show t ∉ sourceSet c from hs), test_off_trim r c ht htrim, zero_mul])
  have hi : (∫ t in box, (sourceSet c).indicator (kernel c) t) = cellIntegral c := by
    rw [setIntegral_indicator (sourceSet_measurable c), inter_eq_right.mpr (source_subset_box c)]
    rfl
  simpa only [hi, testIntegral, dens] using hlim

theorem testSum_tendsto (r : ℕ) (c : Cell) :
    Tendsto (fun N => testSum N r c) atTop (𝓝 (testIntegral r c)) :=
  tendsto_actualPrimeBoxTestSum_cube cutoff_pos (by norm_num [cutoff, mu])
    (test r c) (continuous_test r c).continuousOn

end
end ImbalancedChen.P4AOriginalFull87SourcePrimeTests
