import ImbalancedChen.P1OriginalFourthSavedQ80Total
import ImbalancedChen.P1OriginalFourthPhysicalKernelComparison

/-! The finite family of original limiting row integrals is approached
by one common interior trim and one common positive cap buffer. The
actual old/current Suzuki profiles, including their amplitude, occur
here. This statement is uniform in the later physical mesh choices. -/
namespace ImbalancedChen.P1OriginalFourthTrimmedLimit
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P2OriginalFourthCapProducerInterface P1OriginalPrefixRowDecodeSoundness
open P1OriginalFourthRowGap P1OriginalFourthRowQ80Integral
open P1OriginalFourthAllRowsAdmission P5OriginalFourthFifthSourceInputs
open P1OriginalFourthCommonHistoricalMesh P1OriginalFourthUniformRowMargins
open P1OriginalFourthPhysicalKernelComparison P1FourthIntegralSign
open OriginalU2CoupledRecurrenceSourceOnly (upper A A_pos)
open P1OriginalFourthFourSubintervals (upper_differentiable)

def trimWidth (n : ℕ) : ℝ := 1/((n:ℝ)+1)
def buffer (n : ℕ) : ℝ := min (commonMargin/4) (trimWidth n)
def test (r : FourthWireRow) (n : ℕ) : Point → ℝ :=
  (trimmedBox r.toProducerRow (trimWidth n)).indicator (bufferedRowKernel r.toProducerRow (buffer n))
def testIntegral (r : FourthWireRow) (n : ℕ) : ℝ := ∫ t in box r, test r n t
def testTotal (n : ℕ) : ℝ := (originalFourthWireRows.map (fun r => testIntegral r n)).sum

theorem width_pos (n : ℕ) : 0 < trimWidth n := by unfold trimWidth; positivity
theorem buffer_pos (n : ℕ) : 0 < buffer n := lt_min (div_pos commonMargin_pos (by norm_num)) (width_pos n)
theorem buffer_margin (n : ℕ) : 2*buffer n < commonMargin := by
  have h : buffer n ≤ commonMargin/4 := min_le_left _ _
  linarith only [h,commonMargin_pos]
theorem width_tendsto : Tendsto trimWidth atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
theorem buffer_tendsto : Tendsto buffer atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => commonMargin/4) atTop (𝓝 (commonMargin/4)) := tendsto_const_nhds
  have h := hc.min width_tendsto
  simpa only [buffer,min_eq_right (by linarith only [commonMargin_pos] : 0 ≤ commonMargin/4)] using h

theorem row_mem (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) : r.toProducerRow ∈ originalRows4 :=
  (originalRows4_source _).mpr ⟨r,hr,rfl⟩
theorem all_positive (r : FourthWireRow) (hr : r ∈ originalFourthWireRows)
    (t : Point) (ht : t ∈ r.toProducerRow.box) (i : Fin 4) : 0 < t i := by
  have h := r.toProducerRow.ordered (all_original_rows_geometry r hr) t ht
  fin_cases i <;> linarith only [h.2.1,h.2.2,h.1.2.1,h.1.2.2.1]

theorem trim_measurable (r : FourthWireRow) (d : ℝ) : MeasurableSet (trimmedBox r.toProducerRow d) := by
  change MeasurableSet {t : Point | ∀ i, _}
  rw [show {t : Point | ∀ i, (r.toProducerRow.lower i:ℝ)+d ≤ t i ∧ t i ≤ (r.toProducerRow.upper i:ℝ)-d} =
      ⋂ i : Fin 4, {t : Point | (r.toProducerRow.lower i:ℝ)+d ≤ t i ∧ t i ≤ (r.toProducerRow.upper i:ℝ)-d} by
    ext; simp]
  exact MeasurableSet.iInter (fun i => (measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (measurable_pi_apply i) measurable_const))

def physicalBuffer (r : FourthWireRow) (b : ℝ) (t : Point) : ℝ :=
  4*(upper ((oldCap t-total t)/t 3)-
      upper ((r.toProducerRow.bufferedCandidate b t-total t)/t 3))/(t 0*t 1*t 2*(t 3)^2)

theorem raw_profile (s : ℝ) (t : Point) (hw : 0 < t 3) :
    fourthPlusProfileP1 s t = 4*upper ((s-total t)/t 3)/t 3 := by
  change (2*Real.exp (-Real.eulerMascheroniConstant)/t 3)*
    suzukiContinuousUpperFactor ((s-total t)/t 3) = _
  rw [← P1FourthNearOneKernel.normalization]
  unfold upper
  field_simp [A_pos.ne',hw.ne'] <;> ring

theorem buffered_eq (r : FourthWireRow) (b : ℝ) (t : Point) (h : ∀ i, 0 < t i) :
    bufferedRowKernel r.toProducerRow b t = physicalBuffer r b t := by
  rw [bufferedRowKernel,raw_profile _ _ (h 3),raw_profile _ _ (h 3)]
  unfold physicalBuffer
  simp only [Fin.prod_univ_succ]
  field_simp [(h 0).ne',(h 1).ne',(h 2).ne',(h 3).ne'] <;> ring

theorem zero_buffer (r : FourthWireRow) (t : Point) (h : ∀ i, 0 < t i) :
    bufferedRowKernel r.toProducerRow 0 t = density r t := by
  simp only [buffered_eq r 0 t h,physicalBuffer,ProducerRow.bufferedCandidate,mul_zero,sub_zero,density]

theorem raw_antitone (r : FourthWireRow) (hr : r ∈ originalFourthWireRows)
    {a b : ℝ} (hab : a ≤ b) (hb : 2*b < commonMargin) (t : Point) (ht : t ∈ r.toProducerRow.box) :
    bufferedRowKernel r.toProducerRow b t ≤ bufferedRowKernel r.toProducerRow a t := by
  have hp := all_positive r hr t ht
  have hM := (buffered_row_gates _ (row_mem r hr) b hb t ht).1
  have hs := (r.toProducerRow.residual_range (all_original_rows_geometry r hr) t ht).1
  have hs' := hs.trans_le (residual_mono_level t (hp 3) hM.le)
  have hcap : r.toProducerRow.bufferedCandidate b t ≤ r.toProducerRow.bufferedCandidate a t := by
    unfold ProducerRow.bufferedCandidate
    linarith only [hab]
  have h := rawProfile_antitone_legal t (hp 3) hcap hs'
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left h _) (Finset.prod_nonneg
    (fun i _ => one_div_nonneg.mpr (hp i).le))

theorem buffered_continuous (r : FourthWireRow) (hr : r ∈ originalFourthWireRows)
    (b : ℝ) (hb : 2*b < commonMargin) :
    ContinuousOn (bufferedRowKernel r.toProducerRow b) (Icc (left r) (right r)) := by
  have hp : ContinuousOn (physicalBuffer r b) (Icc (left r) (right r)) := by
    intro t ht
    have h := all_positive r hr t ht
    have ho := (r.toProducerRow.residual_range (all_original_rows_geometry r hr) t ht).1
    have hM := (buffered_row_gates _ (row_mem r hr) b hb t ht).1
    have hn := ho.trans_le (residual_mono_level t (h 3) hM.le)
    have hc : Continuous total := by unfold total; fun_prop
    have h0 := (upper_differentiable ho).continuousAt.comp
      ((old_continuous.sub hc).continuousAt.div (continuous_apply (3:Fin 4)).continuousAt (h 3).ne')
    have hc1 : Continuous (r.toProducerRow.bufferedCandidate b) := (candidate_continuous r).sub continuous_const
    have h1 := (upper_differentiable hn).continuousAt.comp
      ((hc1.sub hc).continuousAt.div (continuous_apply (3:Fin 4)).continuousAt (h 3).ne')
    have hd : Continuous (fun y : Point => y 0*y 1*y 2*(y 3)^2) := by fun_prop
    exact ((continuousAt_const.mul (h0.sub h1)).div hd.continuousAt
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (h 0).ne' (h 1).ne') (h 2).ne') (pow_ne_zero 2 (h 3).ne'))).continuousWithinAt
  exact hp.congr (fun t ht => buffered_eq r b t (all_positive r hr t ht))

theorem test_integrable (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) (n : ℕ) :
    IntegrableOn (test r n) (box r) := by
  have hB : IntegrableOn (bufferedRowKernel r.toProducerRow (buffer n)) (box r) :=
    ((buffered_continuous r hr _ (buffer_margin n)).integrableOn_compact isCompact_Icc).mono_set (box_subset r)
  exact hB.indicator (trim_measurable r _)

theorem buffer_limit (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) (t : Point)
    (ht : t ∈ r.toProducerRow.box) :
    Tendsto (fun n => bufferedRowKernel r.toProducerRow (buffer n) t) atTop (𝓝 (density r t)) := by
  have h := r.toProducerRow.residual_range (all_original_rows_geometry r hr) t ht
  have hc : Tendsto (fun n => (r.toProducerRow.bufferedCandidate (buffer n) t-total t)/t 3)
      atTop (𝓝 ((r.toProducerRow.candidate t-total t)/t 3)) := by
    simpa only [ProducerRow.bufferedCandidate,mul_zero,sub_zero] using
      (((tendsto_const_nhds (x := r.toProducerRow.candidate t)).sub (buffer_tendsto.const_mul 2)).sub
        (tendsto_const_nhds (x := total t))).div_const (t 3)
  have hu := (upper_differentiable (h.1.trans h.2.1)).continuousAt.tendsto.comp hc
  have hd := ((tendsto_const_nhds (x := upper ((oldCap t-total t)/t 3))).sub hu).const_mul 4
  have he := hd.div_const (t 0*t 1*t 2*(t 3)^2)
  exact he.congr' (Eventually.of_forall (fun n => (buffered_eq r _ t (all_positive r hr t ht)).symm))

theorem test_limit (r : FourthWireRow) (hr : r ∈ originalFourthWireRows) :
    Tendsto (testIntegral r) atTop (𝓝 (limitingRowIntegral r)) := by
  have hmeas := measurableSet_logPrimeBox (left r) (right r)
  apply tendsto_integral_of_dominated_convergence (μ := volume.restrict (box r))
    (F := test r) (f := density r) (density r)
    (fun n => (test_integrable r hr n).aestronglyMeasurable) (density_integrable r hr)
  · intro n
    filter_upwards [ae_restrict_mem hmeas] with t ht
    have hbox := box_subset r ht
    have h0 := bufferedRowKernel_nonneg _ (row_mem r hr) 0 (by linarith only [commonMargin_pos]) t hbox
    have hn := bufferedRowKernel_nonneg _ (row_mem r hr) _ (buffer_margin n) t hbox
    have hh := raw_antitone r hr (buffer_pos n).le (buffer_margin n) t hbox
    rw [zero_buffer r t (all_positive r hr t hbox)] at hh h0
    by_cases hit : t ∈ trimmedBox r.toProducerRow (trimWidth n)
    · simpa only [test,indicator_of_mem hit,Real.norm_eq_abs,abs_of_nonneg hn] using hh
    · simpa only [test,indicator_of_notMem hit,norm_zero] using h0
  · filter_upwards [ae_restrict_mem hmeas,ae_restrict_of_ae (ae_box_has_positive_trim r.toProducerRow)]
      with t ht htrim
    obtain ⟨d,hd,htd⟩ := htrim (box_subset r ht)
    apply (buffer_limit r hr t (box_subset r ht)).congr'
    filter_upwards [width_tendsto.eventually (gt_mem_nhds hd)] with n hn
    have hm : t ∈ trimmedBox r.toProducerRow (trimWidth n) :=
      fun i => ⟨by linarith [(htd i).1],by linarith [(htd i).2]⟩
    simp only [test,indicator_of_mem hm]

private theorem list_limit (xs : List FourthWireRow) (h : ∀ r ∈ xs, r ∈ originalFourthWireRows) :
    Tendsto (fun n => (xs.map (fun r => testIntegral r n)).sum) atTop (𝓝 (xs.map limitingRowIntegral).sum) := by
  induction xs with
  | nil => simpa using (show Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0) from tendsto_const_nhds)
  | cons r xs ih =>
    simpa only [List.map_cons,List.sum_cons] using
      (test_limit r (h _ List.mem_cons_self)).add (ih (fun v hv => h _ (List.mem_cons_of_mem _ hv)))

theorem finite_total_limit : Tendsto testTotal atTop (𝓝 (originalFourthWireRows.map limitingRowIntegral).sum) :=
  list_limit _ (fun _ hr => hr)

end
end ImbalancedChen.P1OriginalFourthTrimmedLimit
