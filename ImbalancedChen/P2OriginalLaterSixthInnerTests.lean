import ImbalancedChen.P4AOriginalLaterSixthPriorGeometry
import ImbalancedChen.P2OriginalSixthInnerPrimeRamp
import ImbalancedChen.P4AOriginalElevenProfileQuantization
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-! A continuous lower test for each of the twenty-one original later
physical simplex unions. Arithmetic atoms on an affine wall remain in
the full signed sum. Only the limiting integral removes null frontiers. -/
namespace ImbalancedChen.P2OriginalLaterSixthInnerTests
noncomputable section
open Set Filter MeasureTheory VariableEnvelope
open scoped Classical BigOperators Topology
open P2OriginalLaterSixthKernel
open P2OriginalLaterSixthArchive (Individual physicalRow rowVertices)
open P2OriginalLaterSixthOwnedIntegral (inner support nonneg_on)
open P2OriginalLaterSixthSourceIntegral (owned domain domain_open continuous_eval)
open P2OriginalLaterSixthStageMass (inner_compact owned_measurable)
open P4AOriginalLaterSixthPriorGeometry (regular regular_ae regular_open)
open P2OriginalSixthInnerPrimeRamp (insideDistance insideDistance_zero insideDistance_pos continuous_insideDistance)
open P4AOriginalFull87HistoryCore (width width_pos width_tendsto)
open P2OriginalSixthSimplexMoments (Point)
open P2OriginalSixthMomentRow (cutoff cutoffQ cutoffQ_cast)
open Certificates.P2OriginalSixthElevenLogSemantics (S6 S5)
open P2OriginalLaterSixthCorrections (eval_diff eval_total)
open P4AOriginalElevenProfileQuantization (profile_eq_reciprocals)

def region (i : Piece) : Set Point := interior (inner i)∩domain i∩regular
def trim (i : Piece) (x : ℝ) : Set Point := inner i∩{t | x≤insideDistance (region i) t}
def box : Set Point := logPrimeBox (fun _=>cutoff) (fun _=>(1/5:ℝ))
def ramp (r : ℕ) (i : Piece) (t : Point) := affinePrimeClamp (insideDistance (region i) t/width r-1)
def profile (i : Piece) (t : Point) : ℝ := max 0
  (4/max cutoff (eval (lower i) t-S6 t)-4/max cutoff (eval (upper i) t-S6 t))
def test (r : ℕ) (i : Piece) (t : Point) := profile i t*ramp r i t
def testIntegral (r : ℕ) (i : Piece) := ∫ t in box,test r i t*(∏ j,1/t j)
def testSum (N r : ℕ) (i : Piece) := actualPrimeBoxTestSum N
  (fun _ : Fin 6=>cutoff) (fun _=>(1/5:ℝ)) (test r i)

theorem region_open (i : Piece) : IsOpen (region i) :=
  (isOpen_interior.inter (domain_open i)).inter regular_open
theorem trim_compact (i : Piece) (x : ℝ) : IsCompact (trim i x) :=
  (inner_compact i).inter_right (isClosed_le continuous_const (continuous_insideDistance _))
theorem trim_region {i : Piece} {x : ℝ} (hx : 0<x) {t : Point} (ht : t∈trim i x) :
    t∈owned i ∧ t∈regular := by
  have h : t∈region i := by
    by_contra hn
    have ha := ht.2
    rw [insideDistance_zero hn] at ha
    linarith
  exact ⟨⟨ht.1,h.1.2⟩,h.2⟩

theorem region_ae (i : Piece) : owned i=ᵐ[volume] region i := by
  let w : Set Point := ⋃ s : Individual i,frontier (support i s)
  have hw : volume w=0 := measure_iUnion_null (fun s =>
    (P2OriginalSixthInnerInterior.physical_support_convex _ _).addHaar_frontier volume)
  have hf : ∀ᵐ t : Point ∂volume,t∉w := by rw [ae_iff];simpa only [not_not] using hw
  rw [Filter.eventuallyEq_set]
  filter_upwards [hf,regular_ae] with t ht hreg
  change t∈inner i∩domain i ↔ t∈(interior (inner i)∩domain i)∩regular
  refine ⟨fun hh=>⟨⟨?_,hh.2⟩,hreg⟩,fun hh=>⟨interior_subset hh.1.1,hh.1.2⟩⟩
  obtain ⟨s,hs⟩ := mem_iUnion.mp hh.1
  apply interior_mono (show support i s⊆inner i from fun x hx=>mem_iUnion.mpr ⟨s,hx⟩)
  by_contra hn
  apply ht
  refine mem_iUnion.mpr ⟨s,?_⟩
  rw [frontier,(P2OriginalSixthSimplexMoments.support_compact _ _).isClosed.closure_eq]
  exact ⟨hs,hn⟩

theorem owned_subset_box {i : Piece} {t : Point} (ht : t∈owned i) : t∈box := by
  obtain ⟨hx,_,hr,ho⟩ := P4AOriginalSixthSquareRows.later_source_basic (action i) t ht.2.1
  exact mem_logPrimeBox.mpr (fun j=>⟨hr.le.trans (ho.antitone (Fin.le_last j)),
    (ho.antitone (Fin.zero_le j)).trans_lt (hx.trans (by norm_num))⟩)

theorem inner_factors (i : Piece) {t : Point} (ht : t∈inner i) :
    cutoff≤eval (lower i) t-S6 t ∧ cutoff≤eval (upper i) t-S6 t ∧ eval (lower i) t≤eval (upper i) t := by
  obtain ⟨s,hs⟩ := mem_iUnion.mp ht
  let r := physicalRow i s
  have h (j : Fin 8) : cutoff≤eval (factorPlane i j) t := by
    have hh := (P2OriginalSixthMomentRow.row_factor_bounds r.toRow hs j).1
    change cutoff≤P2OriginalSixthSimplexMoments.interpolate
      (fun k=>(evalQ (factorPlane i j) (r.vertices k):ℝ)) (P2OriginalSixthMomentRow.rowCoordinates r.toRow t) at hh
    rwa [physical_eval r] at hh
  have hg := nonneg_on i s (gapPlane i) r.gap_nonneg hs
  rw [gapPlane,eval_diff] at hg
  exact ⟨by simpa [factorPlane,eval_diff,eval_total] using h 0,
    by simpa [factorPlane,eval_diff,eval_total] using h 1,sub_nonneg.mp hg⟩

theorem profile_on_inner (i : Piece) {t : Point} (ht : t∈inner i) :
    profile i t=primeBoxInitialSavingProfile (eval (lower i) t) (eval (upper i) t) t := by
  obtain ⟨hL,hU,hLU⟩ := inner_factors i ht
  have hc : 0<cutoff := by norm_num [cutoff]
  have hrec := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) (hc.trans_le hL) (sub_le_sub_right hLU (S6 t))
  rw [profile,max_eq_right hL,max_eq_right hU,max_eq_right (sub_nonneg.mpr hrec),
    profile_eq_reciprocals (hc.trans_le hL).ne' (hc.trans_le hU).ne']

theorem continuous_profile (i : Piece) : Continuous (profile i) := by
  have hS : Continuous S6 := by unfold S6 S5;fun_prop
  have hc : 0<cutoff := by norm_num [cutoff]
  exact continuous_const.max ((continuous_const.div
    (continuous_const.max ((continuous_eval (lower i)).sub hS)) (fun _=>(hc.trans_le (le_max_left _ _)).ne')).sub
    (continuous_const.div (continuous_const.max ((continuous_eval (upper i)).sub hS))
      (fun _=>(hc.trans_le (le_max_left _ _)).ne')))
theorem continuous_test (r : ℕ) (i : Piece) : Continuous (test r i) :=
  (continuous_profile i).mul (continuous_affinePrimeClamp.comp
    (((continuous_insideDistance (region i)).div_const _).sub continuous_const))

theorem test_bounds (r : ℕ) (i : Piece) (t : Point) : 0≤test r i t ∧ test r i t≤profile i t := by
  have h := affinePrimeClamp_bounds (insideDistance (region i) t/width r-1)
  exact ⟨mul_nonneg (le_max_left _ _) h.1,(mul_le_mul_of_nonneg_left h.2
    (show 0≤profile i t from le_max_left _ _)).trans_eq (mul_one _)⟩
theorem test_off_trim (r : ℕ) (i : Piece) {t : Point} (ht : t∉trim i (width r)) : test r i t=0 := by
  have hD : insideDistance (region i) t<width r := by
    by_contra! hh
    have hr : t∈region i := by
      by_contra hn
      rw [insideDistance_zero hn] at hh
      exact (not_le_of_gt (width_pos r)) hh
    exact ht ⟨interior_subset hr.1.1,hh⟩
  have hz : ramp r i t=0 := affinePrimeClamp_eq_zero (by
    have hb := (div_lt_one (width_pos r)).mpr hD;linarith)
  simp only [test,hz,mul_zero]

theorem testSum_tendsto (r : ℕ) (i : Piece) :
    Tendsto (fun N=>testSum N r i) atTop (𝓝 (testIntegral r i)) :=
  tendsto_actualPrimeBoxTestSum_cube (by norm_num [cutoff]) (by norm_num [cutoff])
    (test r i) (continuous_test r i).continuousOn

theorem testIntegral_tendsto (i : Piece) :
    Tendsto (fun r=>testIntegral r i) atTop (𝓝 (sourceIntegral i (owned i))) := by
  let den := fun t : Point=>∏ j,1/t j
  have hh := tendsto_integral_of_dominated_convergence (μ:=volume.restrict box)
    (F:=fun r t=>test r i t*den t) (f:=(owned i).indicator (kernel i))
    (fun t=>profile i t*den t)
    (fun r=>(integrableOn_logPrimeBox_test_cube (by norm_num [cutoff]) (test r i)
      (continuous_test r i).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_test_cube (by norm_num [cutoff]) (profile i) (continuous_profile i).continuousOn)
    (fun r=>by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox (fun _ : Fin 6=>cutoff) (fun _=>(1/5:ℝ)))] with t ht
      have hd : 0≤den t := Finset.prod_nonneg (fun j _=>(one_div_pos.mpr
        ((by norm_num [cutoff] : 0<cutoff).trans_le ((mem_logPrimeBox.mp ht j).1))).le)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (test_bounds r i t).1 hd)]
      exact mul_le_mul_of_nonneg_right (test_bounds r i t).2 hd)
    (by
      filter_upwards [ae_restrict_of_ae (region_ae i)] with t h
      apply tendsto_const_nhds.congr'
      by_cases ht : t∈owned i
      · have hd := insideDistance_pos (U:=region i) (by rw [(region_open i).interior_eq];exact h.mp ht)
        filter_upwards [width_tendsto.eventually (gt_mem_nhds (half_pos hd))] with r hr
        have hp : ramp r i t=1 := affinePrimeClamp_eq_one (by
          have hh : 2≤insideDistance (region i) t/width r := (le_div_iff₀ (width_pos r)).mpr (by linarith)
          linarith)
        rw [indicator_of_mem ht,test,hp,mul_one,profile_on_inner i ht.1,P2OriginalLaterSixthCorrections.kernel_profile]
        simp only [den,one_div,Finset.prod_inv_distrib,div_eq_mul_inv]
      · filter_upwards with r
        have hn : t∉trim i (width r) := fun hh=>ht (trim_region (width_pos r) hh).1
        rw [indicator_of_notMem ht,test_off_trim r i hn,zero_mul])
  have hi : (∫ t in box,(owned i).indicator (kernel i) t)=sourceIntegral i (owned i) := by
    rw [setIntegral_indicator (owned_measurable i),Set.inter_eq_right.mpr (fun _ ht=>owned_subset_box ht)] <;> rfl
  simpa only [testIntegral,den,hi] using hh

theorem original_floor_tests (eps : ℝ) (he : 0<eps) :
    ∃ r : ℕ,(∑ j : Fin 7,currentUpperEighteenGains ⟨7+j.val,by omega⟩)-eps<∑ i : Piece,testIntegral r i := by
  have h := P2OriginalLaterSixthStageMass.seven_slots_le_eight_stage_integrals
  rw [P2OriginalLaterSixthStageMass.integral_stages] at h
  have hlim := tendsto_finsetSum (Finset.univ : Finset Piece) (fun i _=>testIntegral_tendsto i)
  exact (hlim.eventually (lt_mem_nhds (show (∑ j : Fin 7,currentUpperEighteenGains ⟨7+j.val,by omega⟩)-eps<
    ∑ i : Piece,sourceIntegral i (owned i) by linarith))).exists

end
end ImbalancedChen.P2OriginalLaterSixthInnerTests
