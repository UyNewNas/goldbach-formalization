import ImbalancedChen.P2OriginalSixthInnerPrimeRamp
import ImbalancedChen.P4AOriginalElevenProfileQuantization
import ImbalancedChen.ActualPrimeBoxTestFunctions

/-! SOURCE_ONLY / UNEVALUATED / UNCOMPILED.
Genuine target-deleted prime tests of continuous lower approximations to
the original2631-simplex union. The actual finite prime sum is passed to
the existing prime theorem. Only the Lebesgue integral uses null fronts;
the ramp stays zero at the unsupported arithmetic faces and ties.
-/
namespace ImbalancedChen.P2OriginalSixthInnerPrimeTests
noncomputable section
open Set Filter MeasureTheory VariableEnvelope
open scoped Classical BigOperators Topology
open P2OriginalSixthMomentRow (Point cutoff)
open P2OriginalSixthLogArchive (sourceCell)
open P2OriginalSixthPullingUnion (eval originalInnerUnion)
open P2OriginalSixthCompactTrim (trim trim_subset_source eval_continuous)
open P2OriginalSixthInnerPrimeRamp (ramp ramp_bounds continuous_ramp ramp_off_trim ramp_eventually_one)
open P4AOriginalElevenOwnCaps (comparisonTies comparison_ties_null)
open P4AOriginalFull87HistoryCore (width width_pos)
open Certificates.P2OriginalSixthElevenLogSemantics
  (PhysicalCell oldCap newCap S6 oldResidual newResidual coordinateProduct savingKernel sourceIntegral)

def box : Set Point := logPrimeBox (fun _ => cutoff) (fun _ => mu)
def profile (i : Fin 11) (t : Point) : ℝ :=
  max 0 (4/max cutoff (oldCap (sourceCell i) t-S6 t)-
    4/max cutoff (newCap (sourceCell i) t-S6 t))
def test (r : ℕ) (i : Fin 11) (t : Point) : ℝ := profile i t*ramp r i t
def testIntegral (r : ℕ) (i : Fin 11) : ℝ := ∫ t in box,test r i t*(∏ j,1/t j)
def testSum (N r : ℕ) (i : Fin 11) : ℝ :=
  actualPrimeBoxTestSum N (fun _ : Fin 6 => cutoff) (fun _ => mu) (test r i)

theorem continuous_profile (i : Fin 11) : Continuous (profile i) := by
  have ho : Continuous (oldCap (sourceCell i)) := by
    simpa only [P2OriginalSixthCrossCellOwnership.eval_old] using
      (eval_continuous (P2OriginalSixthPhysicalGateRows.old (sourceCell i)))
  have hn : Continuous (newCap (sourceCell i)) :=
    P4AOriginalSixthActionBank.endpoint_continuous (.eleven (sourceCell i))
  have hs : Continuous S6 := by unfold S6 Certificates.P2OriginalSixthElevenLogSemantics.S5; fun_prop
  have hc : 0<cutoff := by norm_num [cutoff]
  exact continuous_const.max ((continuous_const.div (continuous_const.max (ho.sub hs))
    (fun _ => (hc.trans_le (le_max_left _ _)).ne')).sub
    (continuous_const.div (continuous_const.max (hn.sub hs))
      (fun _ => (hc.trans_le (le_max_left _ _)).ne')))

theorem profile_eq_on_source {i : Fin 11} {t : Point} (hc : PhysicalCell (sourceCell i) t) :
    profile i t=primeBoxInitialSavingProfile (oldCap (sourceCell i) t) (newCap (sourceCell i) t) t := by
  have hr := hc.residual_guards
  have hR : cutoff<oldCap (sourceCell i) t-S6 t := hc.compactCutoff.trans hr.2.1
  have hM : cutoff<newCap (sourceCell i) t-S6 t := hR.trans (sub_lt_sub_right hc.positiveGap _)
  have hR0 : 0<oldCap (sourceCell i) t-S6 t := hc.rpos.trans hr.2.1
  have hM0 : 0<newCap (sourceCell i) t-S6 t := hR0.trans (sub_lt_sub_right hc.positiveGap _)
  have hle : 4/(newCap (sourceCell i) t-S6 t)≤4/(oldCap (sourceCell i) t-S6 t) :=
    div_le_div_of_nonneg_left (by norm_num) hR0 (sub_le_sub_right hc.positiveGap.le _)
  rw [profile,max_eq_right hR.le,max_eq_right hM.le,max_eq_right (sub_nonneg.mpr hle),
    P4AOriginalElevenProfileQuantization.profile_eq_reciprocals hR0.ne' hM0.ne']

theorem profile_density {i : Fin 11} {t : Point} (hc : PhysicalCell (sourceCell i) t) :
    profile i t*(∏ j,1/t j)=savingKernel (sourceCell i) t := by
  rw [profile_eq_on_source hc,Certificates.P2OriginalSixthElevenLogSemantics.savingKernel_eq_actual_profile]
  simp only [coordinateProduct,one_div,Finset.prod_inv_distrib,div_eq_mul_inv]

theorem source_subset_box {i : Fin 11} {t : Point} (hc : PhysicalCell (sourceCell i) t) : t∈box := by
  have ho := (P4AOriginalElevenPrimeOccurrence.source_strictAnti hc).antitone
  apply mem_logPrimeBox.mpr
  intro j
  exact ⟨hc.compactCutoff.le.trans (ho (Fin.le_last j)),(ho (Fin.zero_le j)).trans_lt hc.largest⟩

theorem test_bounds (r : ℕ) (i : Fin 11) (t : Point) : 0≤test r i t ∧ test r i t≤profile i t := by
  have hp : 0≤profile i t := le_max_left _ _
  exact ⟨mul_nonneg hp (ramp_bounds r i t).1,
    (mul_le_mul_of_nonneg_left (ramp_bounds r i t).2 hp).trans_eq (mul_one _)⟩

theorem continuous_test (r : ℕ) (i : Fin 11) : Continuous (test r i) :=
  (continuous_profile i).mul (continuous_ramp r i)

theorem test_off_trim (r : ℕ) (i : Fin 11) {t : Point} (ht : t∉trim i (width r)) : test r i t=0 := by
  rw [test,ramp_off_trim r i ht,mul_zero]

theorem testIntegral_tendsto (i : Fin 11) :
    Tendsto (fun r => testIntegral r i) atTop (𝓝 (sourceIntegral (sourceCell i) (originalInnerUnion i))) := by
  let dens := fun t : Point => ∏ j,1/t j
  have hties : ∀ᵐ t : Point ∂volume,t∉comparisonTies := by
    rw [ae_iff]
    simpa only [not_not] using comparison_ties_null
  have hlim := tendsto_integral_of_dominated_convergence (μ:=volume.restrict box)
    (F:=fun r t => test r i t*dens t)
    (f:=(originalInnerUnion i).indicator (savingKernel (sourceCell i)))
    (fun t => profile i t*dens t)
    (fun r => (integrableOn_logPrimeBox_test_cube (by norm_num [cutoff]) (test r i)
      (continuous_test r i).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_test_cube (by norm_num [cutoff]) (profile i) (continuous_profile i).continuousOn)
    (fun r => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox (fun _ : Fin 6 => cutoff) (fun _ => mu))] with t ht
      have hd : 0≤dens t := Finset.prod_nonneg (fun j _ =>
        (one_div_pos.mpr ((by norm_num [cutoff] : (0:ℝ)<cutoff).trans_le ((mem_logPrimeBox.mp ht j).1))).le)
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (test_bounds r i t).1 hd)]
      exact mul_le_mul_of_nonneg_right (test_bounds r i t).2 hd)
    (by
      filter_upwards [ae_restrict_of_ae (P2OriginalSixthInnerInterior.original_union_ae_interior i),
        ae_restrict_of_ae (P2OriginalSixthInnerPhysicalCell.original_inner_union_ae_physicalCell i),
        ae_restrict_of_ae hties] with t hinside hsource htie
      apply tendsto_const_nhds.congr'
      by_cases ht : t∈originalInnerUnion i
      · filter_upwards [ramp_eventually_one i (hinside ht) (hsource ht) htie] with r hr
        rw [indicator_of_mem ht,test,hr,mul_one]
        exact (profile_density (hsource ht)).symm
      · filter_upwards with r
        have htrim : t∉trim i (width r) := fun hh => ht hh.1
        rw [indicator_of_notMem ht,test_off_trim r i htrim,zero_mul])
  have hset : box∩originalInnerUnion i=ᵐ[volume] originalInnerUnion i := by
    filter_upwards [P2OriginalSixthInnerPhysicalCell.original_inner_union_ae_physicalCell i] with t ht
    apply propext
    exact ⟨fun h => h.2,fun h => ⟨source_subset_box (ht h),h⟩⟩
  have hi : (∫ t in box,(originalInnerUnion i).indicator (savingKernel (sourceCell i)) t)=
      sourceIntegral (sourceCell i) (originalInnerUnion i) := by
    rw [setIntegral_indicator (P2OriginalSixthOwnedPhysicalIntegral.inner_measurable i)]
    exact setIntegral_congr_set hset
  simpa only [testIntegral,dens,hi] using hlim

theorem testSum_tendsto (r : ℕ) (i : Fin 11) :
    Tendsto (fun N => testSum N r i) atTop (𝓝 (testIntegral r i)) :=
  tendsto_actualPrimeBoxTestSum_cube (by norm_num [cutoff]) (by norm_num [cutoff,mu])
    (test r i) (continuous_test r i).continuousOn

theorem exists_continuous_original_G7_floor (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ r : ℕ, (1208544915921356327515701:ℝ)/(2:ℝ)^96-epsilon<∑ i : Fin 11,testIntegral r i := by
  have hlim := tendsto_finsetSum (Finset.univ : Finset (Fin 11)) (fun i _ => testIntegral_tendsto i)
  have hfloor := P2OriginalSixthPullingUnion.original_all2631_inner_union_floor
  have hs : (1208544915921356327515701:ℝ)/(2:ℝ)^96-epsilon<
      ∑ i : Fin 11,sourceIntegral (sourceCell i) (originalInnerUnion i) := by linarith
  exact (hlim.eventually (lt_mem_nhds hs)).exists

end
end ImbalancedChen.P2OriginalSixthInnerPrimeTests
