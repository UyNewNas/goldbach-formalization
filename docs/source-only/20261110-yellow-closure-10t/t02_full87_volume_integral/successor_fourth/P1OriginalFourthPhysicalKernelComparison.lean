import ImbalancedChen.P1OriginalFourthActualSourceCoverage

/-! SOURCE_ONLY / UNCOMPILED.
The original row density with only the true 2e endpoint buffer is below
the actual active-branch kernel. Gamma is bounded ABOVE by L, so its
approximation error costs nothing in this directed lower comparison.
The current maximum retains every row, including overlaps. This theorem
does not add their integrals or assert pairwise disjointness.
-/
namespace ImbalancedChen.P1OriginalFourthPhysicalKernelComparison
noncomputable section
open scoped Classical BigOperators
open Set VariableEnvelope HistoricalThirdCoarse
open P2OriginalFourthCapProducerInterface P1OriginalCoarseContinuation
open P5OriginalFourthFifthSourceInputs
open P1OriginalFourthAllRowsAdmission P1OriginalFourthUniformRowMargins
open P1OriginalVariableFourthContinuation
open P1OriginalVariableFourthFullSourceActivation
open P1OriginalVariableFourthActiveOnly P1OriginalVariableFourthFullActiveIntegral
open P1FourthNearOneKernel P1FourthFullCellIntegral P1FourthIntegralSign

def bufferedRowKernel (r : ProducerRow) (e : ℝ) (t : Point) : ℝ :=
  (fourthPlusProfileP1 (oldCap t) t - fourthPlusProfileP1 (r.bufferedCandidate e t) t) *
    ∏ i, 1 / t i

theorem original_row_coordinate_cutoff (r : ProducerRow) (hr : r ∈ originalRows4)
    (t : Point) (ht : t ∈ r.box) (i : Fin 4) : (3 / 200 : ℝ) ≤ t i := by
  have hg := originalRows4_geometry r hr
  have ho := r.ordered hg t ht
  have hc : (3 / 200 : ℝ) ≤ t 3 := by
    have hR : (3 / 200 : ℝ) ≤ (r.lower 3 : ℝ) := by exact_mod_cast hg.2.2.2.2.1
    exact hR.trans (ht.1 3)
  fin_cases i <;> linarith [ho.1.2.1,ho.1.2.2.1,ho.2.2]

private theorem raw_profile_abs_le (r : ProducerRow) (hr : r ∈ originalRows4)
    (t : Point) (ht : t ∈ r.box) (lambda : ℝ) (hl : 1 < residual lambda t) :
    |fourthPlusProfileP1 lambda t| ≤ 4 / (3 / 200 : ℝ) := by
  have hc := original_row_coordinate_cutoff r hr t ht 3
  have hp : (0 : ℝ) < t (Fin.last 3) := by change 0 < t 3; linarith
  have hlegal : t ∈ legal (3 / 200) lambda := by
    refine ⟨hc,?_⟩
    have hh := (one_lt_div hp).mp hl
    linarith
  have heq : density lambda t = fourthPlusProfileP1 lambda t := density_eq_actual lambda t hl
  rw [← heq]
  exact abs_density_le (by norm_num : (0 : ℝ) < 3 / 200) hlegal

/-- One fixed bounded density dominates every original row and all
small buffered endpoints. Its support is the original bounded row union.
This supplies the elementary majorant for the separate G1 limit supplier.
-/
theorem buffered_row_kernel_abs_le (r : ProducerRow) (hr : r ∈ originalRows4)
    (e : ℝ) (he : 2*e < commonMargin) (t : Point) (ht : t ∈ r.box) :
    |bufferedRowKernel r e t| ≤ (8 / (3 / 200 : ℝ)) * (1 / (3 / 200 : ℝ)) ^ 4 := by
  have ho := r.ordered (originalRows4_geometry r hr) t ht
  have hlevel := (buffered_row_gates r hr e he t ht).1
  have hlegal := (r.residual_range (originalRows4_geometry r hr) t ht).1
  have hnewLegal := hlegal.trans_le (residual_mono_level t ho.2.1 hlevel.le)
  have hL := raw_profile_abs_le r hr t ht (oldCap t) hlegal
  have hM := raw_profile_abs_le r hr t ht (r.bufferedCandidate e t) hnewLegal
  have hw0 : 0 ≤ ∏ i : Fin 4, 1 / t i :=
    Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr
      ((by norm_num : (0 : ℝ) < 3 / 200).trans_le (original_row_coordinate_cutoff r hr t ht i)).le)
  have hw : (∏ i : Fin 4, 1 / t i) ≤ (1 / (3 / 200 : ℝ)) ^ 4 := by
    calc
      (∏ i : Fin 4, 1 / t i) ≤ ∏ _i : Fin 4, (1 / (3 / 200 : ℝ)) := by
        apply Finset.prod_le_prod
        · intro i _
          exact one_div_nonneg.mpr
            ((by norm_num : (0 : ℝ) < 3 / 200).trans_le (original_row_coordinate_cutoff r hr t ht i)).le
        · intro i _
          exact one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3 / 200)
            (original_row_coordinate_cutoff r hr t ht i)
      _ = _ := by simp
  unfold bufferedRowKernel
  rw [abs_mul,abs_of_nonneg hw0]
  apply mul_le_mul ?_ hw hw0 (by norm_num)
  exact (abs_sub _ _).trans (by linarith)

theorem bufferedRowKernel_nonneg (r : ProducerRow) (hr : r ∈ originalRows4)
    (e : ℝ) (he : 2*e < commonMargin) (t : Point) (ht : t ∈ r.box) :
    0 ≤ bufferedRowKernel r e t := by
  have ho := r.ordered (originalRows4_geometry r hr) t ht
  have hlevel := (buffered_row_gates r hr e he t ht).1
  have hlegal := (r.residual_range (originalRows4_geometry r hr) t ht).1
  have hprofile := rawProfile_antitone_legal t ho.2.1 hlevel.le hlegal
  apply mul_nonneg (sub_nonneg.mpr hprofile)
  apply Finset.prod_nonneg
  intro i _
  have hpos : 0 < t i := by
    fin_cases i <;> linarith [ho.1.1,ho.1.2.1,ho.1.2.2.1,ho.2.1,ho.2.2]
  exact one_div_nonneg.mpr hpos.le

/-- Direct comparison on the GENUINE physical support; the old profile
has its true legal residual >1, proved from the actual third cube gate.
No caller supplies a density, integral or ideal-kernel licence.
-/
theorem buffered_row_kernel_le_actual_branch
    (e : ℚ) (he : 0 ≤ e) (heM : 2*(e : ℝ) < commonMargin)
    (chi : ℝ) (m : ℕ) (omega : ℝ) (label : Label m)
    (hl : label ∈ activeAdoptedLabels (e : ℝ) chi m)
    (r : ProducerRow) (hr : r ∈ originalRows4) (t : Point)
    (ht : t ∈ r.box) (hs : t ∈ positiveActiveCell e chi m omega label) :
    bufferedRowKernel r (e : ℝ) t ≤
      branchRawKernel e chi m label originalRows4 originalAdmission4 t := by
  have ho := r.ordered (originalRows4_geometry r hr) t ht
  have ha := (mem_activeAdoptedLabels (e : ℝ) chi m label).mp hl
  have hseed : branchSeed (e : ℝ) chi m label = (thirdCellExponent e m label.1 : ℝ) := by
    rw [branchSeed,if_pos ha,cast_thirdCellExponent]
  have ht3 := mem_logPrimeMeshCell_historicalPrefixProject (by omega : 3 ≤ 4) hs.2.1.1
  have hb := inBox_of_cell ht3
  change (box m (historicalPrefixProject (by omega : 3 ≤ 4) label.1)).InBox
    (t 0) (t 1) (t 2) at hb
  have hseedL : branchSeed (e : ℝ) chi m label ≤ oldCap t := by
    rw [hseed]
    exact original_third_exponent_le_oldCap e he m label.1 t hb ho.1
  have hgate := (HistoricalThirdCoarse.P1OriginalFourth.mem_gateRegion _ _ _).mp hs.2.2.1
  have hcube : oldCube.eval t < branchSeed (e : ℝ) chi m label := by
    simpa only [oldCube_eval] using hgate.2.2.2
  have hsum : (∑ i : Fin 4, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp only [Fin.sum_univ_succ]
    ring
  have hlegal : 1 < residual (branchSeed (e : ℝ) chi m label) t := by
    apply (one_lt_div ho.2.1).mpr
    rw [hsum]
    rw [oldCube_eval] at hcube
    linarith [ho.2.2]
  have hleft := rawProfile_antitone_legal t ho.2.1 hseedL hlegal
  have hmax : r.bufferedCandidate (e : ℝ) t ≤
      producerProfile4 (e : ℝ) originalRows4 originalAdmission4
        (branchSeed (e : ℝ) chi m label) t := by
    obtain ⟨raw,hm,rfl⟩ := (originalRows4_source r).mp hr
    exact original_candidate_le_actual_profile (e : ℝ) _ raw hm t ht
  have hbuffer := (buffered_row_gates r hr (e : ℝ) heM t ht).1
  have hbufferLegal : 1 < residual (r.bufferedCandidate (e : ℝ) t) t :=
    hlegal.trans_le (residual_mono_level t ho.2.1 (hseedL.trans hbuffer.le))
  have hright := rawProfile_antitone_legal t ho.2.1 hmax hbufferLegal
  have hweight : 0 ≤ ∏ i : Fin 4, 1 / t i :=
    Finset.prod_nonneg (fun i _ => one_div_nonneg.mpr (hs.1 i).le)
  exact mul_le_mul_of_nonneg_right (sub_le_sub hleft hright) hweight

end
end ImbalancedChen.P1OriginalFourthPhysicalKernelComparison
