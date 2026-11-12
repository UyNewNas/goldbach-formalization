import ImbalancedChen.P4AOriginalFull87SourcePrimeTests
import ImbalancedChen.P4AOrderedThirdEighthTrimProgram
import ImbalancedChen.ActualPrimePolyhedralTestFunctions

/-! The strict original rows have a genuine target-deleted prime limit.
Zero linear parts are handled exactly, including a constant false row.
The charge 1+profile controls both the absolute reciprocal-prime mass
of a missed word and its original normalized source profile. -/
namespace ImbalancedChen.P1OriginalFull87PrimeBoundary
noncomputable section
open scoped Classical BigOperators Topology
open Filter MeasureTheory Set VariableEnvelope
open P4AOriginalFull87SourceDictionary (Cell Point Source)
open P4AOriginalFull87StrictActionTrim (sourceSet source_iff_rows rowCount rowValue trim trim_subset_source)
open P4AOriginalFull87HistoryCore (width width_pos)
open P4AOriginalFull87EighthKernelControl (cutoff cutoff_pos)
open P4AOriginalFull87SourcePrimeTests
open P4AOrderedThirdEighthTrimProgram (rowForm row_exact)

private def form (c : Cell) (j : Fin (rowCount c)) : Point →L[ℝ] ℝ :=
  -(∑ i : Fin 8,(rowForm c j).coefficient i • ContinuousLinearMap.proj i)

private theorem row_pos (c : Cell) (j : Fin (rowCount c)) (t : Point) :
    0<rowValue c j t ↔ form c j t<(rowForm c j).constant := by
  rw [←row_exact]
  simp only [form,neg_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,P1FiniteAffineDecisionProgram.Affine.eval]
  constructor <;> intro h <;> linarith

def charge (c : Cell) (t : Point) : ℝ := 1+profile c t
theorem charge_ge_one (c : Cell) (t : Point) : 1≤charge c t :=
  le_add_of_nonneg_right (le_max_left _ _)
theorem charge_nonneg (c : Cell) (t : Point) : 0≤charge c t := zero_le_one.trans (charge_ge_one c t)
theorem continuous_charge (c : Cell) : Continuous (charge c) := continuous_const.add (continuous_profile c)

def sharp (N : ℕ) (c : Cell) : ℝ := actualPrimeBoxTestSum N (fun _ => cutoff) (fun _ => mu)
  ((sourceSet c).indicator (charge c))
def inner (N r : ℕ) (c : Cell) : ℝ := actualPrimeBoxTestSum N (fun _ => cutoff) (fun _ => mu)
  (fun t => charge c t*ramp r c t)
def target (c : Cell) : ℝ := ∫ t in sourceSet c,charge c t*∏ i,1/t i
def approx (r : ℕ) (c : Cell) : ℝ := ∫ t in box,(charge c t*ramp r c t)*∏ i,1/t i

/-- Constant rows are identities on a nonempty original source. Only
genuinely proper walls reach the existing arithmetic polyhedral theorem. -/
theorem sharp_tendsto (c : Cell) : Tendsto (fun N => sharp N c) atTop (𝓝 (target c)) := by
  by_cases h : (sourceSet c).Nonempty
  · obtain ⟨t0,ht0⟩ := h
    let J := {j : Fin (rowCount c) // form c j≠0}
    let E := Fintype.equivFin J
    let L := fun k : Fin (Fintype.card J) => form c (E.symm k).val
    let C := fun k : Fin (Fintype.card J) => (rowForm c (E.symm k).val).constant
    have hS : sourceSet c=primeAffineGateRegion L C := by
      ext t
      constructor
      · intro ht k
        exact (row_pos c _ t).mp ((source_iff_rows c t).mp ht _)
      · intro ht
        apply (source_iff_rows c t).mpr
        intro j
        apply (row_pos c j t).mpr
        by_cases hz : form c j=0
        · have hv := (row_pos c j t0).mp ((source_iff_rows c t0).mp ht0 j)
          simpa only [hz,ContinuousLinearMap.zero_apply] using hv
        · have hv := ht (E ⟨j,hz⟩)
          simpa only [L,C,Equiv.symm_apply_apply] using hv
    have lim := tendsto_actualPrimeBoxTestSum_cube_affineGates cutoff_pos
      (by norm_num [cutoff,mu] : cutoff<mu) L C (fun k => (E.symm k).property)
      (charge c) (continuous_charge c).continuousOn
    rw [←hS,inter_eq_right.mpr (source_subset_box c)] at lim
    exact lim
  · have hs := Set.not_nonempty_iff_eq_empty.mp h
    simpa [sharp,target,hs,actualPrimeBoxTestSum] using (tendsto_const_nhds (x:=(0:ℝ)) :
      Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

theorem inner_tendsto (r : ℕ) (c : Cell) : Tendsto (fun N => inner N r c) atTop (𝓝 (approx r c)) :=
  tendsto_actualPrimeBoxTestSum_cube cutoff_pos (by norm_num [cutoff,mu])
    _ ((continuous_charge c).mul (continuous_ramp r c)).continuousOn

theorem approx_tendsto (c : Cell) : Tendsto (fun r => approx r c) atTop (𝓝 (target c)) := by
  let dens := fun t : Point => ∏ i,1/t i
  have H := tendsto_integral_of_dominated_convergence (μ:=volume.restrict box)
    (F:=fun r t => (charge c t*ramp r c t)*dens t)
    (f:=(sourceSet c).indicator (fun t => charge c t*dens t)) (fun t => charge c t*dens t)
    (fun r => (integrableOn_logPrimeBox_test_cube cutoff_pos _
      ((continuous_charge c).mul (continuous_ramp r c)).continuousOn).aestronglyMeasurable)
    (integrableOn_logPrimeBox_test_cube cutoff_pos (charge c) (continuous_charge c).continuousOn)
    (fun r => by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin 8 => cutoff) (fun _ => mu))] with t ht
      have hd : 0≤dens t := Finset.prod_nonneg fun i _ =>
        (one_div_pos.mpr (cutoff_pos.trans_le ((mem_logPrimeBox.mp ht i).1))).le
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (charge_nonneg c t) (ramp_bounds r c t).1) hd)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (charge_nonneg c t) (ramp_bounds r c t).2) hd)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_logPrimeBox
        (fun _ : Fin 8 => cutoff) (fun _ => mu))] with t ht
      apply tendsto_const_nhds.congr'
      by_cases hs : t∈sourceSet c
      · filter_upwards [ramp_eventually_one hs] with r hr
        simp only [indicator_of_mem hs,hr,mul_one]
      · filter_upwards with r
        simp only [indicator_of_notMem hs,ramp_off_trim r c ht
          (fun hm => hs (trim_subset_source c (width_pos r) hm)),mul_zero,zero_mul])
  rw [setIntegral_indicator (P4AOriginalFull87StrictActionTrim.sourceSet_measurable c),
    inter_eq_right.mpr (source_subset_box c)] at H
  exact H

/-- Both inequalities use the same trim and arithmetic threshold; their
individual target sums are the original 87 integrals and actual primes. -/
theorem cofinal_boundary (ε : ℝ) (hε : 0<ε) :
    ∃ r0 : ℕ,∀ r≥r0,∃ N0 : ℕ,2≤N0 ∧ ∀ N≥N0,
      (∑ c : Cell,sharp N c)-(∑ c : Cell,inner N r c)<ε ∧
      (∑ c : Cell,cellIntegral c)-ε < ∑ c : Cell,testSum N r c := by
  have HA := tendsto_finsetSum (Finset.univ : Finset Cell) (fun c _ => approx_tendsto c)
  have HT := tendsto_finsetSum (Finset.univ : Finset Cell) (fun c _ => testIntegral_tendsto c)
  obtain ⟨r0,hr⟩ := eventually_atTop.mp ((HA.eventually (lt_mem_nhds
    (show (∑ c : Cell,target c)-ε/2<∑ c : Cell,target c by linarith))).and
    (HT.eventually (lt_mem_nhds (show (∑ c : Cell,cellIntegral c)-ε/2<∑ c : Cell,cellIntegral c by linarith))))
  refine ⟨r0,?_⟩
  intro r hr'
  have h := hr r hr'
  have HP := (tendsto_finsetSum (Finset.univ : Finset Cell) (fun c _ => sharp_tendsto c)).sub
    (tendsto_finsetSum (Finset.univ : Finset Cell) (fun c _ => inner_tendsto r c))
  have HN := tendsto_finsetSum (Finset.univ : Finset Cell) (fun c _ => testSum_tendsto r c)
  obtain ⟨N0,h0⟩ := eventually_atTop.mp ((HP.eventually (gt_mem_nhds
    (show (∑ c : Cell,target c)-(∑ c : Cell,approx r c)<ε by linarith only [h.1,hε]))).and
    (HN.eventually (lt_mem_nhds (show (∑ c : Cell,cellIntegral c)-ε<∑ c : Cell,testIntegral r c by
      linarith only [h.2,hε]))))
  exact ⟨max 2 N0,le_max_left _ _,fun N hN => h0 N ((le_max_right _ _).trans hN)⟩

end
end ImbalancedChen.P1OriginalFull87PrimeBoundary
