import ImbalancedChen.P2EnhancedSeedPairD7Domain

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The true D7 seed-model integral, with its actual moving profile. Exact
support slicing is imported from the exclusive domain leaf. The single
weak support boundary is removed only inside a one-dimensional Lebesgue
slice, by integral_Ico_eq_integral_Ioo. Integrability precedes genuine
finite-coordinate Fubini. The logarithmic primitive is the frozen D6
general primitive, applied to the proved moving endpoints. No target
coefficient, numerical pass, H/h licence or final count bound is assumed.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD7Integral

noncomputable section

open Set MeasureTheory Filter Classical
open scoped Interval
open P5OriginalActionMassBound (Point)
open P2EnhancedSeedPairD7Domain
open P2EnhancedSeedPairD6Primitive (pairKernel pair_inner_log_integral)

def slice (u : ℝ) : Set ℝ := {v | (![u,v] : Point) ∈ supportedD7}
def logArgument (u : ℝ) : ℝ :=
  uHi*(1-u-lowerEndpoint u)/(lowerEndpoint u*(1-u-uHi))
def outerSlice (u : ℝ) : ℝ := Real.log (logArgument u)/(u*(1-u))

theorem continuousOn_pairKernel : ContinuousOn pairKernel closedRectangle := by
  apply continuousOn_const.div
  · fun_prop
  · intro x hx
    have hg := closed_geometry hx
    exact (mul_pos (mul_pos hg.1 hg.2.1) hg.2.2).ne'

theorem integrableOn_pairKernel_D7 : IntegrableOn pairKernel D7 :=
  (continuousOn_pairKernel.integrableOn_compact isCompact_Icc).mono_set D7_subset_closed

theorem integrableOn_pairKernel_supported : IntegrableOn pairKernel supportedD7 :=
  integrableOn_pairKernel_D7.mono_set inter_subset_left

theorem measurableSet_slice (u : ℝ) : MeasurableSet (slice u) := by
  have hv : Measurable (fun v : ℝ => (![u,v] : Point)) := by fun_prop
  exact measurableSet_supportedD7.preimage hv

theorem slice_first {u : ℝ} (hu : u ∈ Ioo supportStart boundaryCut) :
    slice u=Ico (supportLine u) uHi := by
  ext v
  change (![u,v] : Point) ∈ supportedD7 ↔ v ∈ Ico (supportLine u) uHi
  rw [supported_vec]
  constructor
  · rintro (⟨_,hv⟩ | ⟨hc,_⟩)
    · exact hv
    · exact False.elim (not_lt_of_ge hc.1 hu.2)
  · exact fun hv => Or.inl ⟨hu,hv⟩

theorem slice_second {u : ℝ} (hu : u ∈ Ico boundaryCut uHi) :
    slice u=Ioo u uHi := by
  ext v
  change (![u,v] : Point) ∈ supportedD7 ↔ v ∈ Ioo u uHi
  rw [supported_vec]
  constructor
  · rintro (⟨hc,_⟩ | ⟨_,hv⟩)
    · exact False.elim (not_lt_of_ge hu.1 hc.2)
    · exact hv
  · exact fun hv => Or.inr ⟨hu,hv⟩

theorem slice_empty {u : ℝ} (hu : u ∉ Ioo supportStart uHi) : slice u=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact hu (by simpa only [Matrix.cons_val_zero] using support_outer_bounds hv)

/-- Only the real integral changes its boundary convention. Exact domain
membership, native cutoff inheritance and prime gates keep the weak wall. -/
theorem slice_integral_eq_open {u : ℝ} (hu : u ∈ Ioo supportStart uHi) :
    (∫ v in slice u,pairKernel ![u,v])=
      ∫ v in Ioo (lowerEndpoint u) uHi,pairKernel ![u,v] := by
  by_cases hc : u<boundaryCut
  · rw [slice_first ⟨hu.1,hc⟩,lowerEndpoint_first hc.le,
      integral_Ico_eq_integral_Ioo]
  · have huc : boundaryCut≤u := le_of_not_gt hc
    rw [slice_second ⟨huc,hu.2⟩,lowerEndpoint_second huc]

/-- Actual two-dimensional Lebesgue Fubini on the integrable D7 support. -/
theorem integral_supported_nested :
    (∫ x in supportedD7,pairKernel x)=
      ∫ u in Ioo supportStart uHi,∫ v in Ioo (lowerEndpoint u) uHi,pairKernel ![u,v] := by
  let F := supportedD7.indicator pairKernel
  have hF : Integrable F :=
    integrableOn_pairKernel_supported.integrable_indicator measurableSet_supportedD7
  have htwo : (∫ x : Point,F x)=∫ u : ℝ,∫ v : ℝ,F ![u,v] := by
    calc
      _ = ∫ u : ℝ,∫ v : ℝ,∫ z : Fin 0 → ℝ,F (Fin.cons u (Fin.cons v z)) :=
        integral_fin_pair F hF
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with u
        apply integral_congr_ae
        filter_upwards [] with v
        rw [integral_fin_zero]
        rfl
  have hslice (u : ℝ) : (∫ v : ℝ,F ![u,v])=∫ v in slice u,pairKernel ![u,v] := by
    change (∫ v : ℝ,(slice u).indicator (fun v => pairKernel ![u,v]) v)=_
    exact integral_indicator (measurableSet_slice u)
  calc
    _ = ∫ x : Point,F x := (integral_indicator measurableSet_supportedD7).symm
    _ = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := htwo
    _ = ∫ u : ℝ,(Ioo supportStart uHi).indicator
        (fun u => ∫ v in Ioo (lowerEndpoint u) uHi,pairKernel ![u,v]) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [hslice]
      by_cases hu : u ∈ Ioo supportStart uHi
      · rw [indicator_of_mem hu]
        exact slice_integral_eq_open hu
      · rw [indicator_of_notMem hu,slice_empty hu]
        simp only [setIntegral_empty]
    _ = _ := integral_indicator measurableSet_Ioo

theorem endpoint_geometry {u : ℝ} (hu : u ∈ Icc supportStart uHi) :
    0<u ∧ 0<lowerEndpoint u ∧ lowerEndpoint u≤uHi ∧ uHi<1-u := by
  have hu0 : 0<u := lt_of_lt_of_le (by norm_num [supportStart]) hu.1
  have hlo : u≤lowerEndpoint u := le_max_left _ _
  have hline : supportLine u≤uHi := by
    dsimp [supportLine,supportStart,uHi] at *
    linarith only [hu.1]
  have hhi : uHi<1-u := by
    dsimp [uHi] at hu ⊢
    linarith only [hu.2]
  exact ⟨hu0,hu0.trans_le hlo,max_le hu.2 hline,hhi⟩

theorem D7_inner_log_slice {u : ℝ} (hu : u ∈ Icc supportStart uHi) :
    (∫ v in Ioo (lowerEndpoint u) uHi,pairKernel ![u,v])=outerSlice u := by
  have hg := endpoint_geometry hu
  have h := pair_inner_log_integral hg.1 hg.2.1 hg.2.2.1 hg.2.2.2
  simpa only [pairKernel,Matrix.cons_val_zero,Matrix.cons_val_one,outerSlice,logArgument,
    one_div,div_eq_mul_inv,mul_comm] using h

theorem logArgument_positive {u : ℝ} (hu : u ∈ Icc supportStart uHi) :
    0<logArgument u := by
  obtain ⟨hu0,hl0,hlr,hr⟩ := endpoint_geometry hu
  have hlres : 0<1-u-lowerEndpoint u := by linarith only [hlr,hr]
  have hrres : 0<1-u-uHi := by linarith only [hr]
  exact div_pos (mul_pos (by norm_num [uHi]) hlres) (mul_pos hl0 hrres)

theorem continuous_lowerEndpoint : Continuous lowerEndpoint := by
  unfold lowerEndpoint supportLine
  fun_prop

theorem continuousOn_outerSlice : ContinuousOn outerSlice (Icc supportStart uHi) := by
  have harg : ContinuousOn logArgument (Icc supportStart uHi) := by
    apply ContinuousOn.div
    · exact continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).sub
        continuous_lowerEndpoint.continuousOn)
    · exact continuous_lowerEndpoint.continuousOn.mul
        ((continuousOn_const.sub continuousOn_id).sub continuousOn_const)
    · intro u hu
      have hg := endpoint_geometry hu
      exact (mul_pos hg.2.1 (by linarith only [hg.2.2.2] : 0<1-u-uHi)).ne'
  have hlog := harg.log (fun u hu => (logArgument_positive hu).ne')
  exact hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    (fun u hu => (mul_pos (endpoint_geometry hu).1
      (lt_trans (by norm_num [uHi]) (endpoint_geometry hu).2.2.2)).ne')

theorem integrableOn_outerSlice : IntegrableOn outerSlice (Ioo supportStart uHi) :=
  (continuousOn_outerSlice.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- Exact original D7 feedback before the common final division by five.
J is a freely chosen model constant. This theorem supplies no enhanced
count licence and assumes no feedback coefficient bound. -/
theorem D7_feedback_outer_log (J : ℝ) :
    (∫ x in D7,feedback J x)=J*∫ u in Ioo supportStart uHi,outerSlice u := by
  calc
    _ = ∫ x in D7,supportedD7.indicator (fun x => J*pairKernel x) x := by
      apply setIntegral_congr_fun measurableSet_D7
      intro x hx
      exact feedback_eq_supported_indicator J hx
    _ = ∫ x in D7 ∩ supportedD7,J*pairKernel x :=
      setIntegral_indicator measurableSet_supportedD7
    _ = ∫ x in supportedD7,J*pairKernel x := by
      rw [inter_eq_right.mpr (show supportedD7 ⊆ D7 from inter_subset_left)]
    _ = J*(∫ x in supportedD7,pairKernel x) := integral_const_mul _ _
    _ = J*(∫ u in Ioo supportStart uHi,
        ∫ v in Ioo (lowerEndpoint u) uHi,pairKernel ![u,v]) := by
      rw [integral_supported_nested]
    _ = _ := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      exact D7_inner_log_slice ⟨hu.1.le,hu.2.le⟩

end
end ImbalancedChen.P2EnhancedSeedPairD7Integral
