import ImbalancedChen.P2EnhancedSeedPairD8Geometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual D8 seed-model integral, genuine finite-dimensional Fubini, and
both rational affine logarithmic pieces. The support boundary is removed
only inside a REAL one-dimensional integral by singleton nullity.
No arithmetic boundary or region 1<=rho<2 is removed.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD8Integral

noncomputable section
open Set MeasureTheory Filter Classical
open scoped Interval
open P2EnhancedSeedSingletonPrimitive (S seedUpper)
open P2EnhancedSeedPairD8Geometry
open P5OriginalActionMassBound (Point)

def pairKernel : Point → ℝ := P2EnhancedSeedPairD6Primitive.pairKernel
def feedback (J : ℝ) (x : Point) : ℝ := seedUpper J (profile x)*pairKernel x
def lowerEndpoint (u : ℝ) : ℝ := max vLo (supportLine u)
def logSlice (l u : ℝ) : ℝ :=
  Real.log (vHi*(1-u-l)/(l*(1-u-vHi)))/(u*(1-u))
def outerSlice (u : ℝ) : ℝ := logSlice (lowerEndpoint u) u
def firstSlice (u : ℝ) : ℝ := logSlice (supportLine u) u
def secondSlice (u : ℝ) : ℝ := logSlice vLo u

theorem continuousOn_pairKernel : ContinuousOn pairKernel closedRectangle := by
  apply continuousOn_const.div
  · fun_prop
  · intro x hx
    have h := closed_geometry hx
    exact (mul_pos (mul_pos h.1 h.2.1) h.2.2).ne'

theorem integrableOn_pairKernel_D8 : IntegrableOn pairKernel D8 :=
  (continuousOn_pairKernel.integrableOn_compact isCompact_Icc).mono_set D8_subset_closed

theorem integrableOn_pairKernel_support : IntegrableOn pairKernel support :=
  integrableOn_pairKernel_D8.mono_set (fun _ hx => hx.1)

theorem feedback_eq_supported (J : ℝ) {x : Point} (hx : x ∈ D8) :
    feedback J x=support.indicator (fun x => J*pairKernel x) x := by
  by_cases hs : x ∈ support
  · rw [feedback,seedUpper,indicator_of_mem ((support_iff_profile hx).mp hs),indicator_of_mem hs]
  · rw [feedback,seedUpper,indicator_of_notMem (fun h => hs ((support_iff_profile hx).mpr h)),
      zero_mul,indicator_of_notMem hs]

theorem integrableOn_feedback (J : ℝ) : IntegrableOn (feedback J) D8 := by
  have hi := ((integrableOn_pairKernel_D8.const_mul J).indicator measurableSet_support)
  apply hi.congr_fun ?_ measurableSet_D8
  intro x hx
  exact (feedback_eq_supported J hx).symm

/-- This equality retains every literal supported pair, including the
sub-two arguments. It asserts a model identity, not a count licence. -/
theorem feedback_integral_support (J : ℝ) :
    (∫ x in D8,feedback J x)=J*(∫ x in support,pairKernel x) := by
  calc
    _ = ∫ x in D8,support.indicator (fun x => J*pairKernel x) x := by
      apply setIntegral_congr_fun measurableSet_D8
      intro x hx
      exact feedback_eq_supported J hx
    _ = ∫ x in D8 ∩ support,J*pairKernel x := setIntegral_indicator measurableSet_support
    _ = _ := by
      rw [inter_eq_right.mpr (show support ⊆ D8 from fun _ hx => hx.1),integral_const_mul]

theorem supported_slice_dictionary {u v : ℝ} (hne : v≠supportLine u) :
    (![u,v] : Point) ∈ support ↔
      u ∈ Ioo uLo uHi ∧ v ∈ Ioo (lowerEndpoint u) vHi := by
  change ((![u,v] : Point) ∈ D8 ∧ supportLine u≤v) ↔ _
  rw [D8_vec]
  simp only [mem_Ioo,lowerEndpoint,max_lt_iff]
  constructor
  · rintro ⟨⟨hu,hv⟩,hs⟩
    exact ⟨hu,⟨⟨hv.1,lt_of_le_of_ne hs hne.symm⟩,hv.2⟩⟩
  · rintro ⟨hu,⟨⟨hv,hs⟩,hv'⟩⟩
    exact ⟨⟨hu,⟨hv,hv'⟩⟩,hs.le⟩

/-- The max endpoint is an exact REAL integral slicing device. The
support-line endpoint alone has zero real slice measure. -/
theorem integral_support_nested :
    (∫ x in support,pairKernel x)=
      ∫ u in Ioo uLo uHi,∫ v in Ioo (lowerEndpoint u) vHi,pairKernel ![u,v] := by
  let F := support.indicator pairKernel
  have hF : Integrable F :=
    integrableOn_pairKernel_support.integrable_indicator measurableSet_support
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
  have hp (u : ℝ) : (fun v : ℝ => F ![u,v])=ᵐ[volume]
      (fun v => (Ioo uLo uHi).indicator (fun u =>
        (Ioo (lowerEndpoint u) vHi).indicator (fun v => pairKernel ![u,v]) v) u) := by
    have hn : ∀ᵐ v : ℝ ∂volume,v≠supportLine u := by rw [ae_iff]; simp
    filter_upwards [hn] with v hne
    have hd := supported_slice_dictionary hne
    by_cases hu : u ∈ Ioo uLo uHi <;>
      by_cases hv : v ∈ Ioo (lowerEndpoint u) vHi
    all_goals simp_all only [F,Set.indicator_apply,if_true,if_false,and_true,true_and,
      and_false,false_and,not_false_eq_true]
  calc
    _ = ∫ x : Point,F x := (integral_indicator measurableSet_support).symm
    _ = ∫ u : ℝ,∫ v : ℝ,F ![u,v] := htwo
    _ = ∫ u : ℝ,(Ioo uLo uHi).indicator
        (fun u => ∫ v in Ioo (lowerEndpoint u) vHi,pairKernel ![u,v]) u := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [integral_congr_ae (hp u)]
      by_cases hu : u ∈ Ioo uLo uHi
      · simp_rw [indicator_of_mem hu]
        exact integral_indicator measurableSet_Ioo
      · simp_rw [indicator_of_notMem hu]
        simp only [integral_zero]
    _ = _ := integral_indicator measurableSet_Ioo

theorem lowerEndpoint_geometry {u : ℝ} (hu : u ∈ Ioo uLo uHi) :
    0<u ∧ 0<lowerEndpoint u ∧ lowerEndpoint u<vHi ∧ vHi<1-u := by
  have h := affine_subpieces hu
  have hu0 : 0<u := lt_trans (by norm_num [uLo]) hu.1
  have hV : vHi<1-u := by dsimp [uHi,vHi] at *; linarith only [hu.2]
  refine ⟨hu0,lt_of_lt_of_le literal_geometry.2.2.1 (le_max_left _ _),?_,hV⟩
  apply max_lt
  · exact literal_geometry.2.2.2.1
  · by_cases hc : u≤cut
    · exact (h.1 hc).2.2
    · exact ((h.2 (le_of_not_ge hc)).trans_lt literal_geometry.2.2.2.1)

theorem actual_inner_log {u : ℝ} (hu : u ∈ Ioo uLo uHi) :
    (∫ v in Ioo (lowerEndpoint u) vHi,pairKernel ![u,v])=outerSlice u := by
  obtain ⟨hu0,hl,hlr,hr⟩ := lowerEndpoint_geometry hu
  have h := P2EnhancedSeedPairD6Primitive.pair_inner_log_integral hu0 hl hlr.le hr
  simpa only [pairKernel,P2EnhancedSeedPairD6Primitive.pairKernel,outerSlice,logSlice,
    Matrix.cons_val_zero,Matrix.cons_val_one,one_div,div_eq_mul_inv,mul_comm] using h

/-- Exact untruncated D8 feedback integral, before the manuscript's /5. -/
theorem feedback_outer_log (J : ℝ) :
    (∫ x in D8,feedback J x)=J*(∫ u in Ioo uLo uHi,outerSlice u) := by
  rw [feedback_integral_support,integral_support_nested]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  exact actual_inner_log hu

theorem first_affine_piece {u : ℝ} (hu : u ∈ Icc uLo cut) :
    lowerEndpoint u=supportLine u ∧ outerSlice u=firstSlice u := by
  have h : vLo≤supportLine u := by
    dsimp [vLo,supportLine,cut] at *
    linarith only [hu.2]
  have heq : lowerEndpoint u=supportLine u := max_eq_right h
  exact ⟨heq,by rw [outerSlice,heq]; rfl⟩

theorem second_affine_piece {u : ℝ} (hu : u ∈ Icc cut uHi) :
    lowerEndpoint u=vLo ∧ outerSlice u=secondSlice u := by
  have heq : lowerEndpoint u=vLo := max_eq_left ((support_cut_dictionary u).mpr hu.1)
  exact ⟨heq,by rw [outerSlice,heq]; rfl⟩

/-- The two affine descriptions agree at the exact rational switch. -/
theorem switch_agrees : firstSlice cut=secondSlice cut := by
  have h : supportLine cut=vLo := by norm_num [supportLine,cut,vLo]
  rw [firstSlice,secondSlice,h]

/-- Both resulting affine subpieces, in one exact outer integral; no
floating boundary decisions and no unproved gain coefficient occur. -/
theorem feedback_two_affine_pieces (J : ℝ) :
    (∫ x in D8,feedback J x)=J*(∫ u in Ioo uLo uHi,
      if u≤cut then firstSlice u else secondSlice u) := by
  rw [feedback_outer_log]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  by_cases hc : u≤cut
  · rw [if_pos hc]
    exact (first_affine_piece ⟨hu.1.le,hc⟩).2
  · rw [if_neg hc]
    exact (second_affine_piece ⟨(le_of_not_ge hc),hu.2.le⟩).2

end
end ImbalancedChen.P2EnhancedSeedPairD8Integral
