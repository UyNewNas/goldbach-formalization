import ImbalancedChen.P2EnhancedSeedPairD8Integral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The two literal affine D8 pieces as a sum of actual real integrals.
There is no assumed cell bound, enhanced-count licence, lambda bound,
table value or saved numerical pass. This is the final analytic D8 leaf;
the positive-count analytic input and finite feedback gain remain OPEN.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD8PieceSum

noncomputable section
open Set MeasureTheory Classical
open scoped Interval
open P2EnhancedSeedPairD8Geometry
open P2EnhancedSeedPairD8Integral

theorem closed_slice_geometry {u : ℝ} (hu : u ∈ Icc uLo uHi) :
    0<u ∧ 0<1-u ∧ 0<lowerEndpoint u ∧ lowerEndpoint u<vHi ∧
      0<1-u-vHi ∧ 0<1-u-lowerEndpoint u := by
  have hu0 : 0<u := lt_of_lt_of_le (by norm_num [uLo]) hu.1
  have hV : 0<1-u-vHi := by dsimp [uHi,vHi] at *; linarith only [hu.2]
  have hline : supportLine u<vHi := by
    dsimp [supportLine,vHi,uLo] at *
    linarith only [hu.1]
  have hl : lowerEndpoint u<vHi := max_lt literal_geometry.2.2.2.1 hline
  exact ⟨hu0,by have hv : 0<vHi := by norm_num [vHi]; linarith only [hV,hv],
    lt_of_lt_of_le literal_geometry.2.2.1 (le_max_left _ _),hl,hV,by linarith only [hl,hV]⟩

theorem continuousOn_outerSlice : ContinuousOn outerSlice (Icc uLo uHi) := by
  have hlow : Continuous lowerEndpoint := by
    unfold lowerEndpoint supportLine
    fun_prop
  have hArg : ContinuousOn
      (fun u : ℝ => vHi*(1-u-lowerEndpoint u)/(lowerEndpoint u*(1-u-vHi)))
      (Icc uLo uHi) := by
    apply ContinuousOn.div
    · exact continuousOn_const.mul ((continuousOn_const.sub continuousOn_id).sub hlow.continuousOn)
    · exact hlow.continuousOn.mul ((continuousOn_const.sub continuousOn_id).sub continuousOn_const)
    · intro u hu
      have h := closed_slice_geometry hu
      exact (mul_pos h.2.2.1 h.2.2.2.2.1).ne'
  have hlog := hArg.log (fun u hu => by
    have h := closed_slice_geometry hu
    exact (div_pos (mul_pos (by norm_num [vHi]) h.2.2.2.2.2)
      (mul_pos h.2.2.1 h.2.2.2.2.1)).ne')
  exact hlog.div (continuousOn_id.mul (continuousOn_const.sub continuousOn_id))
    (fun u hu => (mul_pos (closed_slice_geometry hu).1 (closed_slice_geometry hu).2.1).ne')

theorem integrableOn_outerSlice : IntegrableOn outerSlice (Icc uLo uHi) :=
  continuousOn_outerSlice.integrableOn_compact isCompact_Icc

/-- The rational switch is assigned to the first subpiece. The original
open outer endpoints remain open and no support region is omitted. -/
theorem outerSlice_piece_sum :
    (∫ u in Ioo uLo uHi,outerSlice u)=
      (∫ u in Ioc uLo cut,firstSlice u)+(∫ u in Ioo cut uHi,secondSlice u) := by
  have hleft : Ioc uLo cut ⊆ Icc uLo uHi := fun u hu =>
    ⟨hu.1.le,hu.2.trans literal_geometry.2.1.le⟩
  have hright : Ioo cut uHi ⊆ Icc uLo uHi := fun u hu =>
    ⟨literal_geometry.1.le.trans hu.1.le,hu.2.le⟩
  have hdis : Disjoint (Ioc uLo cut) (Ioo cut uHi) := by
    apply Set.disjoint_left.mpr
    intro u hl hr
    exact (not_lt_of_ge hl.2) hr.1
  have hset : Ioc uLo cut ∪ Ioo cut uHi=Ioo uLo uHi := by
    ext u
    constructor
    · rintro (h | h)
      · exact ⟨h.1,h.2.trans_lt literal_geometry.2.1⟩
      · exact ⟨literal_geometry.1.trans h.1,h.2⟩
    · intro h
      by_cases hc : u≤cut
      · exact Or.inl ⟨h.1,hc⟩
      · exact Or.inr ⟨lt_of_not_ge hc,h.2⟩
  have hs := setIntegral_union hdis measurableSet_Ioo
    (integrableOn_outerSlice.mono_set hleft) (integrableOn_outerSlice.mono_set hright)
  rw [hset] at hs
  calc
    _ = (∫ u in Ioc uLo cut,outerSlice u)+(∫ u in Ioo cut uHi,outerSlice u) := hs
    _ = _ := by
      congr 1
      · apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        exact (first_affine_piece ⟨hu.1.le,hu.2⟩).2
      · apply setIntegral_congr_fun measurableSet_Ioo
        intro u hu
        exact (second_affine_piece ⟨hu.1.le,hu.2.le⟩).2

/-- Exactly the manuscript's D8 affine logarithmic pair formula, with
all rational endpoints and both pieces. The factor J is taken once. -/
theorem feedback_exact_two_integrals (J : ℝ) :
    (∫ x in D8,feedback J x)=J*((∫ u in uLo..cut,
      Real.log (vHi*(1-u-supportLine u)/(supportLine u*(1-u-vHi)))/(u*(1-u)))+
      (∫ u in cut..uHi,
      Real.log (vHi*(1-u-vLo)/(vLo*(1-u-vHi)))/(u*(1-u)))) := by
  rw [feedback_outer_log,outerSlice_piece_sum]
  rw [← intervalIntegral.integral_of_le literal_geometry.1.le]
  rw [integral_Ioo_eq_integral_Ioc,← intervalIntegral.integral_of_le literal_geometry.2.1.le]
  rfl

end
end ImbalancedChen.P2EnhancedSeedPairD8PieceSum
