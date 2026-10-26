import ImbalancedChen.P2EnhancedSeedPairD7Integral

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact two-affine-piece assembly for the ORIGINAL D7 model feedback.
The first lower endpoint is 1-16u/5 on [1265/5648,5/21]; the second is u
on [5/21,100/353]. Integrability and the actual D7 Fubini identity are
imported, and the split follows from interval additivity, not a certificate
pass or an assumed final feedback inequality. No numerical evaluation.
-/

namespace ImbalancedChen.P2EnhancedSeedPairD7AffinePieces

noncomputable section

open Set MeasureTheory
open scoped Interval
open P2EnhancedSeedPairD7Domain
open P2EnhancedSeedPairD7Integral

def firstLogSlice (u : ℝ) : ℝ :=
  Real.log (uHi*((11/5)*u)/((1-(16/5)*u)*(1-u-uHi)))/(u*(1-u))

def secondLogSlice (u : ℝ) : ℝ :=
  Real.log (uHi*(1-2*u)/(u*(1-u-uHi)))/(u*(1-u))

theorem outerSlice_first {u : ℝ} (hu : u≤boundaryCut) :
    outerSlice u=firstLogSlice u := by
  unfold outerSlice logArgument
  rw [lowerEndpoint_first hu]
  unfold firstLogSlice supportLine
  congr 3 <;> ring

theorem outerSlice_second {u : ℝ} (hu : boundaryCut≤u) :
    outerSlice u=secondLogSlice u := by
  unfold outerSlice logArgument
  rw [lowerEndpoint_second hu]
  unfold secondLogSlice
  congr 3 <;> ring

theorem first_intervalIntegrable :
    IntervalIntegrable outerSlice volume supportStart boundaryCut := by
  have hac : supportStart≤boundaryCut := by norm_num [supportStart,boundaryCut]
  have hcb : boundaryCut≤uHi := by norm_num [boundaryCut,uHi]
  have hc := continuousOn_outerSlice.mono
    (show Icc supportStart boundaryCut ⊆ Icc supportStart uHi from
      fun u hu => ⟨hu.1,hu.2.trans hcb⟩)
  exact hc.intervalIntegrable_of_Icc hac

theorem second_intervalIntegrable :
    IntervalIntegrable outerSlice volume boundaryCut uHi := by
  have hac : supportStart≤boundaryCut := by norm_num [supportStart,boundaryCut]
  have hcb : boundaryCut≤uHi := by norm_num [boundaryCut,uHi]
  have hc := continuousOn_outerSlice.mono
    (show Icc boundaryCut uHi ⊆ Icc supportStart uHi from
      fun u hu => ⟨hac.trans hu.1,hu.2⟩)
  exact hc.intervalIntegrable_of_Icc hcb

theorem outer_log_exact_affine_split :
    (∫ u in Ioo supportStart uHi,outerSlice u)=
      (∫ u in supportStart..boundaryCut,firstLogSlice u)+
      (∫ u in boundaryCut..uHi,secondLogSlice u) := by
  have hab : supportStart≤uHi := by norm_num [supportStart,uHi]
  have hac : supportStart≤boundaryCut := by norm_num [supportStart,boundaryCut]
  have hcb : boundaryCut≤uHi := by norm_num [boundaryCut,uHi]
  calc
    _ = ∫ u in supportStart..uHi,outerSlice u := by
      rw [integral_Ioo_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
    _ = (∫ u in supportStart..boundaryCut,outerSlice u)+
        (∫ u in boundaryCut..uHi,outerSlice u) :=
      (intervalIntegral.integral_add_adjacent_intervals
        first_intervalIntegrable second_intervalIntegrable).symm
    _ = _ := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hac] at hu
        exact outerSlice_first hu.2
      · apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hcb] at hu
        exact outerSlice_second hu.1

/-- The D7 piece of the original seven-piece lambda J calculation,
before the unique final division by five. This is an integral identity;
it makes no lambda, H, h or J2omega assertion. -/
theorem D7_feedback_exact_affine_pieces (J : ℝ) :
    (∫ x in D7,feedback J x)=J*
      ((∫ u in supportStart..boundaryCut,firstLogSlice u)+
        (∫ u in boundaryCut..uHi,secondLogSlice u)) := by
  rw [D7_feedback_outer_log,outer_log_exact_affine_split]

end
end ImbalancedChen.P2EnhancedSeedPairD7AffinePieces
