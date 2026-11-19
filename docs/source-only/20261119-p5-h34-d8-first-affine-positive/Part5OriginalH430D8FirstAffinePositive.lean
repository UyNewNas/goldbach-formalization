import ImbalancedChen.Part5OriginalH430D8SecondFourCell

/-!
P5.6 -> h34: first independent, strictly positive rational lower certificate
for the ORIGINAL moving FIRST affine part of the D8 pair source.

This is NOT added to the earlier full-D8 >= 103/1000 theorem: that old
theorem already retained the first piece as nonnegative. A stronger
combined D8 bound needs an independently exported second-only certificate.
The actual seven-source goal and count/seed/PP obligations stay OPEN.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430D8FirstAffinePositive
noncomputable section

open Set MeasureTheory Certificates
open scoped Interval
open P2EnhancedSeedPairD8Geometry
open P2EnhancedSeedPairD8Integral
open P2EnhancedSeedPairD8PieceSum
open P2EnhancedSeedActualSevenLogIdentity

private theorem log_floor (q : ℚ) (hq : 1 ≤ q) :
    (logSeriesLower q 2 : ℝ) ≤ Real.log (q : ℝ) := by
  let c : RationalLogCertificate :=
    ⟨q, 2, logSeriesLower q 2, logSeriesUpper q 2⟩
  have hc : c.check = true := by
    simpa only [RationalLogCertificate.check, decide_eq_true_eq] using
      (show c.Valid from ⟨hq, le_rfl, le_rfl⟩)
  exact (RationalLogCertificate.check_sound c hc).1

/-- The TRUE first-affine logarithm argument increases as the lower
moving v-bound decreases. This is a comparison of the original
supportLine, not a surrogate constant rectangle. -/
private theorem first_argument_mono (u : ℝ) (hu : u ∈ Icc uLo cut) :
    vHi * (1-uLo-supportLine uLo) /
      (supportLine uLo*(1-uLo-vHi)) ≤
    vHi * (1-u-supportLine u) /
      (supportLine u*(1-u-vHi)) := by
  have hFull0 : uLo ∈ Icc uLo uHi :=
    ⟨le_refl _, (literal_geometry.1.trans literal_geometry.2.1).le⟩
  have hFullU : u ∈ Icc uLo uHi :=
    ⟨hu.1,hu.2.trans literal_geometry.2.1.le⟩
  have hg0 := closed_slice_geometry hFull0
  have hgU := closed_slice_geometry hFullU
  have hp0 := first_affine_piece
    (show uLo ∈ Icc uLo cut from ⟨le_refl _,literal_geometry.1.le⟩)
  have hpU := first_affine_piece hu
  have hS0 : 0 < supportLine uLo := by
    rw [← hp0.1]
    exact hg0.2.2.1
  have hSU : 0 < supportLine u := by
    rw [← hpU.1]
    exact hgU.2.2.1
  have hV0 : 0 < 1-uLo-vHi := hg0.2.2.2.2.1
  have hVU : 0 < 1-u-vHi := hgU.2.2.2.2.1
  have hDen0 : 0 < supportLine uLo*(1-uLo-vHi) :=
    mul_pos hS0 hV0
  have hDenU : 0 < supportLine u*(1-u-vHi) :=
    mul_pos hSU hVU
  have hU0 : (50/227 : ℝ) ≤ u := by simpa only [uLo] using hu.1
  have hSBound : supportLine u ≤ supportLine uLo := by
    dsimp [supportLine,uLo]
    linarith only [hU0]
  have hDenBound :
      supportLine u*(1-u-vHi) ≤
        supportLine uLo*(1-uLo-vHi) := by
    calc
      _ ≤ supportLine uLo*(1-u-vHi) :=
        mul_le_mul_of_nonneg_right hSBound hVU.le
      _ ≤ supportLine uLo*(1-uLo-vHi) :=
        mul_le_mul_of_nonneg_left (by linarith only [hu.1]) hS0.le
  have hNum0 : 0 ≤ vHi*(1-uLo-supportLine uLo) := by
    have hn : 0 ≤ 1-uLo-supportLine uLo := by
      rw [← hp0.1]
      exact hg0.2.2.2.2.2.le
    exact mul_nonneg (by norm_num [vHi]) hn
  have hNumBound :
      vHi*(1-uLo-supportLine uLo) ≤
        vHi*(1-u-supportLine u) := by
    dsimp [vHi,supportLine,uLo]
    linarith only [hU0]
  apply (div_le_div_iff₀ hDen0 hDenU).mpr
  exact (mul_le_mul_of_nonneg_left hDenBound hNum0).trans
    (mul_le_mul_of_nonneg_right hNumBound hDen0.le)

/-- One exact D8-FIRST-affine rational Darboux floor. Its logarithm
argument is evaluated at the genuine left endpoint uLo and u(1-u)
is bounded at the genuine right endpoint cut. -/
private theorem first_pointwise_floor (u : ℝ)
    (hu : u ∈ Icc uLo cut) :
    (logSeriesLower (249700/191821 : ℚ) 2 : ℝ) /
      (cut*(1-cut)) ≤ outerSlice u := by
  have hFull : u ∈ Icc uLo uHi :=
    ⟨hu.1,hu.2.trans literal_geometry.2.1.le⟩
  have hg := closed_slice_geometry hFull
  have hDenU : 0 < u*(1-u) := mul_pos hg.1 hg.2.1
  have hDenCut : 0 < cut*(1-cut) := by norm_num [cut]
  have hHalf : 2*cut ≤ 1 := by norm_num [cut]
  have hDelta : 0 ≤ 1-cut-u := by
    linarith only [hHalf,hu.2]
  have hProd : 0 ≤ (cut-u)*(1-cut-u) :=
    mul_nonneg (sub_nonneg.mpr hu.2) hDelta
  have hDenBound : u*(1-u) ≤ cut*(1-cut) := by
    nlinarith only [hProd]
  have hQ :
      ((249700/191821 : ℚ) : ℝ) =
        vHi*(1-uLo-supportLine uLo) /
          (supportLine uLo*(1-uLo-vHi)) := by
    norm_num [uLo,vHi,supportLine]
  have hArg :
      ((249700/191821 : ℚ) : ℝ) ≤
        vHi*(1-u-supportLine u) /
          (supportLine u*(1-u-vHi)) := by
    rw [hQ]
    exact first_argument_mono u hu
  have hLog :
      (logSeriesLower (249700/191821 : ℚ) 2 : ℝ) ≤
      Real.log (vHi*(1-u-supportLine u) /
        (supportLine u*(1-u-vHi))) :=
    (log_floor (249700/191821) (by norm_num)).trans
      (Real.log_le_log
        (by norm_num : (0 : ℝ) < ((249700/191821 : ℚ) : ℝ))
        hArg)
  have hSeries :
      (0 : ℝ) ≤ (logSeriesLower (249700/191821 : ℚ) 2 : ℝ) := by
    norm_num [logSeriesLower,logParameter,Finset.sum_range_succ]
  rw [(first_affine_piece hu).2]
  change (logSeriesLower (249700/191821 : ℚ) 2 : ℝ) /
      (cut*(1-cut)) ≤
      Real.log (vHi*(1-u-supportLine u) /
        (supportLine u*(1-u-vHi))) / (u*(1-u))
  apply (div_le_div_iff₀ hDenCut hDenU).mpr
  exact (mul_le_mul_of_nonneg_left hDenBound hSeries).trans
    (mul_le_mul_of_nonneg_right hLog hDenCut.le)

/-- The true first D8 affine integral is strictly positive by an
independent exact rational certificate. Do not double-count this floor
when using an older full-D8 >= 103/1000 theorem. -/
theorem genuine_d8_first_affine_ge_1_over_200 :
    (1/200 : ℝ) ≤ ∫ u in Ioc uLo cut, firstSlice u := by
  have hSub : Icc uLo cut ⊆ Icc uLo uHi :=
    fun _ hu => ⟨hu.1,hu.2.trans literal_geometry.2.1.le⟩
  have hInt : IntervalIntegrable outerSlice volume uLo cut :=
    (continuousOn_outerSlice.mono hSub).intervalIntegrable_of_Icc
      literal_geometry.1.le
  have hMono := intervalIntegral.integral_mono_on literal_geometry.1.le
    intervalIntegrable_const hInt (fun u hu => first_pointwise_floor u hu)
  have hVal :
      (cut-uLo) *
        ((logSeriesLower (249700/191821 : ℚ) 2 : ℝ) /
          (cut*(1-cut))) ≤ ∫ u in uLo..cut, outerSlice u := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hMono
  have hRat :
      (1/200 : ℝ) ≤
        (cut-uLo) *
          ((logSeriesLower (249700/191821 : ℚ) 2 : ℝ) /
            (cut*(1-cut))) := by
    norm_num [cut,uLo,logSeriesLower,logParameter,Finset.sum_range_succ]
  have hSame :
      (∫ u in Ioc uLo cut, firstSlice u) =
        ∫ u in uLo..cut, outerSlice u := by
    calc
      _ = ∫ u in Ioc uLo cut, outerSlice u := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro u hu
        exact (first_affine_piece ⟨hu.1.le,hu.2⟩).2.symm
      _ = _ := by
        rw [← intervalIntegral.integral_of_le literal_geometry.1.le]
  rw [hSame]
  exact hRat.trans hVal

/-- Standalone full D8 consequence using nonnegativity of the second
piece. This is NOT added to the older 103/1000 bound: the latter already
includes the first piece's nonnegative mass. -/
theorem genuine_d8_first_source_in_full :
    (1/200 : ℝ) ≤ d8Logs := by
  have hFirst := genuine_d8_first_affine_ge_1_over_200
  have hSecond : 0 ≤ ∫ u in Ioo cut uHi, secondSlice u := by
    apply MeasureTheory.setIntegral_nonneg
    intro u hu
    rw [← (second_affine_piece ⟨hu.1.le,hu.2.le⟩).2]
    exact Part5OriginalH430D8SecondAffineRationalLower.actual_d8_outer_nonneg
      ⟨literal_geometry.1.le.trans hu.1.le,hu.2.le⟩
  unfold d8Logs
  linarith only [hFirst,hSecond]

end
end ImbalancedChen.Part5OriginalH430D8FirstAffinePositive
