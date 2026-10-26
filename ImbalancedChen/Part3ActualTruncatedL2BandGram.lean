import ImbalancedChen.Part3ActualAnnularConstantOrthogonality

/-! Exact ORIGINAL quotient L2 normalization between two sharp completed
Eisenstein truncation levels. The genuine global Hilbert inner difference
is the sum of the two actual completed-constant finite height Grams.
Both Grams are honest L1 integrals with literal y^-2dy and retain the
native finite oldform coefficient normalization and central logarithm.
No ordinary incoming-wave identification or automorphic completeness.
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT. -/

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.Gamma0QuotientCellPushforward20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.MaassWeightedCoordinateL220261024zz
open ImbalancedChen.Part3.ActualCompletedTwoCuspTruncation20261026b
open ImbalancedChen.Part3.ActualTruncatedCompletedL220261026b
open ImbalancedChen.Part3.ActualTruncationConstantBands20261026b
open ImbalancedChen.Part3.ActualTwoCuspHeightRemainders20261026b
open ImbalancedChen.Part3.ActualAnnularConstantOrthogonality20261026b

namespace ImbalancedChen.Part3.ActualTruncatedL2BandGram20261026b

private theorem native_inner_of_representatives {p : ℕ} [NeZero p]
    (f g : Lp ℂ 2 (carrierPushforward p)) (F G : Gamma0OrbitSpace p → ℂ)
    (hf : (f : Gamma0OrbitSpace p → ℂ) =ᵐ[carrierPushforward p] F)
    (hg : (g : Gamma0OrbitSpace p → ℂ) =ᵐ[carrierPushforward p] G) :
    inner ℂ f g = ∫ q, star (F q) * G q ∂carrierPushforward p := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hg] with q hfq hgq
  rw [hfq, hgq]
  simp only [RCLike.inner_apply', Complex.star_def]

theorem truncation_band_inner_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) (b : Bool) :
    inner ℂ (truncatedCompletedL2 p hp Y hY s hs)
      (cuspConstantBandL2 p hp Y Z hY hYZ u hu b) = 0 := by
  rw [native_inner_of_representatives _ _ _ _ (truncatedCompletedL2_coeFn p hp Y hY s hs)
    (cuspConstantBandL2_coeFn p hp Y Z hY hYZ u hu b)]
  exact truncated_constantBand_integral_zero p hp Y Z hY hYZ s u hs hu b

theorem band_truncation_inner_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) (b : Bool) :
    inner ℂ (cuspConstantBandL2 p hp Y Z hY hYZ s hs b)
      (truncatedCompletedL2 p hp Y hY u hu) = 0 :=
  (inner_eq_zero_symm).mp (truncation_band_inner_zero p hp Y Z hY hYZ u s hu hs b)

theorem cross_cusp_band_inner_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) :
    inner ℂ (cuspConstantBandL2 p hp Y Z hY hYZ s hs false)
      (cuspConstantBandL2 p hp Y Z hY hYZ u hu true) = 0 := by
  rw [native_inner_of_representatives _ _ _ _
    (cuspConstantBandL2_coeFn p hp Y Z hY hYZ s hs false)
    (cuspConstantBandL2_coeFn p hp Y Z hY hYZ u hu true)]
  exact cross_cusp_constantBand_integral_zero p hp Y Z hY hYZ s u

theorem reverse_cross_cusp_band_inner_zero (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) :
    inner ℂ (cuspConstantBandL2 p hp Y Z hY hYZ s hs true)
      (cuspConstantBandL2 p hp Y Z hY hYZ u hu false) = 0 :=
  (inner_eq_zero_symm).mp (cross_cusp_band_inner_zero p hp Y Z hY hYZ u s hu hs)

theorem band_inner_Gram (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) (b : Bool) :
    inner ℂ (cuspConstantBandL2 p hp Y Z hY hYZ s hs b)
      (cuspConstantBandL2 p hp Y Z hY hYZ u hu b) = completedConstantBandGram p Y Z s u b := by
  rw [native_inner_of_representatives _ _ _ _
    (cuspConstantBandL2_coeFn p hp Y Z hY hYZ s hs b)
    (cuspConstantBandL2_coeFn p hp Y Z hY hYZ u hu b)]
  exact constantBand_pair_integral p hp Y Z hY hYZ s u hs hu b

/-- Increasing the actual cutoff adds only the two completed constant
Grams to the ORIGINAL Hilbert pairing. All six off-diagonal blocks
vanish by proved physical means or genuine disjoint cusp supports. -/
theorem truncated_L2_inner_difference (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) :
    inner ℂ (truncatedCompletedL2 p hp Z (hY.trans hYZ) s hs)
        (truncatedCompletedL2 p hp Z (hY.trans hYZ) u hu) -
      inner ℂ (truncatedCompletedL2 p hp Y hY s hs)
        (truncatedCompletedL2 p hp Y hY u hu) =
      completedConstantBandGram p Y Z s u false + completedConstantBandGram p Y Z s u true := by
  have hsum (v : ℂ) (hv : v ∈ completedRegularDomain p) :
      truncatedCompletedL2 p hp Z (hY.trans hYZ) v hv =
        truncatedCompletedL2 p hp Y hY v hv +
          cuspConstantBandL2 p hp Y Z hY hYZ v hv false +
          cuspConstantBandL2 p hp Y Z hY hYZ v hv true := by
    calc
      _ = (cuspConstantBandL2 p hp Y Z hY hYZ v hv false +
          cuspConstantBandL2 p hp Y Z hY hYZ v hv true) +
            truncatedCompletedL2 p hp Y hY v hv :=
        (sub_eq_iff_eq_add).mp (truncation_L2_level_difference p hp Y Z hY hYZ v hv)
      _ = _ := by abel
  rw [hsum s hs, hsum u hu]
  simp only [inner_add_left, inner_add_right, truncation_band_inner_zero,
    band_truncation_inner_zero, cross_cusp_band_inner_zero, reverse_cross_cusp_band_inner_zero,
    band_inner_Gram, zero_add, add_zero]
  ring

theorem physicalCuspConstant_continuousOn (p : ℕ) (hp : p.Prime) (s : ℂ) (b : Bool) :
    ContinuousOn (physicalCuspConstant p s b) (Ioi 0) := by
  cases b
  · exact completedInfinityConstant_continuousOn p s
  · exact completedReflectedConstant_continuousOn p hp.pos s

/-- Honest finite weighted-height L1, including the central logarithmic
constant; the Gram is not a default-zero divergent Bochner integral. -/
theorem weighted_constant_band_integrable (p : ℕ) (hp : p.Prime) (Y Z : ℝ)
    (hY : 1 ≤ Y) (s u : ℂ) (b : Bool) :
    IntegrableOn (fun y => ((y⁻¹)^2 : ℝ) •
      (star (physicalCuspConstant p s b y) * physicalCuspConstant p u b y)) (Ioc Y Z) := by
  have hpos : Icc Y Z ⊆ Ioi (0 : ℝ) := fun y hy =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hY.trans hy.1)
  have hweight : ContinuousOn (fun y : ℝ => (y⁻¹)^2) (Icc Y Z) :=
    (continuousOn_id.inv₀ (fun y hy => ne_of_gt (hpos hy))).pow 2
  have hprod : ContinuousOn (fun y => star (physicalCuspConstant p s b y) *
      physicalCuspConstant p u b y) (Icc Y Z) :=
    ((physicalCuspConstant_continuousOn p hp s b).mono hpos).star.mul
      ((physicalCuspConstant_continuousOn p hp u b).mono hpos)
  exact (hweight.smul hprod).integrableOn_Icc.mono_set Ioc_subset_Icc_self

theorem completedConstantBandGram_eq_weighted (p : ℕ) (Y Z : ℝ) (hY : 1 ≤ Y)
    (s u : ℂ) (b : Bool) : completedConstantBandGram p Y Z s u b =
      ∫ y in Ioc Y Z, ((y⁻¹)^2 : ℝ) •
        (star (physicalCuspConstant p s b y) * physicalCuspConstant p u b y) := by
  have hpos : Ioc Y Z ⊆ Ioi (0 : ℝ) := fun y hy =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hY.trans hy.1.le)
  unfold completedConstantBandGram verticalWeightedMeasure
  rw [Measure.restrict_withDensity measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc, inter_eq_self_of_subset_left hpos]
  simpa only [NNReal.smul_def, verticalWeight] using
    (integral_withDensity_eq_integral_smul verticalWeight_measurable
      (fun y => star (physicalCuspConstant p s b y) * physicalCuspConstant p u b y)
      (μ := (volume : Measure ℝ).restrict (Ioc Y Z)))

/-- Explicit physical normalization: both genuine completed constant
profiles are integrated with coefficient one and the canonical y^-2dy.
The central regularization and the actual oldform denominator remain. -/
theorem truncated_L2_inner_difference_physical (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s u : ℂ)
    (hs : s ∈ completedRegularDomain p) (hu : u ∈ completedRegularDomain p) :
    inner ℂ (truncatedCompletedL2 p hp Z (hY.trans hYZ) s hs)
        (truncatedCompletedL2 p hp Z (hY.trans hYZ) u hu) -
      inner ℂ (truncatedCompletedL2 p hp Y hY s hs)
        (truncatedCompletedL2 p hp Y hY u hu) =
      (∫ y in Ioc Y Z, ((y⁻¹)^2 : ℝ) •
        (star (completedInfinityConstant p s y) * completedInfinityConstant p u y)) +
      ∫ y in Ioc Y Z, ((y⁻¹)^2 : ℝ) •
        (star (completedReflectedConstant p s y) * completedReflectedConstant p u y) := by
  rw [truncated_L2_inner_difference p hp Y Z hY hYZ s u hs hu,
    completedConstantBandGram_eq_weighted p Y Z hY s u false,
    completedConstantBandGram_eq_weighted p Y Z hY s u true]
  rfl

theorem constantBandGram_self_re (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ)
    (hs : s ∈ completedRegularDomain p) (b : Bool) :
    (completedConstantBandGram p Y Z s s b).re =
      ‖cuspConstantBandL2 p hp Y Z hY hYZ s hs b‖ ^ 2 := by
  rw [← band_inner_Gram p hp Y Z hY hYZ s s hs hs b]
  exact (norm_sq_eq_re_inner _).symm

theorem truncated_L2_mass_difference (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    ‖truncatedCompletedL2 p hp Z (hY.trans hYZ) s hs‖ ^ 2 -
      ‖truncatedCompletedL2 p hp Y hY s hs‖ ^ 2 =
      (completedConstantBandGram p Y Z s s false).re +
        (completedConstantBandGram p Y Z s s true).re := by
  have h := congrArg Complex.re (truncated_L2_inner_difference p hp Y Z hY hYZ s s hs hs)
  simpa only [Complex.sub_re, Complex.add_re, ← norm_sq_eq_re_inner] using h

theorem truncated_L2_mass_monotone (p : ℕ) [NeZero p] (hp : p.Prime)
    (Y Z : ℝ) (hY : 1 ≤ Y) (hYZ : Y ≤ Z) (s : ℂ) (hs : s ∈ completedRegularDomain p) :
    ‖truncatedCompletedL2 p hp Y hY s hs‖ ^ 2 ≤
      ‖truncatedCompletedL2 p hp Z (hY.trans hYZ) s hs‖ ^ 2 := by
  have h := truncated_L2_mass_difference p hp Y Z hY hYZ s hs
  rw [constantBandGram_self_re p hp Y Z hY hYZ s hs false,
    constantBandGram_self_re p hp Y Z hY hYZ s hs true] at h
  linarith [sq_nonneg ‖cuspConstantBandL2 p hp Y Z hY hYZ s hs false‖,
    sq_nonneg ‖cuspConstantBandL2 p hp Y Z hY hYZ s hs true‖]

end ImbalancedChen.Part3.ActualTruncatedL2BandGram20261026b
