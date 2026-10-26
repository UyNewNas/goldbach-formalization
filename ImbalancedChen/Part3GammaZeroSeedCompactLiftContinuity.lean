import ImbalancedChen.Part3GammaSmoothZeroSeedNativeGraph
import ImbalancedChen.Part3GammaCompactSeedL2Transport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Every original continuous compact HeightSeed has an exact compact smooth-
horizontal lift on H. Its actual effective Poincare L2 vector is the
original zeroSeedL2, by the genuine complex reindex and conull section.
One compact carrier controls all profiles with support inside the same
height support. The existing actual compact-overlap budget therefore
gives a quantitative zeroSeedL2 difference bound from uniform profile
error. No density or Poincare continuity conclusion is assumed.
-/
namespace ImbalancedChen.Part3.GammaZeroSeedCompactLiftContinuity20261026b

noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0ActualParabolicUnfolding20261025a
open GammaInfinityTranslationStrip20261025a
open ActualInfinityKloostermanSeed20261025a CompactCuspParabolicL220261025a
open ActualInfinityCuspAnnihilator20261026b
open SmoothIntegerUnitPartition20261026b SmoothZeroHeightSeedProfiles20261026b
open GammaSmoothZeroSeedNativeGraph20261026b GammaCompactSeedL2Transport20261026a

theorem complexHorizontalPartition_norm_le_one (x : ℝ) : ‖complexHorizontalPartition x‖ ≤ 1 := by
  have hnonneg : 0 ≤ horizontalUnitPartition x :=
    sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith : x ≤ x + 1))
  have hle : horizontalUnitPartition x ≤ 1 :=
    (sub_le_self _ (Real.smoothTransition.nonneg x)).trans (Real.smoothTransition.le_one (x + 1))
  rw [complexHorizontalPartition, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

def heightProfileCompactCarrier (s : HeightSeed) : Set UpperHalfPlane :=
  {z | z.re ∈ Icc (-1 : ℝ) 1 ∧ z.im ∈ tsupport s.toFun}

theorem heightProfileCompactCarrier_isCompact (s : HeightSeed) :
    IsCompact (heightProfileCompactCarrier s) := by
  apply UpperHalfPlane.isEmbedding_coe.isCompact_iff.mpr
  have heq : UpperHalfPlane.coe '' heightProfileCompactCarrier s =
      (fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)) '' (Icc (-1 : ℝ) 1 ×ˢ tsupport s.toFun) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨(z.re, z.im), hz, by ext <;> rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨⟨p.1, p.2⟩, s.positive hp.2⟩, hp, rfl⟩
  rw [heq]
  exact (isCompact_Icc.prod s.compact).image (by fun_prop)

def compactHeightLift (s : HeightSeed) (z : UpperHalfPlane) : ℂ :=
  complexHorizontalPartition z.re * s.toFun z.im

theorem compactHeightLift_continuous (s : HeightSeed) : Continuous (compactHeightLift s) :=
  (complexHorizontalPartition_cinfty.continuous.comp UpperHalfPlane.continuous_re).mul
    (s.continuous.comp UpperHalfPlane.continuous_im)

theorem compactHeightLift_support_subset (s t : HeightSeed)
    (ht : tsupport t.toFun ⊆ tsupport s.toFun) :
    Function.support (compactHeightLift t) ⊆ heightProfileCompactCarrier s := by
  intro z hz
  have hn := mul_ne_zero_iff.mp hz
  refine ⟨⟨?_, ?_⟩, ht (subset_tsupport t.toFun hn.2)⟩
  · by_contra h
    apply hn.1
    rw [complexHorizontalPartition, horizontalUnitPartition_zero_left z.re (by linarith),
      Complex.ofReal_zero]
  · by_contra h
    apply hn.1
    rw [complexHorizontalPartition, horizontalUnitPartition_zero_right z.re (by linarith),
      Complex.ofReal_zero]

theorem compactHeightLift_integer_sum (s : HeightSeed) (z : UpperHalfPlane) :
    (∑' k : ℤ, compactHeightLift s (translate k z)) = fourierRadialSeed 0 s.toFun z := by
  have him : ∀ k : ℤ, (translate k z).im = z.im := by
    intro k
    rw [translate_eq_vadd, UpperHalfPlane.vadd_im]
  simp only [compactHeightLift, translate_re, him]
  rw [tsum_mul_right, complexHorizontalPartition_integer_sum, one_mul]
  simp [fourierRadialSeed]

/-- Exact canonical quotient equality, valid for continuous profiles
without smoothness, and for any supplied common original height carrier. -/
theorem seedL2_compactHeightLift_eq_zeroSeed (N : ℕ) [NeZero N] (s t : HeightSeed)
    (ht : tsupport t.toFun ⊆ tsupport s.toFun) :
    seedL2 N (compactHeightLift t) (compactHeightLift_continuous t)
      (heightProfileCompactCarrier s) (heightProfileCompactCarrier_isCompact s)
      (compactHeightLift_support_subset s t ht) = zeroSeedL2 N t := by
  apply Lp.ext
  filter_upwards [seedL2_ae N (compactHeightLift t) (compactHeightLift_continuous t)
    (heightProfileCompactCarrier s) (heightProfileCompactCarrier_isCompact s)
    (compactHeightLift_support_subset s t ht),
    (compactCuspPoincare_memLp_two N 0 t.toFun t.continuous t.compact t.positive).coeFn_toLp,
    reducedProjection_range_ae N] with q hlift hzero hsection
  obtain ⟨z, rfl⟩ := hsection
  rw [hlift, hzero, complexPoincare_projection, parabolicComplexPoincare_projection]
  exact compact_trace_eq_parabolic_of_integer_trace N (compactHeightLift t)
    (fourierRadialSeed 0 t.toFun) (heightProfileCompactCarrier s)
    (heightProfileCompactCarrier_isCompact s) (compactHeightLift_support_subset s t ht)
    (compactHeightLift_integer_sum t) z

/-- Uniform profile approximation is transported into the actual
quotient L2 with one fixed genuine compact-overlap constant. -/
theorem zeroSeedL2_uniform_difference_bound (N : ℕ) [NeZero N] (s t : HeightSeed)
    (ht : tsupport t.toFun ⊆ tsupport s.toFun) {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ y : ℝ, ‖s.toFun y - t.toFun y‖ ≤ ε) :
    ‖zeroSeedL2 N s - zeroSeedL2 N t‖ ≤
      transportConstant N (heightProfileCompactCarrier s) * ε := by
  rw [← seedL2_compactHeightLift_eq_zeroSeed N s s Subset.rfl,
    ← seedL2_compactHeightLift_eq_zeroSeed N s t ht]
  apply seedL2_difference_bound N _ _ (compactHeightLift_continuous s)
    (compactHeightLift_continuous t) (heightProfileCompactCarrier s)
    (heightProfileCompactCarrier_isCompact s) (compactHeightLift_support_subset s s Subset.rfl)
    (compactHeightLift_support_subset s t ht) hε
  intro z _hz
  change ‖complexHorizontalPartition z.re * s.toFun z.im -
    complexHorizontalPartition z.re * t.toFun z.im‖ ≤ ε
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right (complexHorizontalPartition_norm_le_one z.re)
    (norm_nonneg _)).trans (by simpa only [one_mul] using herr z.im)

end
end ImbalancedChen.Part3.GammaZeroSeedCompactLiftContinuity20261026b
