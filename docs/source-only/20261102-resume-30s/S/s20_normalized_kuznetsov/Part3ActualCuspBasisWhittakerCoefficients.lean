import ImbalancedChen.Part3ActualCuspSmoothFiniteKernelDescent
import ImbalancedChen.Part3ActualEigenOriginalFourierClassicalModes
import ImbalancedChen.Part3NormalizedCuspHighTailMeasure
import ImbalancedChen.Part3CanonicalHighStripRawEnergy
import ImbalancedChen.Part3ActualRealMaassFourierK
import ImbalancedChen.Part3ActualImaginaryMaassFourierK
import ImbalancedChen.Part3UpperRectangleMollifierGeometry
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The coefficients below belong to the EXISTING entire native cusp Hilbert
basis, represented by its EXISTING single smooth family.  Every normalized
cusp uses that same family and its original quotient measure.  Exact high
cusp measure transport supplies the raw physical strip L2 hypothesis of
the existing real/imaginary K classifications.  Smoothness, periodicity,
PDE, and spatial norm are conclusions, not new hypotheses.

The physical K amplitude rhoK has paper coefficients
rhoW = rhoK/(2*sqrt(|n|)) and R = sqrt(|n|)*rhoW = rhoK/2.
The actual infinity and cusp-one matrices are respectively Id and oldSL;
the latter is the literal [[sqrt(N),0],[sqrt(N),1/sqrt(N)]] matrix.
No replacement basis, raw-rho parameter, spectral measure or trace
identity is postulated.  This is the same-basis coefficient construction;
the full continuous/holomorphic Kuznetsov identity is a separate theorem.

Inherited be3646/0f1f, eigen-regularity and d4d0a/c51501 installation/API
holds remain explicit.  This source neither repairs nor bypasses them.
-/

namespace ImbalancedChen.Part3.ActualCuspBasisWhittakerCoefficients20261102

noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open ActualFullCuspEigenbasis20261026b ActualCuspEigenbasisNativeLabels20261026b
open ActualCuspSmoothEigenprofileFamily20261026b
open ActualCuspSmoothFiniteKernelDescent20261027
open ActualEigenNormalizedSmoothFrame20261026b
open ActualEigenOriginalFourierClassicalModes20261026b
open NormalizedCuspHighTailMeasure20261026b NormalizedCuspCompactQuotientLp20261026b
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0GeneralCuspUnitPeriod20261025a Gamma0GeneralCuspWidth20261025a
open Gamma0ActualCuspsSourceOnly ActualCuspStripCutoff20261025a
open ActualQuotientHighStripL220261026a CanonicalHighStripRawEnergy20261026b
open MaassWeightedCoordinateL220261024zz MaassWeakOperatorCore20261024zz
open CanonicalTensorHyperbolicLaplacianForm20261024z
open Gamma0CompactTensorPoincareC2Core20261025a
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open ActualRealMaassFourierK20261026a ActualImaginaryMaassFourierK20261026b
open RealBesselTailKSelection20261026a ComplexOrderKBridgeSourceOnly
open UpperRectangleMollifierGeometry20261026b
attribute [local instance] Measure.Subtype.measureSpace

variable (N : ℕ) [NeZero N] (hN : 0 < N)

/-- A chart of the already chosen smooth representative, not a new choice. -/
def basisFrame (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) : ℝ × ℝ → ℂ :=
  smoothFrame N g (actualCuspSmoothProfile N hN i)

def basisMode (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) (n : ℤ) : ℝ → ℂ :=
  coefficient (basisFrame N hN i g) n

theorem basisFrame_smooth (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) :
    ContDiffOn ℝ ∞ (basisFrame N hN i g) upperChart :=
  smoothFrame_contDiffOn N hN g _ (actualCuspSmoothProfile_spec N hN i).1

theorem basisFrame_periodic (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ))
    (x y : ℝ) (hy : 0 < y) :
    basisFrame N hN i g (x+1,y) = basisFrame N hN i g (x,y) :=
  smoothFrame_period_one N hN g _ (actualCuspSmoothProfile_spec N hN i).2.2.1 y hy x

/-- The original native eigenvalue governs the ordinary chart PDE. -/
theorem basisFrame_native_PDE (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) :
    ∀ p ∈ upperDomain,
      -(p.2 : ℂ)^2 * (partialX (partialX (basisFrame N hN i g)) p +
        partialY (partialY (basisFrame N hN i g)) p) =
          (actualCuspNativeEigenvalue N hN i : ℂ) * basisFrame N hN i g p := by
  intro p hp
  have hC2 : ContDiffOn ℝ 2 (basisFrame N hN i g) upperDomain :=
    (basisFrame_smooth N hN i g).of_le (by simp)
  have he := smoothFrame_maass N hN g _ (actualCuspSmoothProfile_spec N hN i).1
    (actualCuspNativeEigenvalue N hN i) (actualCuspSmoothProfile_spec N hN i).2.2.2 hp
  change chartMaass (basisFrame N hN i g) p = _ at he
  unfold chartMaass at he
  rw [← positive_C2_laplacian_eq_slices (basisFrame N hN i g) hC2 p hp] at he
  simpa only [euclideanLaplacian, Pi.add_apply, directional, xDirection, yDirection,
    partialX, partialY, neg_mul] using he

/-- The original quotient basis norm supplies spatial L2 in every actual
normalized high cusp.  No Fourier norm or spectral estimate is input. -/
theorem basisFrame_raw_strip_energy (i : actualCuspBasisIndex N hN)
    (g : SL(2, ℤ)) {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun p : PeriodCell × ℝ =>
      p.2⁻¹^2 * ‖basisFrame N hN i g (p.1,p.2)‖^2)
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))) := by
  let U := actualCuspQuotientSmoothProfile N hN i
  let F : UpperHalfPlane → ℂ := fun z =>
    actualCuspSmoothProfile N hN i (frameAction N hN g z)
  have hU : MemLp U 2 (carrierPushforward N) :=
    (Lp.memLp (actualCuspHilbertBasis N hN i : QuotientL2 N)).congr
      (actualCuspQuotientSmoothProfile_ae N hN i).symm
  have hF : MemLp F 2 ((volume : Measure UpperHalfPlane).restrict (highWidthStrip 1 2)) := by
    have h := (hU.mono_measure Measure.restrict_le_self).comp_measurePreserving
      (normalizedHighCusp_measurePreserving N hN g (by norm_num : (1 : ℝ) < 2))
    simpa only [Function.comp_apply, U, F, normalizedCuspQuotientMap,
      actualCuspQuotientSmoothProfile_projection] using h
  have hcompact : MemLp F 2
      ((volume : Measure UpperHalfPlane).restrict (upperRectangle 0 1 Y 2)) := by
    have h := quotient_memLp_frame_compact N hN g
      (upperRectangle_isCompact 0 1 Y 2 hY) hU
    simpa only [frameLift, U, F, actualCuspQuotientSmoothProfile_projection] using h
  have hhigh : IntegrableOn (fun z => ‖F z‖^2) (actualHighStrip Y) :=
    ((hcompact.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).union
      (hF.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0))).mono_set (by
        intro z hz
        by_cases hh : z.im ≤ 2
        · exact Or.inl ⟨⟨hz.2.1, hz.2.2.le⟩, hz.1.le, hh⟩
        · exact Or.inr ⟨hz.2, (lt_of_not_ge hh).le⟩)
  have hraw := canonical_high_strip_raw_energy F hY.le hhigh
  have hyp : ∀ᵐ p : PeriodCell × ℝ ∂
      ((volume : Measure PeriodCell).prod (volume.restrict (Ioi Y))), Y < p.2 := by
    apply (ae_prod_iff_ae_ae (measurable_snd measurableSet_Ioi)).mpr
    exact ae_of_all _ (fun _ => ae_restrict_mem measurableSet_Ioi)
  apply hraw.congr
  filter_upwards [hyp] with p hp
  have hp0 : 0 < p.2 := hY.trans hp
  have heq : chartPullback F (p.1,p.2) = basisFrame N hN i g (p.1,p.2) := by
    rw [basisFrame, smoothFrame_at_upper N hN g _ hp0]
    simp only [chartPullback, dif_pos hp0, F, chartLift_of_positive hp0, complexOfPair]
  rw [heq]

/-- This is the native quotient Fourier coefficient on one conull height
set for all signed indices.  No representative is evaluated on a null slice. -/
theorem basisModes_ae_original (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) :
    ∀ᵐ y ∂((volume : Measure ℝ).restrict (Ioi (0 : ℝ))), ∀ n : ℤ,
      basisMode N hN i g n y =
        frameFourier N hN g (actualCuspHilbertBasis N hN i : QuotientL2 N) n y :=
  classicalFrameModes_ae_original N hN g _ _ (actualCuspSmoothProfile_spec N hN i).2.1

/-- Order determined by the original native eigenvalue; threshold belongs
to the real-order branch, where K_0 is strictly positive. -/
def basisOrder (i : actualCuspBasisIndex N hN) : ℂ :=
  if actualCuspNativeEigenvalue N hN i ≤ 1/4 then
    (Real.sqrt (1/4-actualCuspNativeEigenvalue N hN i) : ℂ)
  else (Real.sqrt (actualCuspNativeEigenvalue N hN i-1/4) : ℂ) * Complex.I

/-- Real and imaginary classifications are applied to the same native
basis, every normalized cusp, and every signed nonzero index. -/
theorem basisMode_unique_K_amplitude_tail (i : actualCuspBasisIndex N hN)
    (g : SL(2, ℤ)) {n : ℤ} (hn : n ≠ 0) {Y : ℝ} (hY : 0 < Y) :
    ∃! rho : ℂ, ∀ y : ℝ, Y < y →
      basisMode N hN i g n y = rho * (Real.sqrt y : ℂ) *
        complexOrderK (basisOrder N hN i) (2*Real.pi*|(n : ℝ)|*y) := by
  have hC2 : ContDiffOn ℝ 2 (basisFrame N hN i g) upperDomain :=
    (basisFrame_smooth N hN i g).of_le (by simp)
  have hp := basisFrame_periodic N hN i g
  have hstrip := basisFrame_raw_strip_energy N hN i g hY
  by_cases hlow : actualCuspNativeEigenvalue N hN i ≤ 1/4
  · let nu : ℝ := Real.sqrt (1/4-actualCuspNativeEigenvalue N hN i)
    have hnu : 0 ≤ nu := Real.sqrt_nonneg _
    have hsq : nu^2 = 1/4-actualCuspNativeEigenvalue N hN i :=
      Real.sq_sqrt (sub_nonneg.mpr hlow)
    have hlabel : (actualCuspNativeEigenvalue N hN i : ℂ) = 1/4-(nu : ℂ)^2 := by
      calc
        _ = ((1/4-nu^2 : ℝ) : ℂ) := congrArg Complex.ofReal (by linarith)
        _ = _ := by push_cast; rfl
    have hPDE : ∀ p ∈ upperDomain,
        -(p.2 : ℂ)^2 * (partialX (partialX (basisFrame N hN i g)) p +
          partialY (partialY (basisFrame N hN i g)) p) =
            (1/4-(nu : ℂ)^2) * basisFrame N hN i g p := by
      intro p hpos
      rw [basisFrame_native_PDE N hN i g p hpos, hlabel]
    have hshape (y : ℝ) (hy : 0 < y) :
        basisMode N hN i g n y =
          realMaassKCoefficient (basisFrame N hN i g) n nu * (Real.sqrt y : ℂ) *
            complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) :=
      actual_nonzero_coefficient_eq_realK hC2 hp hnu hPDE hY hstrip hn hy
    have hord : basisOrder N hN i = (nu : ℂ) := by simp only [basisOrder, if_pos hlow, nu]
    refine ⟨realMaassKCoefficient (basisFrame N hN i g) n nu, ?_, ?_⟩
    · intro y hy
      rw [hord]
      exact hshape y (hY.trans hy)
    · intro d hd
      have hanchor : 0 < Y+1 := by linarith
      have hden : (Real.sqrt (Y+1) : ℂ) *
          complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*(Y+1)) ≠ 0 := by
        apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hanchor).ne')
        apply actualRealK_ne_zero
        have ha := modeFrequency_pos hn
        exact mul_pos ha hanchor
      apply mul_right_cancel₀ hden
      have he := (hd (Y+1) (by linarith)).symm.trans (hshape (Y+1) hanchor)
      simpa only [hord, mul_assoc, basisMode] using he
  · let tau : ℝ := Real.sqrt (actualCuspNativeEigenvalue N hN i-1/4)
    have hsq : tau^2 = actualCuspNativeEigenvalue N hN i-1/4 :=
      Real.sq_sqrt (by linarith : 0 ≤ actualCuspNativeEigenvalue N hN i-1/4)
    have hlabel : (actualCuspNativeEigenvalue N hN i : ℂ) = ((1/4+tau^2 : ℝ) : ℂ) :=
      congrArg Complex.ofReal (by linarith)
    have hPDE : ∀ p ∈ upperDomain,
        -(p.2 : ℂ)^2 * (partialX (partialX (basisFrame N hN i g)) p +
          partialY (partialY (basisFrame N hN i g)) p) =
            ((1/4+tau^2 : ℝ) : ℂ) * basisFrame N hN i g p := by
      intro p hpos
      rw [basisFrame_native_PDE N hN i g p hpos, hlabel]
    have h := actual_nonzero_coefficient_eq_unique_imaginaryK hC2 hp hPDE hn hY hstrip
    simpa only [basisMode, basisOrder, if_neg hlow, tau] using h

/-- Chosen only from the preceding actual PDE theorem.  The zero-mode
extension is unused by the nonzero trace and creates no spectral datum. -/
def basisRhoK (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) (n : ℤ) : ℂ :=
  if hn : n ≠ 0 then Classical.choose
    (basisMode_unique_K_amplitude_tail N hN i g hn (by norm_num : (0 : ℝ) < 2)) else 0

theorem basisMode_eq_K (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ))
    {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    basisMode N hN i g n y = basisRhoK N hN i g n * (Real.sqrt y : ℂ) *
      complexOrderK (basisOrder N hN i) (2*Real.pi*|(n : ℝ)|*y) := by
  let Y : ℝ := min 2 (y/2)
  have hY : 0 < Y := lt_min (by norm_num) (half_pos hy)
  obtain ⟨rho, hshape, _⟩ := basisMode_unique_K_amplitude_tail N hN i g hn hY
  have hrho : rho = basisRhoK N hN i g n := by
    rw [basisRhoK, dif_pos hn]
    apply (Classical.choose_spec
      (basisMode_unique_K_amplitude_tail N hN i g hn (by norm_num : (0 : ℝ) < 2))).2
    intro t ht
    exact hshape t (lt_of_le_of_lt (min_le_left _ _) ht)
  rw [← hrho]
  exact hshape y (lt_of_le_of_lt (min_le_right _ _) (by linarith))

/-- One coefficient serves all positive heights.  Low compact bands and
the exact high cusp measure paid the tail hypothesis above. -/
theorem basisMode_unique_K_amplitude (i : actualCuspBasisIndex N hN)
    (g : SL(2, ℤ)) {n : ℤ} (hn : n ≠ 0) :
    ∃! rho : ℂ, ∀ y : ℝ, 0 < y →
      basisMode N hN i g n y = rho * (Real.sqrt y : ℂ) *
        complexOrderK (basisOrder N hN i) (2*Real.pi*|(n : ℝ)|*y) := by
  refine ⟨basisRhoK N hN i g n, fun y hy => basisMode_eq_K N hN i g hn hy, ?_⟩
  intro rho hrho
  rw [basisRhoK, dif_pos hn]
  apply (Classical.choose_spec
    (basisMode_unique_K_amplitude_tail N hN i g hn (by norm_num : (0 : ℝ) < 2))).2
  intro y hy
  exact hrho y (by linarith)

def basisRhoW (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) (n : ℤ) : ℂ :=
  basisRhoK N hN i g n / (2 * (Real.sqrt |(n : ℝ)| : ℂ))

def basisR (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ)) (n : ℤ) : ℂ :=
  (Real.sqrt |(n : ℝ)| : ℂ) * basisRhoW N hN i g n

private theorem sqrt_abs_ne_zero {n : ℤ} (hn : n ≠ 0) :
    (Real.sqrt |(n : ℝ)| : ℂ) ≠ 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hnR)).ne'

theorem basisR_eq_half_native (i : actualCuspBasisIndex N hN) (g : SL(2, ℤ))
    {n : ℤ} (hn : n ≠ 0) :
    basisR N hN i g n = basisRhoK N hN i g n / 2 := by
  unfold basisR basisRhoW
  field_simp [sqrt_abs_ne_zero hn] <;> ring

/-- The exact physical Whittaker expression, with no newly defined W. -/
theorem basisMode_eq_Whittaker_normalization (i : actualCuspBasisIndex N hN)
    (g : SL(2, ℤ)) {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    basisMode N hN i g n y = basisRhoW N hN i g n *
      (2 * (Real.sqrt (|(n : ℝ)|*y) : ℂ)) *
        complexOrderK (basisOrder N hN i) (2*Real.pi*|(n : ℝ)|*y) := by
  rw [basisMode_eq_K N hN i g hn hy, Real.sqrt_mul (abs_nonneg _),
    Complex.ofReal_mul, basisRhoW]
  field_simp [sqrt_abs_ne_zero hn] <;> ring

theorem basisMode_eq_normalizedR (i : actualCuspBasisIndex N hN)
    (g : SL(2, ℤ)) {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    basisMode N hN i g n y = (2*basisR N hN i g n) * (Real.sqrt y : ℂ) *
      complexOrderK (basisOrder N hN i) (2*Real.pi*|(n : ℝ)|*y) := by
  rw [basisMode_eq_K N hN i g hn hy, basisR_eq_half_native N hN i g hn]
  ring

/-- Conjugation is on the infinity-side coefficient in the actual same
basis product.  The exact normalization factor is one quarter. -/
theorem basisR_product (i : actualCuspBasisIndex N hN) (g h : SL(2, ℤ))
    {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    starRingEnd ℂ (basisR N hN i g m) * basisR N hN i h n =
      (starRingEnd ℂ (basisRhoK N hN i g m) * basisRhoK N hN i h n)/4 := by
  rw [basisR_eq_half_native N hN i g hm, basisR_eq_half_native N hN i h hn]
  simp only [map_div]
  norm_num <;> ring

theorem basis_scaling_infinity : normalizedScaling N hN (1 : SL(2, ℤ)) = 1 := by
  apply Subtype.ext
  rw [normalizedScaling_entries, cuspWidth_infinity N hN]
  ext i j <;> fin_cases i <;> fin_cases j <;> norm_num

theorem basis_scaling_one : normalizedScaling N hN cuspOneMatrix =
    P3ActualCuspScalingSourceOnly.oldSL (N : ℝ) (by exact_mod_cast hN) :=
  normalizedScaling_cuspOne N hN

theorem basisMode_eq_fixed_scaling_integral (i : actualCuspBasisIndex N hN)
    (g : SL(2, ℤ)) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    basisMode N hN i g n y = ∫ x in Ico (0 : ℝ) 1,
      _root_.fourier (-n) (x : UnitAddCircle) *
        actualCuspSmoothProfile N hN i
          (normalizedScaling N hN g • ActualCuspFourierSectionSourceOnly.horizontal y hy x) := by
  rw [basisMode, coefficient_eq_Ico]
  apply setIntegral_congr_fun measurableSet_Ico
  intro x _
  rw [basisFrame, smoothFrame_at_upper N hN g _ hy]
  simp only [frameAction, chartLift_of_positive hy,
    ActualCuspFourierSectionSourceOnly.horizontal, complexOfPair]

end
end ImbalancedChen.Part3.ActualCuspBasisWhittakerCoefficients20261102
