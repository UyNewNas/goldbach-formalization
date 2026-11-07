import ImbalancedChen.Part3ActualCompactPoincareFourier
import ImbalancedChen.Part3CompactCuspParabolicPairing
import Mathlib.MeasureTheory.Integral.Prod

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

The actual fixed-c compact-cusp geometric pairing kernel is jointly
continuous and compactly supported on the full (x,y) plane. Positive
radial support of the OUTER profile kills the apparent y=0 singularity;
positive radial support of the transformed INNER profile supplies a
uniform horizontal support bound. Joint absolute integrability is proved
before Fubini is applied. The resulting double integral keeps the actual
Fourier convention, the negative output-mode phase, conjugation of the
outer radial profile, and the canonical y^{-2} weight.
No spectral or Kuznetsov identity, normalization, or hIntegrable supplier
is introduced.
-/

namespace ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a

noncomputable section
open Set MeasureTheory Filter Topology
open scoped MatrixGroups UpperHalfPlane FourierTransform
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a

/-- Actual normalized period-one character. -/
def phase (m : ℤ) (x : ℝ) : ℂ := AddCircle.fourier m (x : UnitAddCircle)

private theorem phase_continuous (m : ℤ) : Continuous (phase m) :=
  (map_continuous (AddCircle.fourier m)).comp continuous_quotient_mk'

/-- Canonical weight times the conjugated OUTER radial seed. -/
def radialWeight (ψ : ℝ → ℂ) (y : ℝ) : ℂ := ((y⁻¹ ^ 2 : ℝ) : ℂ) * star (ψ y)

/-- The actual rational Bruhat kernel, extended algebraically off y>0. -/
def rawBruhatKernel (c : ℝ) (n : ℤ) (φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  phase n (-p.1 / (c ^ 2 * (p.1 ^ 2 + p.2 ^ 2))) *
    φ (p.2 / (c ^ 2 * (p.1 ^ 2 + p.2 ^ 2)))

/-- Fixed-c geometric pair kernel; output mode m has the NEGATIVE phase,
while the transformed input seed keeps its actual mode n. -/
def geometricPairKernel (c : ℝ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  radialWeight ψ p.2 * phase (-m) p.1 * rawBruhatKernel c n φ p

theorem rawBruhatKernel_eq_actual (c : ℝ) (hc : c ≠ 0) (n : ℤ) (φ : ℝ → ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    rawBruhatKernel c n φ (x, y) = actualKernel c hc y hy n φ x :=
  (actualKernel_formula c hc y hy n φ x).symm

private theorem denominator_ne_zero (c : ℝ) (hc : c ≠ 0) (p : ℝ × ℝ)
    (hy : p.2 ≠ 0) : c ^ 2 * (p.1 ^ 2 + p.2 ^ 2) ≠ 0 :=
  ne_of_gt (mul_pos (sq_pos_of_ne_zero hc)
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hy)))

theorem radialWeight_continuous (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) : Continuous (radialWeight ψ) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  by_cases hy : y = 0
  · have hnot : y ∉ tsupport ψ := by
      intro hm
      have hp := hpos hm
      simpa only [hy, mem_Ioi, lt_self_iff_false] using hp
    have hev : ψ =ᶠ[𝓝 y] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℂ)) y).congr_of_eventuallyEq
    filter_upwards [hev] with t ht
    simp [radialWeight, ht]
  · unfold radialWeight
    fun_prop (disch := exact hy)

theorem radialWeight_hasCompactSupport (ψ : ℝ → ℂ) (hc : HasCompactSupport ψ) :
    HasCompactSupport (radialWeight ψ) := by
  have hstar : HasCompactSupport (fun y => star (ψ y)) :=
    hc.comp_left (g := star) (by simp)
  exact hstar.mul_left

/-- Joint continuity uses actual denominator nonvanishing when y!=0 and
an actual zero neighborhood of the outer seed when y=0. -/
theorem geometricPairKernel_continuous (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Continuous (geometricPairKernel c m n ψ φ) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hy : p.2 = 0
  · have hnot : p.2 ∉ tsupport ψ := by
      intro hm
      have hp := hposψ hm
      simpa only [hy, mem_Ioi, lt_self_iff_false] using hp
    have hevψ : ψ =ᶠ[𝓝 p.2] 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    have hev := continuous_snd.continuousAt hevψ
    apply (continuousAt_const : ContinuousAt (fun _ : ℝ × ℝ => (0 : ℂ)) p).congr_of_eventuallyEq
    filter_upwards [hev] with q hq
    simp [geometricPairKernel, radialWeight, hq]
  · have hd := denominator_ne_zero c hc p hy
    have hre : ContinuousAt (fun q : ℝ × ℝ => -q.1 / (c ^ 2 * (q.1 ^ 2 + q.2 ^ 2))) p := by
      fun_prop (disch := exact hd)
    have him : ContinuousAt (fun q : ℝ × ℝ => q.2 / (c ^ 2 * (q.1 ^ 2 + q.2 ^ 2))) p := by
      fun_prop (disch := exact hd)
    exact (((radialWeight_continuous ψ hψ hposψ).continuousAt.comp p continuous_snd.continuousAt).mul
      ((phase_continuous (-m)).continuousAt.comp p continuous_fst.continuousAt)).mul
        (((phase_continuous n).continuousAt.comp p hre).mul (hφ.continuousAt.comp p him))

/-- Both genuine radial compact supports force compact joint support,
including a uniform horizontal bound for all relevant heights. -/
theorem geometricPairKernel_hasCompactSupport (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (geometricPairKernel c m n ψ φ) := by
  obtain ⟨a, ha, hfloor⟩ := radial_support_positive_floor φ hcφ hposφ
  obtain ⟨b, hb⟩ := hcψ.bddAbove_image continuous_id.continuousOn
  let B : ℝ := max b 0
  let R : ℝ := B / (a * c ^ 2) + 1
  apply HasCompactSupport.of_support_subset_isCompact ((isCompact_Icc : IsCompact (Icc (-R) R)).prod hcψ)
  intro p hp
  have hψne : ψ p.2 ≠ 0 := by
    intro hzero
    exact hp (by simp [geometricPairKernel, radialWeight, hzero])
  have hySupport : p.2 ∈ tsupport ψ := subset_tsupport ψ hψne
  have hy : 0 < p.2 := hposψ hySupport
  have hB : p.2 ≤ B := (hb ⟨p.2, hySupport, rfl⟩).trans (le_max_left b 0)
  have hraw : rawBruhatKernel c n φ p ≠ 0 := right_ne_zero_of_mul hp
  have hkernel : actualKernel c hc p.2 hy n φ p.1 ≠ 0 := by
    rw [← rawBruhatKernel_eq_actual]
    exact hraw
  have hx := actualKernel_support_bound c hc p.2 hy n φ a ha hfloor hkernel
  have hratio := div_le_div_of_nonneg_right hB (mul_pos ha (sq_pos_of_ne_zero hc)).le
  refine ⟨?_, hySupport⟩
  change -R ≤ p.1 ∧ p.1 ≤ R
  dsimp [R]
  constructor <;> linarith [hx.1, hx.2]

/-- Actual joint absolute integrability is a consequence, not a premise. -/
theorem geometricPairKernel_integrable (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (geometricPairKernel c m n ψ φ) (volume : Measure (ℝ × ℝ)) :=
  (geometricPairKernel_continuous c hc m n ψ φ hψ hφ hposψ).integrable_of_hasCompactSupport
    (geometricPairKernel_hasCompactSupport c hc m n ψ φ hcψ hposψ hcφ hposφ)

/-- No guessed Fourier normalization: this is Mathlib's actual real
Fourier transform, with its exact -2*pi*i*x*m character. -/
theorem actualKernel_fourier_eq_phase_integral (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (φ : ℝ → ℂ) (y : ℝ) (hy : 0 < y) :
    𝓕 (actualKernel c hc y hy n φ) (m : ℝ) =
      ∫ x : ℝ, phase (-m) x * rawBruhatKernel c n φ (x, y) := by
  rw [fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  rw [rawBruhatKernel_eq_actual]
  change Complex.exp (↑(-2 * Real.pi * x * (m : ℝ)) * Complex.I) * _ = phase (-m) x * _
  congr 1
  rw [phase, AddCircle.fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- Positive-height Fourier slice, zero outside the actual upper chart. -/
def actualFourierSlice (c : ℝ) (hc : c ≠ 0) (m n : ℤ) (φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then 𝓕 (actualKernel c hc y hy n φ) (m : ℝ) else 0

theorem geometricPairKernel_integral_x (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (y : ℝ) :
    (∫ x : ℝ, geometricPairKernel c m n ψ φ (x, y)) = radialWeight ψ y * actualFourierSlice c hc m n φ y := by
  by_cases hy : 0 < y
  · rw [actualFourierSlice, dif_pos hy, actualKernel_fourier_eq_phase_integral]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    exact mul_assoc _ _ _
  · have hnot : y ∉ tsupport ψ := fun hm => hy (hposψ hm)
    have hzero := image_eq_zero_of_notMem_tsupport hnot
    simp [geometricPairKernel, radialWeight, actualFourierSlice, hy, hzero]

/-- Weighted fixed-c Fourier slice is truly L1, obtained from joint
integrability by Fubini, with no input hIntegrable certificate. -/
theorem weighted_actualFourierSlice_integrable (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (fun y => radialWeight ψ y * actualFourierSlice c hc m n φ y) := by
  have hG : Integrable (geometricPairKernel c m n ψ φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa only [← Measure.volume_eq_prod] using
      geometricPairKernel_integrable c hc m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  exact hG.integral_prod_right.congr
    (Filter.Eventually.of_forall (geometricPairKernel_integral_x c hc m n ψ φ hposψ))

/-- Genuine fixed-c geometric double-integral theorem, with the integral
order exchange justified by the proved compact joint support. -/
theorem fixed_modulus_geometric_double_integral (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ y : ℝ, radialWeight ψ y * actualFourierSlice c hc m n φ y) =
      ∫ x : ℝ, ∫ y : ℝ, geometricPairKernel c m n ψ φ (x, y) := by
  have hG : Integrable (geometricPairKernel c m n ψ φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa only [← Measure.volume_eq_prod] using
      geometricPairKernel_integrable c hc m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  calc
    _ = ∫ y : ℝ, ∫ x : ℝ, geometricPairKernel c m n ψ φ (x, y) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y =>
        (geometricPairKernel_integral_x c hc m n ψ φ hposψ y).symm)
    _ = _ := (integral_integral_swap hG).symm

end
end ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
