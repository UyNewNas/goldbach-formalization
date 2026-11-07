import ImbalancedChen.Part3CompactCuspQuotientGeometricPairing
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

Actual fixed-double-coset Archimedean orbital integral. The change of
Fourier variable x=y*u is proved with its exact Jacobian: dx*dy/y^2
becomes du*dy/y. Both transformed radial heights and both Fourier phases
are retained. Compact positive radial support proves joint compact
support/L1 after the nonconstant dilation, hence licenses both orders of
integration. This is a genuine geometric precursor; it is not an
unproved identification with the Kuznetsov J/K transform.
-/

namespace ImbalancedChen.Part3.PoincareOrbitalDilation20261026a

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a

/-- The actual variable x=y*u, including its positive-height Jacobian y.
The signed extension off the upper chart is harmless because the outer
positive-height radial seed is identically zero there. -/
def dilatedOrbitalKernel (c : ℝ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2 : ℂ) * geometricPairKernel c m n ψ φ (p.2 * p.1, p.2)

/-- Actual transformed imaginary part after x=y*u. -/
def orbitalHeight (c y u : ℝ) : ℝ := 1 / (c ^ 2 * y * (1 + u ^ 2))

/-- Exact positive-frequency oscillation, with the original negative
Fourier sign on BOTH the output mode and the transformed input phase. -/
def orbitalPhase (c : ℝ) (m n : ℤ) (y u : ℝ) : ℝ :=
  2 * Real.pi * ((m : ℝ) * y * u + (n : ℝ) * u * orbitalHeight c y u)

/-- Explicit dimensionless kernel: the canonical radial measure is dy/y.
No factor of 2, pi, or the modulus c has been absorbed into a measure. -/
def explicitOrbitalKernel (c : ℝ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.2⁻¹ : ℂ) * star (ψ p.2) *
    Complex.exp (-Complex.I * (orbitalPhase c m n p.2 p.1 : ℂ)) *
      φ (orbitalHeight c p.2 p.1)

private theorem phase_eq_exp (k : ℤ) (x : ℝ) :
    phase k x = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * (x : ℂ)) := by
  simp only [phase, AddCircle.fourier_coe_apply, div_one]

/-- Algebraic Fourier-variable dictionary on the actual positive chart. -/
theorem dilatedOrbitalKernel_eq_explicit (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (y : ℝ) (hy : 0 < y) (u : ℝ) :
    dilatedOrbitalKernel c m n ψ φ (u, y) = explicitOrbitalKernel c m n ψ φ (u, y) := by
  have hy0 := hy.ne'
  have hd : 1 + u ^ 2 ≠ 0 := ne_of_gt (by positivity : 0 < 1 + u ^ 2)
  have hden : c ^ 2 * ((y * u) ^ 2 + y ^ 2) = c ^ 2 * y ^ 2 * (1 + u ^ 2) := by ring
  have him : y / (c ^ 2 * ((y * u) ^ 2 + y ^ 2)) = orbitalHeight c y u := by
    dsimp [orbitalHeight]
    rw [hden]
    field_simp [hc, hy0, hd]
    <;> ring
  have hre : -(y * u) / (c ^ 2 * ((y * u) ^ 2 + y ^ 2)) = -u * orbitalHeight c y u := by
    dsimp [orbitalHeight]
    rw [hden]
    field_simp [hc, hy0, hd]
    <;> ring
  have hweight : (y : ℂ) * ((y⁻¹ ^ 2 : ℝ) : ℂ) = (y⁻¹ : ℂ) := by
    push_cast
    field_simp [hy0]
  have hphase : phase (-m) (y * u) * phase n (-u * orbitalHeight c y u) =
      Complex.exp (-Complex.I * (orbitalPhase c m n y u : ℂ)) := by
    rw [phase_eq_exp, phase_eq_exp, ← Complex.exp_add]
    congr 1
    dsimp [orbitalPhase]
    push_cast
    ring
  change (y : ℂ) *
    ((((y⁻¹ ^ 2 : ℝ) : ℂ) * star (ψ y) * phase (-m) (y * u)) *
      (phase n (-(y * u) / (c ^ 2 * ((y * u) ^ 2 + y ^ 2))) *
        φ (y / (c ^ 2 * ((y * u) ^ 2 + y ^ 2))))) = _
  rw [him, hre]
  calc
    _ = ((y : ℂ) * ((y⁻¹ ^ 2 : ℝ) : ℂ)) * star (ψ y) *
        (phase (-m) (y * u) * phase n (-u * orbitalHeight c y u)) *
          φ (orbitalHeight c y u) := by ring
    _ = _ := by rw [hweight, hphase]; rfl
/-- The zero extension in the actual upper chart agrees as well. -/
theorem dilatedOrbitalKernel_eq_explicit_all (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    dilatedOrbitalKernel c m n ψ φ = explicitOrbitalKernel c m n ψ φ := by
  funext p
  by_cases hy : 0 < p.2
  · exact dilatedOrbitalKernel_eq_explicit c hc m n ψ φ p.2 hy p.1
  · have hz : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hy (hposψ hm))
    simp [dilatedOrbitalKernel, explicitOrbitalKernel, geometricPairKernel, radialWeight, hz]

theorem dilatedOrbitalKernel_continuous (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hφ : Continuous φ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) : Continuous (dilatedOrbitalKernel c m n ψ φ) :=
  (Complex.continuous_ofReal.comp continuous_snd).mul
    ((geometricPairKernel_continuous c hc m n ψ φ hψ hφ hposψ).comp
      ((continuous_snd.mul continuous_fst).prodMk continuous_snd))

/-- Positive lower support of the OUTER seed makes x=y*u a proper change
on the real joint support; a horizontal support bound then bounds u. -/
theorem dilatedOrbitalKernel_hasCompactSupport (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    HasCompactSupport (dilatedOrbitalKernel c m n ψ φ) := by
  obtain ⟨a, ha, hfloorφ⟩ := radial_support_positive_floor φ hcφ hposφ
  obtain ⟨b, hb, hfloorψ⟩ := radial_support_positive_floor ψ hcψ hposψ
  obtain ⟨B₀, hB₀⟩ := hcψ.bddAbove_image continuous_id.continuousOn
  let B : ℝ := max B₀ 0
  let R : ℝ := B / (a * c ^ 2) + 1
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_Icc : IsCompact (Icc (-(R / b)) (R / b))).prod hcψ)
  intro p hp
  have hG : geometricPairKernel c m n ψ φ (p.2 * p.1, p.2) ≠ 0 := right_ne_zero_of_mul hp
  have hψne : ψ p.2 ≠ 0 := by
    intro hz
    exact hG (by simp [geometricPairKernel, radialWeight, hz])
  have hsψ := subset_tsupport ψ hψne
  have hy : 0 < p.2 := hposψ hsψ
  have hBy : p.2 ≤ B := (hB₀ ⟨p.2, hsψ, rfl⟩).trans (le_max_left B₀ 0)
  have hraw : rawBruhatKernel c n φ (p.2 * p.1, p.2) ≠ 0 := right_ne_zero_of_mul hG
  have hkernel : actualKernel c hc p.2 hy n φ (p.2 * p.1) ≠ 0 := by
    rw [← rawBruhatKernel_eq_actual]
    exact hraw
  have hx := actualKernel_support_bound c hc p.2 hy n φ a ha hfloorφ hkernel
  have hratio := div_le_div_of_nonneg_right hBy (mul_pos ha (sq_pos_of_ne_zero hc)).le
  have hxR : |p.2 * p.1| ≤ R := by
    rw [abs_le]
    dsimp [R]
    constructor <;> linarith [hx.1, hx.2]
  have hu : |p.1| ≤ R / b := by
    apply (le_div_iff₀ hb).mpr
    calc
      |p.1| * b ≤ |p.1| * p.2 := mul_le_mul_of_nonneg_left (hfloorψ _ hψne) (abs_nonneg _)
      _ = |p.2 * p.1| := by rw [abs_mul, abs_of_pos hy]; ring
      _ ≤ R := hxR
  exact ⟨abs_le.mp hu, hsψ⟩

/-- The actual nonconstant coordinate dilation has genuine joint L1. -/
theorem dilatedOrbitalKernel_integrable (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (dilatedOrbitalKernel c m n ψ φ) (volume : Measure (ℝ × ℝ)) :=
  (dilatedOrbitalKernel_continuous c hc m n ψ φ hψ hφ hposψ).integrable_of_hasCompactSupport
    (dilatedOrbitalKernel_hasCompactSupport c hc m n ψ φ hcψ hposψ hcφ hposφ)

/-- Exact one-dimensional dilation, with the Jacobian proved from Haar
measure rather than inserted into an orbital-transform definition. -/
theorem orbital_dilation_integral_u (c : ℝ) (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (y : ℝ) :
    (∫ u : ℝ, dilatedOrbitalKernel c m n ψ φ (u, y)) =
      ∫ x : ℝ, geometricPairKernel c m n ψ φ (x, y) := by
  by_cases hy : 0 < y
  · simp only [dilatedOrbitalKernel]
    rw [integral_const_mul,
      Measure.integral_comp_mul_left (fun x => geometricPairKernel c m n ψ φ (x, y)) y,
      abs_of_pos (inv_pos.mpr hy), Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hy.ne', Complex.ofReal_one, one_mul]
  · have hz : ψ y = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hy (hposψ hm))
    simp [dilatedOrbitalKernel, geometricPairKernel, radialWeight, hz]

/-- Actual orbital double-integral identity with the explicit Fourier
variable and exact canonical measure factor. All integral-order exchanges
are justified by the existing actual joint L1 theorem. -/
theorem actual_orbital_eq_explicit_dimensionless (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ x : ℝ, ∫ y : ℝ, geometricPairKernel c m n ψ φ (x, y)) =
      ∫ y : ℝ, ∫ u : ℝ, explicitOrbitalKernel c m n ψ φ (u, y) := by
  have hG : Integrable (geometricPairKernel c m n ψ φ)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    simpa only [← Measure.volume_eq_prod] using
      geometricPairKernel_integrable c hc m n ψ φ hψ hcψ hposψ hφ hcφ hposφ
  rw [integral_integral_swap hG]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  rw [← orbital_dilation_integral_u c m n ψ φ hposψ y,
    dilatedOrbitalKernel_eq_explicit_all c hc m n ψ φ hposψ]

/-- Joint absolute integrability of the EXPLICIT dimensionless formula
is a theorem, not an assumed oscillatory convergence certificate. -/
theorem explicitOrbitalKernel_integrable (c : ℝ) (hc : c ≠ 0) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (explicitOrbitalKernel c m n ψ φ) (volume : Measure (ℝ × ℝ)) := by
  rw [← dilatedOrbitalKernel_eq_explicit_all c hc m n ψ φ hposψ]
  exact dilatedOrbitalKernel_integrable c hc m n ψ φ hψ hcψ hposψ hφ hcφ hposφ

end
end ImbalancedChen.Part3.PoincareOrbitalDilation20261026a
