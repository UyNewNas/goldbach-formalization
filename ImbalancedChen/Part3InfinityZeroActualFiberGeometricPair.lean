import ImbalancedChen.Part3InfinityZeroActualFiberFourier
import ImbalancedChen.Part3CompactCuspGeometricFubini

/-!
SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-26.

The positive-d contribution to the actual mixed-cusp strip pairing is
an actual original-coset sum, not an abstract Kloosterman supplier. The
actual conjugated outer seed and the canonical y^-2 density are kept.
Joint L1 and Fubini use the existing real-C compact-kernel theorem at
the matrix-derived C=sqrt(N)*d. The final orbit integral explicitly has
N*d^2 in both rational coordinates. No Bessel evaluation or spectral
formula is asserted. Full quotient/all-d assembly remains OPEN.
-/

noncomputable section

namespace ImbalancedChen.Part3.InfinityZeroActualFiberGeometricPair20261026a

open Set MeasureTheory
open scoped UpperHalfPlane FourierTransform
open ImbalancedChen.Part3.ActualInfinityKloostermanSeed20261025a
open ImbalancedChen.Part3.ActualCompactBruhatKernel20261025a
open ImbalancedChen.Part3.InfinityZeroActualFiberFourier20261026a
open ImbalancedChen.Part3.CompactCuspGeometricFubini20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail

/-- The actual fixed-d strip pairing slice, with the ORIGINAL coset sum. -/
def mixedFiberPairSlice (N : ℕ) (hN : 0 < N) (d : ℕ) (m n : ℤ)
    (ψ φ : ℝ → ℂ) (y : ℝ) : ℂ :=
  if hy : 0 < y then
    ∫ x in (0 : ℝ)..1, ((y⁻¹ ^ 2 : ℝ) : ℂ) *
      star (fourierRadialSeed m ψ (horizontalPoint y hy x)) *
        actualZeroFiber N hN d n φ (horizontalPoint y hy x)
  else 0

/-- The mixed-cusp orbit integral with EVERY level and denominator factor
visible. It retains the -m output phase and +n transformed seed mode. -/
def mixedOrbitKernel (N d : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  radialWeight ψ p.2 * phase (-m) p.1 *
    (phase n (-p.1 / ((N : ℝ) * (d : ℝ) ^ 2 * (p.1 ^ 2 + p.2 ^ 2))) *
      φ (p.2 / ((N : ℝ) * (d : ℝ) ^ 2 * (p.1 ^ 2 + p.2 ^ 2))))

theorem mixedOrbitKernel_eq_realC (N d : ℕ) (m n : ℤ) (ψ φ : ℝ → ℂ) :
    mixedOrbitKernel N d m n ψ φ = geometricPairKernel (zeroModulus N d) m n ψ φ := by
  funext p
  simp only [mixedOrbitKernel, geometricPairKernel, rawBruhatKernel, zeroModulus_sq]

/-- Real-C machinery is used only after actual matrix normalization has
identified C. Thus joint L1 is proved for this specific mixed orbit. -/
theorem mixedOrbitKernel_integrable (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (m n : ℤ) (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (mixedOrbitKernel N d m n ψ φ) (volume : Measure (ℝ × ℝ)) := by
  rw [mixedOrbitKernel_eq_realC]
  exact geometricPairKernel_integrable (zeroModulus N d) (zeroModulus_ne_zero N hN d)
    m n ψ φ hψ hcψ hposψ hφ hcφ hposφ

/-- Actual conjugation and the actual normalized circle integral give
S_d(-m*N^-1,-n), with no sign/order convention left implicit. -/
theorem mixedFiberPairSlice_eq_weightedFourier (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (m n : ℤ) (ψ φ : ℝ → ℂ) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) (y : ℝ) :
    mixedFiberPairSlice N hN d m n ψ φ y =
      (if N.Coprime d then kloosterman d (-m * inverseResidue d (N : ℤ)) (-n) else 0) *
        (radialWeight ψ y * actualFourierSlice (zeroModulus N d)
          (zeroModulus_ne_zero N hN d) m n φ y) := by
  by_cases hy : 0 < y
  · rw [mixedFiberPairSlice, dif_pos hy, actualFourierSlice, dif_pos hy]
    have hpoint (x : ℝ) : ((y⁻¹ ^ 2 : ℝ) : ℂ) *
        star (fourierRadialSeed m ψ (horizontalPoint y hy x)) *
          actualZeroFiber N hN d n φ (horizontalPoint y hy x) =
        radialWeight ψ y * (AddCircle.fourier (-m) (x : UnitAddCircle) *
          actualZeroFiber N hN d n φ (horizontalPoint y hy x)) := by
      simp only [fourierRadialSeed, horizontalPoint, star_mul',
        Complex.star_def, ← AddCircle.fourier_neg, radialWeight]
      ring
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul,
      actualZeroFiber_fourierIntegral N hN d y hy n m φ hφ hcφ hposφ]
    ring
  · simp [mixedFiberPairSlice, actualFourierSlice, hy]

/-- Both genuine radial support floors give a cutoff uniform in ALL y
and x in the paired original fiber. The level is N*d^2, not d^2/N. -/
theorem mixedFiberPairSlice_zero_of_large (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfloorφ : ∀ t, φ t ≠ 0 → a ≤ t) (hfloorψ : ∀ t, ψ t ≠ 0 → b ≤ t)
    (hlarge : 1 < a * ((N : ℝ) * (d : ℝ) ^ 2) * b) (y : ℝ) :
    mixedFiberPairSlice N hN d m n ψ φ y = 0 := by
  by_cases hy : 0 < y
  · by_cases hzero : ψ y = 0
    · simp [mixedFiberPairSlice, hy, fourierRadialSeed, horizontalPoint, hzero]
    · have hby := hfloorψ y hzero
      have hnonneg : 0 ≤ a * ((N : ℝ) * (d : ℝ) ^ 2) := by positivity
      have hlargey : 1 < a * ((N : ℝ) * (d : ℝ) ^ 2) * y :=
        hlarge.trans_le (mul_le_mul_of_nonneg_left hby hnonneg)
      simp only [mixedFiberPairSlice, dif_pos hy,
        actualZeroFiber_zero_of_large N hN d y hy n φ _ a ha hfloorφ hlargey,
        mul_zero, intervalIntegral.integral_zero]
  · simp [mixedFiberPairSlice, hy]

/-- The original fixed-d paired Fourier contribution is genuinely L1. -/
theorem mixedFiberPairSlice_integrable (N : ℕ) (hN : 0 < N) (d : ℕ) [NeZero d]
    (m n : ℤ) (ψ φ : ℝ → ℂ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ)) (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    Integrable (mixedFiberPairSlice N hN d m n ψ φ) := by
  have heq := funext (mixedFiberPairSlice_eq_weightedFourier N hN d m n ψ φ hφ hcφ hposφ)
  rw [heq]
  exact (weighted_actualFourierSlice_integrable (zeroModulus N d)
    (zeroModulus_ne_zero N hN d) m n ψ φ hψ hcψ hposψ hφ hcφ hposφ).const_mul _

/-- A nontrivial geometric mixed-cusp bridge for the ORIGINAL coset fiber:
actual seed pairing -> derived physical arithmetic -> explicit orbit integral.
The interchange is justified by actual compact joint L1, not hAbsSum. -/
theorem integrated_actualMixedFiber_eq_geometric (N : ℕ) (hN : 0 < N)
    (d : ℕ) [NeZero d] (m n : ℤ) (ψ φ : ℝ → ℂ)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hposψ : tsupport ψ ⊆ Ioi (0 : ℝ))
    (hφ : Continuous φ) (hcφ : HasCompactSupport φ) (hposφ : tsupport φ ⊆ Ioi (0 : ℝ)) :
    (∫ y : ℝ, mixedFiberPairSlice N hN d m n ψ φ y) =
      (if N.Coprime d then kloosterman d (-m * inverseResidue d (N : ℤ)) (-n) else 0) *
        ∫ x : ℝ, ∫ y : ℝ, mixedOrbitKernel N d m n ψ φ (x, y) := by
  simp_rw [mixedFiberPairSlice_eq_weightedFourier N hN d m n ψ φ hφ hcφ hposφ]
  rw [integral_const_mul, fixed_modulus_geometric_double_integral (zeroModulus N d)
    (zeroModulus_ne_zero N hN d) m n ψ φ hψ hcψ hposψ hφ hcφ hposφ,
    mixedOrbitKernel_eq_realC]

end ImbalancedChen.Part3.InfinityZeroActualFiberGeometricPair20261026a
