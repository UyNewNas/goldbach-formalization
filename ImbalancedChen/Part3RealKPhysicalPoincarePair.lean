import ImbalancedChen.Part3QuotientRealKFourierCoefficient

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Exact real-order K spectral coefficient of the actual physical width-one
seed e(nx) psi(y), periodized on the actual Gamma0 quotient. The conjugate
falls on psi, the measure is dy/y^2, and R=sqrt(|n|)rho. Compact positive
radial support independently proves the radial transform is integrable.
This is an individual Maass pairing, with no spectral completeness or
automorphic Plancherel density assertion.
-/

namespace ImbalancedChen.Part3.RealKPhysicalPoincarePair20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open QuotientRealKFourierCoefficient20261026b ActualPoincareSpectralCoefficient20261026a
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open ComplexOrderKBridgeSourceOnly ComplexOrderKQCalculus
open Gamma0QuotientCellPushforward20261025a Gamma0ParabolicEffectiveDecomposition20261025a
open Gamma0QuotientConullTransport20261025a ActualInfinityKloostermanSeed20261025a
open CompactCuspParabolicL220261025a

def realKSeedIntegrand (n : ℤ) (nu : ℝ) (ψ : ℝ → ℂ) (y : ℝ) : ℂ :=
  ((y⁻¹)^2 : ℝ) • (star (ψ y) *
    ((Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (modeFrequency n*y)))

def realKSeedTransform (n : ℤ) (nu : ℝ) (ψ : ℝ → ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), realKSeedIntegrand n nu ψ y

/-- Compact positive support pays for absolute integrability independently
of whether the selected Maass Fourier coefficient vanishes. -/
theorem realKSeedIntegrand_integrable {n : ℤ} (hn : n ≠ 0) (nu : ℝ)
    (ψ : ℝ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (hpos : tsupport ψ ⊆ Ioi (0 : ℝ)) :
    Integrable (realKSeedIntegrand n nu ψ) := by
  have hK : ContinuousOn (fun y => complexOrderK (nu : ℂ) (modeFrequency n*y))
      (Ioi (0 : ℝ)) := by
    intro y hy
    exact ((complexOrderK_hasDerivAt_q (nu : ℂ)
      (mul_pos (modeFrequency_pos hn) hy)).continuousAt.comp
      (continuous_const.mul continuous_id).continuousAt).continuousWithinAt
  have hcont : ContinuousOn (realKSeedIntegrand n nu ψ) (Ioi (0 : ℝ)) :=
    (((continuousOn_id.inv₀ (fun y hy => hy.ne')).pow 2).smul
      (hψ.star.continuousOn.mul
        ((Complex.continuous_ofReal.comp Real.continuous_sqrt).continuousOn.mul hK)))
  have hsupp : Function.support (realKSeedIntegrand n nu ψ) ⊆ tsupport ψ := by
    intro y hy
    by_contra hout
    exact hy (by simp [realKSeedIntegrand, image_eq_zero_of_notMem_tsupport hout])
  exact (integrableOn_iff_integrable_of_support_subset hsupp).mp
    ((hcont.mono hpos).integrableOn_compact hc)

variable (N : ℕ) [NeZero N] (U : Gamma0OrbitSpace N → ℂ)
  (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N))
  (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
  (nu : ℝ) (hnu : 0 ≤ nu)
  (hPDE : ∀ p ∈ upperDomain,
    -(p.2 : ℂ)^2 * (partialX (partialX (maassChart N U)) p +
      partialY (partialY (maassChart N U)) p) = (1/4-(nu : ℂ)^2)*maassChart N U p)
  {n : ℤ} (hn : n ≠ 0) (ψ : ℝ → ℂ) (hψ : Continuous ψ)
  (hc : HasCompactSupport ψ) (hpos : tsupport ψ ⊆ Ioi (0 : ℝ))

/-- Actual physical Poincare pairing, with the proved individual K
coefficient and all seed and height normalizations retained. -/
theorem actual_physical_poincare_pair_eq_rho_realK :
    (∫ q, star (parabolicComplexPoincare N (fourierRadialSeed n ψ) q) * U q
      ∂carrierPushforward N) = quotientRho N U nu n * realKSeedTransform n nu ψ := by
  rw [actual_quotient_pairing_eq_fourier N n ψ hψ hc hpos U hU,
    realKSeedTransform, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
  rw [actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hn hy]
  simp only [realKSeedIntegrand, Complex.real_smul, modeFrequency]
  ring

/-- Literal manuscript normalization R(n)=sqrt(|n|)rho(n). There is no
extra 2*pi, cusp width, square-root height, or spectral measure factor. -/
theorem actual_physical_poincare_pair_eq_R_realK :
    (∫ q, star (parabolicComplexPoincare N (fourierRadialSeed n ψ) q) * U q
      ∂carrierPushforward N) =
      (quotientR N U nu n / (Real.sqrt |(n : ℝ)| : ℂ)) * realKSeedTransform n nu ψ := by
  rw [quotientR_div_sqrt N U nu hn]
  exact actual_physical_poincare_pair_eq_rho_realK N U hU hU2 hC2 nu hnu hPDE hn ψ hψ hc hpos

/-- The same formula for the actual quotient Hilbert inner product;
both vectors and the scalar radial transform are genuinely integrable. -/
theorem actual_physical_poincare_inner_eq_R_realK :
    inner ℂ ((compactCuspPoincare_memLp_two N n ψ hψ hc hpos).toLp
      (parabolicComplexPoincare N (fourierRadialSeed n ψ))) (hU2.toLp U) =
      (quotientR N U nu n / (Real.sqrt |(n : ℝ)| : ℂ)) * realKSeedTransform n nu ψ := by
  rw [actual_poincare_L2_inner_eq_fourier N n ψ hψ hc hpos U hU hU2,
    ← actual_quotient_pairing_eq_fourier N n ψ hψ hc hpos U hU]
  exact actual_physical_poincare_pair_eq_R_realK N U hU hU2 hC2 nu hnu hPDE hn ψ hψ hc hpos

end
end ImbalancedChen.Part3.RealKPhysicalPoincarePair20261026b
