import ImbalancedChen.Part3CanonicalHighStripRawEnergy
import ImbalancedChen.Part3ActualRealMaassFourierK

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The nonzero literal Fourier coefficient of an actual quotient L2 Maass
function is its actual real-order K mode, including nu=0. Quotient L2,
the original C2 chart and its original PDE are the only analytic inputs.
The amplitude rho is fixed by the coefficient at height one; the ABL
normalization is R(n)=sqrt(|n|) rho(n). No spectral expansion is asserted.
-/

namespace ImbalancedChen.Part3.QuotientRealKFourierCoefficient20261026b
noncomputable section
open Set MeasureTheory
open scoped UpperHalfPlane
open CanonicalHighStripRawEnergy20261026b ActualRealMaassFourierK20261026a
open ActualPoincareSpectralCoefficient20261026a ActualMaassFourierODE20261026a
open ActualFourierBesselConjugation20261026a ComplexOrderKBridgeSourceOnly
open Gamma0QuotientCellPushforward20261025a GammaInfinityTranslationStrip20261025a
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeightedCoordinateL220261024zz
attribute [local instance] Measure.Subtype.measureSpace

def maassChart (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) : ℝ × ℝ → ℂ :=
  chartPullback (testLift N U)

/-- The horizontal period is obtained from actual quotient invariance. -/
theorem maassChart_periodic (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (x y : ℝ) (hy : 0 < y) : maassChart N U (x+1,y) = maassChart N U (x,y) := by
  let z : UpperHalfPlane := ⟨⟨x,y⟩,hy⟩
  have ht : translate 1 z = (⟨⟨x+1,y⟩,hy⟩ : UpperHalfPlane) := by
    rw [translate_eq_vadd]
    apply UpperHalfPlane.ext
    ext <;> simp [z, UpperHalfPlane.coe_vadd] <;> ring
  have h := testLift_periodic N U 1 z
  rw [ht] at h
  simpa only [maassChart, chartPullback, upperChart, mem_setOf_eq, hy, dif_pos, z] using h

/-- The two independently constructed literal coefficients agree, including
their negative exponential and width-one normalization. -/
theorem actualTestFourier_eq_coefficient (N : ℕ) (U : Gamma0OrbitSpace N → ℂ)
    (n : ℤ) (y : ℝ) :
    actualTestFourier N U n y = coefficient (maassChart N U) n y := by
  rw [actualTestFourier_eq_interval, coefficient, periodIntegral_eq_interval]
  rfl

def quotientRho (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (nu : ℝ) (n : ℤ) : ℂ :=
  realMaassKCoefficient (maassChart N U) n nu

def quotientR (N : ℕ) (U : Gamma0OrbitSpace N → ℂ) (nu : ℝ) (n : ℤ) : ℂ :=
  (Real.sqrt |(n : ℝ)| : ℂ) * quotientRho N U nu n

variable (N : ℕ) [NeZero N] (U : Gamma0OrbitSpace N → ℂ)
  (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N))
  (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
  (nu : ℝ) (hnu : 0 ≤ nu)
  (hPDE : ∀ p ∈ upperDomain,
    -(p.2 : ℂ)^2 * (partialX (partialX (maassChart N U)) p +
      partialY (partialY (maassChart N U)) p) = (1/4-(nu : ℂ)^2)*maassChart N U p)

/-- End-to-end actual quotient theorem. This includes all exceptional
real orders and the threshold eigenvalue lambda=1/4. -/
theorem actual_quotient_fourier_eq_realK {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N U n y = quotientRho N U nu n * (Real.sqrt y : ℂ) *
      complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) := by
  rw [actualTestFourier_eq_coefficient]
  exact actual_nonzero_coefficient_eq_realK hC2 (maassChart_periodic N U) hnu hPDE
    (by norm_num : (0 : ℝ) < 1) (actual_quotient_raw_strip_energy N U hU hU2 1 le_rfl) hn hy

/-- The Maass amplitude is explicitly determined by a positive-height
literal Fourier coefficient; actual K positivity pays for division. -/
theorem quotientRho_eq_value_at {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    quotientRho N U nu n = actualTestFourier N U n y /
      ((Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (modeFrequency n*y)) := by
  rw [actualTestFourier_eq_coefficient]
  exact realMaassKCoefficient_eq_value_at hC2 (maassChart_periodic N U) hnu hPDE
    (by norm_num : (0 : ℝ) < 1) (actual_quotient_raw_strip_energy N U hU hU2 1 le_rfl) hn hy

theorem quotientR_div_sqrt {n : ℤ} (hn : n ≠ 0) :
    quotientR N U nu n / (Real.sqrt |(n : ℝ)| : ℂ) = quotientRho N U nu n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hs : (Real.sqrt |(n : ℝ)| : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hnR)).ne'
  exact mul_div_cancel_left₀ _ hs

end
end ImbalancedChen.Part3.QuotientRealKFourierCoefficient20261026b
