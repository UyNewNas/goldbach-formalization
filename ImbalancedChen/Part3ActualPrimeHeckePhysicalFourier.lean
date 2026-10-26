import ImbalancedChen.Part3ActualPrimeHeckeQuotientDescent
import ImbalancedChen.Part3ActualHeckeAllRealK
import ImbalancedChen.Part3ActualCommonIntervalCompletionL1
import Mathlib.Data.Fintype.BigOperators

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
The genuinely descended Gamma0 quotient Hecke operator is identified with
the original physical p^-1/2[u(pz)+sum_{b<p}u((z+b)/p)] expression. Its
literal quotient Fourier coefficients have the proved physical height
arguments and correct divisibility branches. Genuine original quotient
Maass L2 and PDE hypotheses further give its actual real-K coefficients.
No transformed L2 bound, spectral realization or completeness is assumed.
-/

namespace ImbalancedChen.Part3.ActualPrimeHeckePhysicalFourier20261026b
noncomputable section
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup MatrixGroups
open scoped MatrixGroups UpperHalfPlane BigOperators
open ActualPrimeHeckeBranchSeparation20261026b ActualPrimeHeckeRealBranch20261026b
open ActualPrimeHeckeQuotientDescent20261026b ActualHeckeAllRealK20261026b
open ActualHeckeAllFourier20261026b ActualHeckeDivisibleFourier20261026b
open ActualHeckeTranslationProjector20261026b QuotientRealKFourierCoefficient20261026b
open ActualPoincareSpectralCoefficient20261026a ActualMaassFourierODE20261026a
open Gamma0QuotientCellPushforward20261025a ComplexOrderKBridgeSourceOnly
open CanonicalPlanarL2UnitarySourceOnly MaassWeightedCoordinateL220261024zz
open ActualCommonIntervalCompletionL1SourceOnly

theorem branch_chart_none (p : ℕ) (hp : 0 < p) (z : ℍ) :
    chartMap (branchSL p hp none • z) = ((p : ℝ)*z.re, (p : ℝ)*z.im) := by
  apply Prod.ext
  · change (branchSL p hp none • z).re = _
    simpa using congrArg Complex.re (branchSL_none_coe p hp z)
  · change (branchSL p hp none • z).im = _
    simpa using congrArg Complex.im (branchSL_none_coe p hp z)

theorem branch_chart_some (p : ℕ) (hp : 0 < p) (b : ZMod p) (z : ℍ) :
    chartMap (branchSL p hp (some b) • z) =
      ((z.re+(b.val : ℝ))/(p : ℝ), z.im/(p : ℝ)) := by
  apply Prod.ext
  · change (branchSL p hp (some b) • z).re = _
    simpa only [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.add_re,
      Complex.ofReal_re] using congrArg Complex.re (branchSL_some_coe p hp b z)
  · change (branchSL p hp (some b) • z).im = _
    simpa only [← Complex.ofReal_natCast, Complex.div_ofReal_im, Complex.add_im,
      Complex.ofReal_im, add_zero] using congrArg Complex.im (branchSL_some_coe p hp b z)

/-- Exact p+1 native branch sum = original literal physical expression.
The integer residue sum is reindexed using its proved canonical values. -/
theorem nativeHecke_eq_physical (p : ℕ) (hp : 0 < p) (f : ℍ → ℂ) (z : ℍ) :
    nativeHecke p hp f z = primeHeckeExpression p (chartPullback f) (chartMap z) := by
  letI : NeZero p := ⟨hp.ne'⟩
  have hnone : f (branchSL p hp none • z) =
      chartPullback f ((p : ℝ)*z.re, (p : ℝ)*z.im) := by
    rw [← chartPullback_at_upper f (branchSL p hp none • z), branch_chart_none]
  have hsome (b : ZMod p) : f (branchSL p hp (some b) • z) =
      chartPullback f ((z.re+(b.val : ℝ))/(p : ℝ), z.im/(p : ℝ)) := by
    rw [← chartPullback_at_upper f (branchSL p hp (some b) • z), branch_chart_some]
  have hsum : (∑ j : Branch p, f (branchSL p hp j • z)) =
      chartPullback f ((p : ℝ)*z.re, (p : ℝ)*z.im) +
        ∑ b ∈ Finset.range p, chartPullback f ((z.re+(b : ℝ))/(p : ℝ), z.im/(p : ℝ)) := by
    rw [Fintype.sum_option, hnone]
    simp_rw [hsome]
    rw [sum_zmod_val_reindex]
  exact congrArg (fun q : ℂ => (Real.sqrt (p : ℝ) : ℂ)⁻¹*q) hsum

/-- The actual quotient Hecke chart, with its original physical heights. -/
theorem quotientHecke_chart (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (x y : ℝ) (hy : 0 < y) :
    maassChart N (quotientHecke N p hp hpN U) (x,y) =
      primeHeckeExpression p (maassChart N U) (x,y) := by
  let z : ℍ := ⟨⟨x,y⟩,hy⟩
  change chartPullback (testLift N (quotientHecke N p hp hpN U)) (chartMap z) = _
  rw [chartPullback_at_upper, quotientHecke_lift]
  exact nativeHecke_eq_physical p hp.pos (testLift N U) z

theorem actual_quotient_hecke_fourier_eq_physical (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (n : ℤ) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N (quotientHecke N p hp hpN U) n y =
      coefficient (primeHeckeExpression p (maassChart N U)) n y := by
  rw [actualTestFourier_eq_coefficient]
  simp only [coefficient, periodIntegral_eq_interval, phased]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [quotientHecke_chart N p hp hpN U x y hy]

/-- True quotient Hecke Fourier transfer at EVERY integer index,
including zero. Gamma automorphy has been proved, not assumed. -/
theorem actual_quotient_hecke_fourier_all (N p : ℕ) (hp : p.Prime) (hpN : ¬ p ∣ N)
    (U : Gamma0OrbitSpace N → ℂ) (hC : ContinuousOn (maassChart N U) upperDomain)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N (quotientHecke N p hp hpN U) n y =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        ((if (p : ℤ) ∣ n then actualTestFourier N U (n/(p : ℤ)) ((p : ℝ)*y) else 0) +
          (p : ℂ)*actualTestFourier N U ((p : ℤ)*n) (y/(p : ℝ))) := by
  rw [actual_quotient_hecke_fourier_eq_physical N p hp hpN U n hy,
    coefficient_primeHeckeExpression_all p hp.pos hC (maassChart_periodic N U) n hy]
  simp_rw [← actualTestFourier_eq_coefficient N U]

/-- The actual descended quotient Hecke function has the actual K
coefficient paid by the ORIGINAL quotient Maass PDE and original L2 norm. -/
theorem actual_quotient_hecke_realK_all (N p : ℕ) [NeZero N]
    (hp : p.Prime) (hpN : ¬ p ∣ N) (U : Gamma0OrbitSpace N → ℂ)
    (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N))
    (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
    (nu : ℝ) (hnu : 0 ≤ nu)
    (hPDE : ∀ z ∈ upperDomain,
      -(z.2 : ℂ)^2*(partialX (partialX (maassChart N U)) z+
        partialY (partialY (maassChart N U)) z)=(1/4-(nu : ℂ)^2)*maassChart N U z)
    {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    actualTestFourier N (quotientHecke N p hp hpN U) n y =
      (quotientRho N U nu ((p : ℤ)*n) +
        if (p : ℤ) ∣ n then quotientRho N U nu (n/(p : ℤ)) else 0) *
          (Real.sqrt y : ℂ)*complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) := by
  rw [actual_quotient_hecke_fourier_eq_physical N p hp hpN U n hy]
  exact actual_hecke_realK_all N U hU hU2 hC2 nu hnu hPDE p hp.pos hn hy

end
end ImbalancedChen.Part3.ActualPrimeHeckePhysicalFourier20261026b
