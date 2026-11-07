import ImbalancedChen.Part3ActualHeckeAllFourier
import ImbalancedChen.Part3ActualHeckeRealKTransfer

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Actual all-index K-amplitude transfer for the physical normalized
prime-Hecke expression of a genuine quotient smooth L2 real-order Maass
function. At every n!=0 the amplitude is rho(p*n)+1_{p|n}rho(n/p).
An actual pointwise eigenfunction identity implies the corresponding
Fourier recurrence; existence of Hecke eigenfunctions is not asserted.
No automorphic spectral expansion, coefficient ansatz, or Gamma-automorphy
theorem is assumed or constructed here.
-/

namespace ImbalancedChen.Part3.ActualHeckeAllRealK20261026b
noncomputable section
open Set MeasureTheory
open ActualHeckeAllFourier20261026b ActualHeckeRealKTransfer20261026b
open ActualHeckeDivisibleFourier20261026b ActualHeckeTranslationProjector20261026b
open QuotientRealKFourierCoefficient20261026b ActualPoincareSpectralCoefficient20261026a
open ActualMaassFourierODE20261026a ActualFourierBesselConjugation20261026a
open Gamma0QuotientCellPushforward20261025a ComplexOrderKBridgeSourceOnly

variable (N : ℕ) [NeZero N] (U : Gamma0OrbitSpace N → ℂ)
  (hU : Continuous (testLift N U)) (hU2 : MemLp U 2 (carrierPushforward N))
  (hC2 : ContDiffOn ℝ 2 (maassChart N U) upperDomain)
  (nu : ℝ) (hnu : 0 ≤ nu)
  (hPDE : ∀ z ∈ upperDomain,
    -(z.2 : ℂ)^2 * (partialX (partialX (maassChart N U)) z +
      partialY (partialY (maassChart N U)) z) = (1/4-(nu : ℂ)^2)*maassChart N U z)

/-- Both branches at every nonzero integer index, with the actual
original quotient hypotheses supplying the two original K modes. -/
theorem actual_hecke_realK_all (p : ℕ) (hp : 0 < p)
    {n : ℤ} (hn : n ≠ 0) {y : ℝ} (hy : 0 < y) :
    coefficient (primeHeckeExpression p (maassChart N U)) n y =
      (quotientRho N U nu ((p : ℤ)*n) +
        if (p : ℤ) ∣ n then quotientRho N U nu (n/(p : ℤ)) else 0) *
          (Real.sqrt y : ℂ) * complexOrderK (nu : ℂ) (2*Real.pi*|(n : ℝ)|*y) := by
  have hpZ : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  by_cases hd : (p : ℤ) ∣ n
  · obtain ⟨m, hm⟩ := hd
    have hm0 : m ≠ 0 := by
      intro hzero
      exact hn (by simpa only [hzero, mul_zero] using hm)
    rw [hm, if_pos (dvd_mul_right (p : ℤ) m), Int.mul_ediv_cancel_left m hpZ]
    simpa only [add_comm] using
      actual_hecke_realK_divisible N U hU hU2 hC2 nu hnu hPDE p hp hm0 hy
  · have hpn : (p : ℤ)*n ≠ 0 := mul_ne_zero hpZ hn
    have harg : 2*Real.pi*|(((p : ℤ)*n : ℤ) : ℝ)|*(y/(p : ℝ)) =
        2*Real.pi*|(n : ℝ)|*y := by
      simp only [Int.cast_mul, Int.cast_natCast, abs_mul, abs_of_pos hpR]
      field_simp [hpR.ne'] <;> ring
    have hroot : (Real.sqrt (y/(p : ℝ)) : ℂ) =
        (Real.sqrt y : ℂ) / (Real.sqrt (p : ℝ) : ℂ) := by
      rw [Real.sqrt_div hy.le, Complex.ofReal_div]
    have hs : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpR).ne'
    have hsq : (Real.sqrt (p : ℝ) : ℂ)^2 = (p : ℂ) := by
      exact_mod_cast Real.sq_sqrt hpR.le
    rw [coefficient_primeHeckeExpression_all p hp hC2.continuousOn
      (maassChart_periodic N U) n hy]
    simp only [if_neg hd, zero_add, add_zero]
    rw [← actualTestFourier_eq_coefficient N U ((p : ℤ)*n) (y/(p : ℝ)),
      actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hpn (div_pos hy hpR),
      harg, hroot, ← hsq]
    field_simp [hs] <;> ring

/-- Integrating an actual pointwise physical Hecke eigenfunction identity
gives its literal Fourier coefficient identity, not an assumed one. -/
theorem coefficient_of_actual_hecke_eigenfunction (p : ℕ) (eigen : ℂ)
    (hEigen : ∀ z ∈ upperDomain,
      primeHeckeExpression p (maassChart N U) z = eigen * maassChart N U z)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (primeHeckeExpression p (maassChart N U)) n y =
      eigen * actualTestFourier N U n y := by
  rw [actualTestFourier_eq_coefficient]
  simp only [coefficient, periodIntegral_eq_interval, phased]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [hEigen (x,y) hy]
  ring

/-- Conditional Hecke Fourier recurrence derived from the original
pointwise eigenfunction identity and actual quotient Maass classification.
No existence or completeness of such eigenfunctions is claimed. -/
theorem actual_hecke_rho_recurrence (p : ℕ) (hp : 0 < p) (eigen : ℂ)
    (hEigen : ∀ z ∈ upperDomain,
      primeHeckeExpression p (maassChart N U) z = eigen * maassChart N U z)
    {n : ℤ} (hn : n ≠ 0) :
    quotientRho N U nu ((p : ℤ)*n) +
      (if (p : ℤ) ∣ n then quotientRho N U nu (n/(p : ℤ)) else 0) =
        eigen * quotientRho N U nu n := by
  let D : ℂ := complexOrderK (nu : ℂ) (modeFrequency n)
  have hD : D ≠ 0 :=
    RealBesselTailKSelection20261026a.actualRealK_ne_zero nu (modeFrequency_pos hn)
  have hT := actual_hecke_realK_all N U hU hU2 hC2 nu hnu hPDE p hp hn (by norm_num : (0 : ℝ) < 1)
  have hF := actual_quotient_fourier_eq_realK N U hU hU2 hC2 nu hnu hPDE hn
    (by norm_num : (0 : ℝ) < 1)
  have hE := coefficient_of_actual_hecke_eigenfunction N U p eigen hEigen n
    (by norm_num : (0 : ℝ) < 1)
  simp only [Real.sqrt_one, Complex.ofReal_one, mul_one] at hT hF
  apply mul_right_cancel₀ hD
  calc
    _ = coefficient (primeHeckeExpression p (maassChart N U)) n 1 := by
      simpa only [D, modeFrequency, mul_one] using hT.symm
    _ = eigen * actualTestFourier N U n 1 := hE
    _ = _ := by
      rw [hF]
      dsimp [D, modeFrequency]
      ring

end
end ImbalancedChen.Part3.ActualHeckeAllRealK20261026b
