import ImbalancedChen.Part3ActualHeckeNondivisibleFourier

/-!
SOURCE_ONLY / UNCOMPILED / ZERO_FORMAL_CREDIT, 2026-10-26.
Every integer Fourier coefficient of the literal p^-1/2 prime-Hecke
expression, with the upper branch present precisely when p divides n.
The original physical heights p*y and y/p, lower branch index p*n, and
upper branch index n/p are retained. This is a theorem of the actual
finite physical expression, independent of Gamma automorphy or spectra.
-/

namespace ImbalancedChen.Part3.ActualHeckeAllFourier20261026b
noncomputable section
open Set MeasureTheory
open ActualMaassFourierODE20261026a ActualHeckeTranslationProjector20261026b
open ActualHeckeDivisibleFourier20261026b ActualHeckeNondivisibleFourier20261026b

theorem coefficient_heckeUp_all (p : ℕ) (hp : 0 < p) {u : ℝ × ℝ → ℂ}
    (hu : ContinuousOn u upperDomain)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (heckeUp p u) n y =
      if (p : ℤ) ∣ n then coefficient u (n/(p : ℤ)) ((p : ℝ)*y) else 0 := by
  by_cases hd : (p : ℤ) ∣ n
  · rw [if_pos hd]
    have hn : (p : ℤ)*(n/(p : ℤ)) = n := Int.mul_ediv_cancel' hd
    simpa only [hn] using coefficient_heckeUp_divisible p hp hu hper (n/(p : ℤ)) hy
  · rw [if_neg hd]
    exact coefficient_heckeUp_nondivisible p hp hper n hd hy

/-- Linearity of the literal physical coefficient; true slice
integrability is obtained from the original spatial continuity. -/
theorem coefficient_primeHeckeExpression_linear (p : ℕ) (hp : 0 < p)
    {u : ℝ × ℝ → ℂ} (hu : ContinuousOn u upperDomain)
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (primeHeckeExpression p u) n y =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        (coefficient (heckeUp p u) n y + coefficient (heckeDown p u) n y) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hup : Continuous (fun x => heckeUp p u (x,y)) :=
    (continuous_slice hu (mul_pos hpR hy)).comp (by fun_prop)
  have hdown := heckeDown_slice_continuous p hp hu hy
  simp only [coefficient, periodIntegral_eq_interval, phased, primeHeckeExpression]
  calc
    _ = ∫ x in (0 : ℝ)..1, (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        (phase n x * heckeUp p u (x,y) + phase n x * heckeDown p u (x,y)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (((phase_continuous _).mul hup).intervalIntegrable 0 1)
        (((phase_continuous _).mul hdown).intervalIntegrable 0 1)]

/-- All-index native Fourier transfer, including the zero coefficient.
No divisibility-supported coefficient identity is assumed. -/
theorem coefficient_primeHeckeExpression_all (p : ℕ) (hp : 0 < p)
    {u : ℝ × ℝ → ℂ} (hu : ContinuousOn u upperDomain)
    (hper : ∀ x y : ℝ, 0 < y → u (x+1,y) = u (x,y))
    (n : ℤ) {y : ℝ} (hy : 0 < y) :
    coefficient (primeHeckeExpression p u) n y =
      (Real.sqrt (p : ℝ) : ℂ)⁻¹ *
        ((if (p : ℤ) ∣ n then coefficient u (n/(p : ℤ)) ((p : ℝ)*y) else 0) +
          (p : ℂ) * coefficient u ((p : ℤ)*n) (y/(p : ℝ))) := by
  rw [coefficient_primeHeckeExpression_linear p hp hu n hy,
    coefficient_heckeUp_all p hp hu hper n hy,
    coefficient_heckeDown p hp hu n hy, Complex.real_smul]

end
end ImbalancedChen.Part3.ActualHeckeAllFourier20261026b
