import ImbalancedChen.Part3CompletedCentralFourierDerivInterchange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Genuine central differentiation under both ORIGINAL physical prime-cusp
Fourier integrals. The finite oldform expressions are integrated using the
actual continuous traces, then differentiated using the proved full-level
dominated interchange. The resulting signed cross derivative is identified
with the integral of the actual pointwise derivative. Multiplication by the
true inverse completion transfers the interchange to both ordinary channels,
retaining the central zero and exact derivative factor two. No final
interchange or normalization is passed as a hypothesis.
-/

noncomputable section
open Set Complex Filter Metric MeasureTheory Topology
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
open ImbalancedChen.Part3.LevelOldformScattering20261026a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinReflection20261025a
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
open ImbalancedChen.Part3.AllLevelContinuedMaass20261026a
open ImbalancedChen.Part3.AllLevelCentralNormalization20261026a
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.PrimeCompletedChannelReflection20261026b
open ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b
open ImbalancedChen.Part3.PrimeCentralFourierFunctional20261026b
open ImbalancedChen.Part3.CompletedCentralParameterDomination20261026b
open ImbalancedChen.Part3.CompletedCentralFourierDerivInterchange20261026b
open ImbalancedChen.Part3.FrickeNormalizer
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.PrimeCentralFourierDerivInterchange20261026b

private theorem dilated_horizontal_fourier {p : ℕ} (hp : p.Prime) (s : ℂ)
    (y : ℝ) (hy : 0 < y) (x : ℝ) :
    completedActualEisenstein s (pnatDilate ⟨p, hp.pos⟩ (horizontalPoint y hy x)) =
      completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x) := by
  simp [completedActualEisenstein, pnatDilate, dilate, horizontalPoint,
    Complex.mul_re, Complex.mul_im]

private theorem prime_fourier_pair_explicit {p : ℕ} (hp : p.Prime) (s : ℂ)
    (hs : 0 < s.re) (hs1 : s ≠ 1) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    ((∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform p s (horizontalPoint y hy x)) =
      primeRatio p s * ((∫ x in (0 : ℝ)..1, fourierPhase n x *
        completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x)) -
          primeRatio p s * (∫ x in (0 : ℝ)..1, fourierPhase n x * completedEisensteinFourier s y x)) /
            (1 - primeRatio p s ^ 2)) ∧
    ((∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedLevelOldform p s (frickeSL p hp.pos • horizontalPoint y hy x)) =
      primeRatio p s * ((∫ x in (0 : ℝ)..1, fourierPhase n x * completedEisensteinFourier s y x) -
        primeRatio p s * (∫ x in (0 : ℝ)..1, fourierPhase n x *
          completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x))) / (1 - primeRatio p s ^ 2)) := by
  have hpy : 0 < (p : ℝ) * y := mul_pos (by exact_mod_cast hp.pos) hy
  have h0 : IntervalIntegrable (fun x : ℝ => fourierPhase n x * completedEisensteinFourier s y x) volume 0 1 := by
    simpa using ((fourierPhase_continuous n).mul
      (completedFourier_scaled_continuous s hy (1 : ℤ))).intervalIntegrable 0 1
  have hpint : IntervalIntegrable (fun x : ℝ => fourierPhase n x *
      completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x)) volume 0 1 := by
    simpa using ((fourierPhase_continuous n).mul
      (completedFourier_scaled_continuous s hpy (p : ℤ))).intervalIntegrable 0 1
  constructor
  · calc
      _ = ∫ x in (0 : ℝ)..1, (primeRatio p s / (1 - primeRatio p s ^ 2)) *
          (fourierPhase n x * completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x) -
            primeRatio p s * (fourierPhase n x * completedEisensteinFourier s y x)) := by
        congr 1
        funext x
        rw [completed_prime_q_explicit hp s hs, dilated_horizontal_fourier hp]
        simp only [completedActualEisenstein, horizontalPoint]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub hpint (h0.const_mul _), intervalIntegral.integral_const_mul]
        ring
  · calc
      _ = ∫ x in (0 : ℝ)..1, (primeRatio p s / (1 - primeRatio p s ^ 2)) *
          (fourierPhase n x * completedEisensteinFourier s y x - primeRatio p s *
            (fourierPhase n x * completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x))) := by
        congr 1
        funext x
        rw [completed_prime_fricke_q_explicit hp s hs hs1, dilated_horizontal_fourier hp]
        simp only [completedActualEisenstein, horizontalPoint]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub h0 (hpint.const_mul _), intervalIntegral.integral_const_mul]
        ring

private theorem prime_quotient_hasDerivAt {p : ℕ} (hp : p.Prime) {X Y : ℂ → ℂ}
    (hX : HasDerivAt X 0 (1 / 2 : ℂ)) (hY : HasDerivAt Y 0 (1 / 2 : ℂ)) :
    HasDerivAt (fun s : ℂ => primeRatio p s * (Y s - primeRatio p s * X s) / (1 - primeRatio p s ^ 2))
      (-(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        (primeRatio p (1 / 2) * (Y (1 / 2) - primeRatio p (1 / 2) * X (1 / 2)) /
          (1 - primeRatio p (1 / 2) ^ 2)) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        (primeRatio p (1 / 2) * (X (1 / 2) - primeRatio p (1 / 2) * Y (1 / 2)) /
          (1 - primeRatio p (1 / 2) ^ 2))) (1 / 2 : ℂ) := by
  have hq := primeRatio_hasDerivAt hp (1 / 2 : ℂ)
  have hd := prime_local_denominator_ne_zero hp (by norm_num : 0 < (1 / 2 : ℂ).re)
  have h := (hq.mul (hY.sub (hq.mul hX))).div ((hq.pow 2).const_sub 1) hd
  convert h using 1 <;> field_simp [hd] <;> ring

/-- Both completed physical Fourier channels admit a genuine central
derivative. The derivative values retain both actual Fourier functionals. -/
theorem completed_prime_fourier_hasDerivAt_cross_pair {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedLevelOldform p s (horizontalPoint y hy x))
      (-(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform p (1 / 2) (horizontalPoint y hy x)) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x *
          completedLevelOldform p (1 / 2) (frickeSL p hp.pos • horizontalPoint y hy x))) (1 / 2 : ℂ)) ∧
    (HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedLevelOldform p s (frickeSL p hp.pos • horizontalPoint y hy x))
      (-(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x *
          completedLevelOldform p (1 / 2) (frickeSL p hp.pos • horizontalPoint y hy x)) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform p (1 / 2) (horizontalPoint y hy x))) (1 / 2 : ℂ)) := by
  let X : ℂ → ℂ := fun s => ∫ x in (0 : ℝ)..1, fourierPhase n x * completedEisensteinFourier s y x
  let Y : ℂ → ℂ := fun s => ∫ x in (0 : ℝ)..1, fourierPhase n x *
    completedEisensteinFourier s ((p : ℝ) * y) ((p : ℝ) * x)
  have hpy : 0 < (p : ℝ) * y := mul_pos (by exact_mod_cast hp.pos) hy
  have hX : HasDerivAt X 0 (1 / 2 : ℂ) := by
    simpa [X] using completedFourier_integral_hasDerivAt_center_zero n (1 : ℤ) y hy
  have hY : HasDerivAt Y 0 (1 / 2 : ℂ) := by
    simpa [Y] using completedFourier_integral_hasDerivAt_center_zero n (p : ℤ) ((p : ℝ) * y) hpy
  have hcenter := prime_fourier_pair_explicit hp (1 / 2 : ℂ) (by norm_num) (by norm_num) n y hy
  have he : ∀ᶠ s : ℂ in 𝓝 (1 / 2 : ℂ),
      0 < s.re ∧ s ≠ 1 := by
    filter_upwards [ball_mem_nhds (1 / 2 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)] with s hs
    have hquarter : s ∈ closedBall (1 / 2 : ℂ) (1 / 4 : ℝ) :=
      mem_closedBall.mpr (le_trans (mem_ball.mp hs).le (by norm_num))
    exact ⟨lt_of_lt_of_le (by norm_num) (quarter_disk_re_bounds hquarter).1,
      (quarter_disk_avoids_poles hquarter).2⟩
  have hi := prime_quotient_hasDerivAt hp hX hY
  have hj := prime_quotient_hasDerivAt hp hY hX
  dsimp only [X, Y] at hi hj
  rw [← hcenter.1, ← hcenter.2] at hi hj
  constructor
  · apply hi.congr_of_eventuallyEq
    filter_upwards [he] with s hs
    exact (prime_fourier_pair_explicit hp s hs.1 hs.2 n y hy).1
  · apply hj.congr_of_eventuallyEq
    filter_upwards [he] with s hs
    exact (prime_fourier_pair_explicit hp s hs.1 hs.2 n y hy).2

/-- Actual derivative/integral exchange for the prime infinity channel. -/
theorem completed_prime_fourier_hasDerivAt_integral {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedLevelOldform p s (horizontalPoint y hy x))
      (∫ x in (0 : ℝ)..1, fourierPhase n x *
        deriv (fun s : ℂ => completedLevelOldform p s (horizontalPoint y hy x)) (1 / 2)) (1 / 2 : ℂ) := by
  rw [completed_prime_central_derivative_fourier_cross hp n y hy]
  exact (completed_prime_fourier_hasDerivAt_cross_pair hp n y hy).1

/-- The actual Fricke central derivative has the second signed Fourier
cross row, with integrability inherited from both actual cusp traces. -/
theorem completed_prime_fricke_derivative_fourier_cross {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ =>
      completedLevelOldform p s (frickeSL p hp.pos • horizontalPoint y hy x)) (1 / 2)) =
      -(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x *
          completedLevelOldform p (1 / 2) (frickeSL p hp.pos • horizontalPoint y hy x)) +
      ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
        (∫ x in (0 : ℝ)..1, fourierPhase n x * completedLevelOldform p (1 / 2) (horizontalPoint y hy x)) := by
  have hi := completed_infinity_fourier_integrable p (1 / 2) n y hy
  have hj := completed_fricke_fourier_integrable p hp.pos (1 / 2)
    (criticalStrip_subset_completedRegularDomain p (by norm_num)) n y hy
  calc
    _ = ∫ x in (0 : ℝ)..1,
        (-(Real.log (p : ℝ) : ℂ) / (1 - primeRatio p (1 / 2) ^ 2)) *
          (fourierPhase n x * completedLevelOldform p (1 / 2)
            (frickeSL p hp.pos • horizontalPoint y hy x)) +
        ((Real.log (p : ℝ) : ℂ) * primeRatio p (1 / 2) / (1 - primeRatio p (1 / 2) ^ 2)) *
          (fourierPhase n x * completedLevelOldform p (1 / 2) (horizontalPoint y hy x)) := by
      congr 1
      funext x
      rw [completed_prime_fricke_deriv_center_cross hp]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (hj.const_mul _) (hi.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

theorem completed_prime_fricke_fourier_hasDerivAt_integral {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      completedLevelOldform p s (frickeSL p hp.pos • horizontalPoint y hy x))
      (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ =>
        completedLevelOldform p s (frickeSL p hp.pos • horizontalPoint y hy x)) (1 / 2)) (1 / 2 : ℂ) := by
  rw [completed_prime_fricke_derivative_fourier_cross hp n y hy]
  exact (completed_prime_fourier_hasDerivAt_cross_pair hp n y hy).2

/-- The genuine ordinary derivative is passed through the original Fourier
integral using the true completion reciprocal with its simple central zero. -/
theorem ordinary_prime_fourier_hasDerivAt_integral {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      centralOrdinaryLevel p s (horizontalPoint y hy x))
      (∫ x in (0 : ℝ)..1, fourierPhase n x *
        deriv (fun s : ℂ => centralOrdinaryLevel p s (horizontalPoint y hy x)) (1 / 2)) (1 / 2 : ℂ) := by
  rw [ordinary_central_derivative_infinity_fourier p n y hy]
  have h := inverseCompletion_hasDerivAt_center.mul
    (completed_prime_fourier_hasDerivAt_cross_pair hp n y hy).1
  simp only [inverseCompletion_center, zero_mul, add_zero] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => ordinary_infinity_fourier_normalization p s n y hy)

theorem ordinary_prime_fricke_fourier_hasDerivAt_integral {p : ℕ} (hp : p.Prime)
    (n : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      centralOrdinaryLevel p s (frickeSL p hp.pos • horizontalPoint y hy x))
      (∫ x in (0 : ℝ)..1, fourierPhase n x * deriv (fun s : ℂ =>
        centralOrdinaryLevel p s (frickeSL p hp.pos • horizontalPoint y hy x)) (1 / 2)) (1 / 2 : ℂ) := by
  rw [ordinary_central_derivative_fricke_fourier p hp.pos n y hy]
  have h := inverseCompletion_hasDerivAt_center.mul
    (completed_prime_fourier_hasDerivAt_cross_pair hp n y hy).2
  simp only [inverseCompletion_center, zero_mul, add_zero] at h
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s => ordinary_fricke_fourier_normalization p hp.pos s n y hy)

end ImbalancedChen.Part3.PrimeCentralFourierDerivInterchange20261026b
