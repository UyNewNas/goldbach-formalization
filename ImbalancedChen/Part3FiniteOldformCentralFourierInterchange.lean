import ImbalancedChen.Part3AllLevelCompletedCentralJet

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Central differentiation under the original physical Fourier integral of
the actual finite completed oldform numerator, for every prime list and
every positive integral dilation. The proof inducts on the literal oldform
construction, differentiating the new-prime coefficient p^(-s) as well as
the family. The full-level base uses the actual dominated derivative
interchange. Integral linearity is justified by the proved continuous
actual numerator and actual jet traces. No finite-coefficient constancy or
interchange assumption is made.
-/

noncomputable section
open Set Complex Filter MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.PrimeLevelEisensteinDegeneracy20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CentralHeightLogEuler20261026b
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b
open ImbalancedChen.Part3.PrimeCentralFourierFunctional20261026b
open ImbalancedChen.Part3.CompletedCentralFourierDerivInterchange20261026b
open ImbalancedChen.Part3.AllLevelCompletedCentralJet20261026b
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.FiniteOldformCentralFourierInterchange20261026b

theorem finiteNumerator_fourier_integrable (L : List PrimeIndex) (s : ℂ)
    (m : ℕ+) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    IntervalIntegrable (fun x : ℝ => fourierPhase n x *
      finiteCompletedNumerator L s (pnatDilate m (horizontalPoint y hy x))) volume 0 1 :=
  ((fourierPhase_continuous n).mul
    (finiteCompletedNumerator_dilation_continuous L s m y hy)).intervalIntegrable 0 1

theorem finiteJet_fourier_integrable (L : List PrimeIndex)
    (m : ℕ+) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    IntervalIntegrable (fun x : ℝ => fourierPhase n x *
      finiteCentralJet L (pnatDilate m (horizontalPoint y hy x))) volume 0 1 :=
  ((fourierPhase_continuous n).mul
    (finiteCentralJet_dilation_continuous L m y hy)).intervalIntegrable 0 1

/-- Genuine derivative of the original finite-oldform Fourier functional,
with its actual central jet inside the integral. -/
theorem finiteNumerator_fourier_hasDerivAt_center (L : List PrimeIndex)
    (m : ℕ+) (n : ℤ) (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun s : ℂ => ∫ x in (0 : ℝ)..1, fourierPhase n x *
      finiteCompletedNumerator L s (pnatDilate m (horizontalPoint y hy x)))
      (∫ x in (0 : ℝ)..1, fourierPhase n x *
        finiteCentralJet L (pnatDilate m (horizontalPoint y hy x))) (1 / 2 : ℂ) := by
  induction L generalizing m with
  | nil =>
      have hmy : 0 < (m : ℝ) * y := mul_pos (by exact_mod_cast m.pos) hy
      simpa [finiteCompletedNumerator, completedListValue, oldformTerms, finiteCentralJet,
        pnatDilate_one, completedActualEisenstein, pnatDilate, dilate, horizontalPoint,
        Complex.mul_re, Complex.mul_im] using
          completedFourier_integral_hasDerivAt_center_zero n ((m : ℕ) : ℤ) ((m : ℝ) * y) hmy
  | cons p L ih =>
      have hRaise := ih (m * primePNat p)
      have hBase := ih m
      by_cases hd : p.1 ∣ primeProduct L
      · simpa only [finiteCompletedNumerator_cons, finiteCentralJet, if_pos hd, pnatDilate_mul] using hRaise
      · have hq := primeRatio_hasDerivAt p.2 (1 / 2 : ℂ)
        have h := hRaise.sub (hq.mul hBase)
        have hf (s : ℂ) :
            (∫ x in (0 : ℝ)..1, fourierPhase n x *
              finiteCompletedNumerator (p :: L) s (pnatDilate m (horizontalPoint y hy x))) =
            (∫ x in (0 : ℝ)..1, fourierPhase n x *
              finiteCompletedNumerator L s (pnatDilate (m * primePNat p) (horizontalPoint y hy x))) -
            primeRatio p.1 s * (∫ x in (0 : ℝ)..1, fourierPhase n x *
              finiteCompletedNumerator L s (pnatDilate m (horizontalPoint y hy x))) := by
          calc
            _ = ∫ x in (0 : ℝ)..1,
                fourierPhase n x * finiteCompletedNumerator L s
                  (pnatDilate (m * primePNat p) (horizontalPoint y hy x)) -
                primeRatio p.1 s * (fourierPhase n x *
                  finiteCompletedNumerator L s (pnatDilate m (horizontalPoint y hy x))) := by
              congr 1
              funext x
              rw [finiteCompletedNumerator_cons, if_neg hd, pnatDilate_mul]
              ring
            _ = _ := by
              rw [intervalIntegral.integral_sub
                (finiteNumerator_fourier_integrable L s (m * primePNat p) n y hy)
                ((finiteNumerator_fourier_integrable L s m n y hy).const_mul _),
                intervalIntegral.integral_const_mul]
        have hj :
            (∫ x in (0 : ℝ)..1, fourierPhase n x *
              finiteCentralJet (p :: L) (pnatDilate m (horizontalPoint y hy x))) =
            (∫ x in (0 : ℝ)..1, fourierPhase n x *
              finiteCentralJet L (pnatDilate (m * primePNat p) (horizontalPoint y hy x))) +
            (primeLog p * primeRatio p.1 (1 / 2)) *
              (∫ x in (0 : ℝ)..1, fourierPhase n x *
                finiteCompletedNumerator L (1 / 2) (pnatDilate m (horizontalPoint y hy x))) -
            primeRatio p.1 (1 / 2) * (∫ x in (0 : ℝ)..1, fourierPhase n x *
              finiteCentralJet L (pnatDilate m (horizontalPoint y hy x))) := by
          calc
            _ = ∫ x in (0 : ℝ)..1,
                (fourierPhase n x * finiteCentralJet L
                  (pnatDilate (m * primePNat p) (horizontalPoint y hy x)) +
                (primeLog p * primeRatio p.1 (1 / 2)) * (fourierPhase n x *
                  finiteCompletedNumerator L (1 / 2) (pnatDilate m (horizontalPoint y hy x)))) -
                primeRatio p.1 (1 / 2) * (fourierPhase n x *
                  finiteCentralJet L (pnatDilate m (horizontalPoint y hy x))) := by
              congr 1
              funext x
              rw [finiteCentralJet, if_neg hd, pnatDilate_mul]
              ring
            _ = _ := by
              rw [intervalIntegral.integral_sub
                ((finiteJet_fourier_integrable L (m * primePNat p) n y hy).add
                  ((finiteNumerator_fourier_integrable L (1 / 2) m n y hy).const_mul _))
                ((finiteJet_fourier_integrable L m n y hy).const_mul _),
                intervalIntegral.integral_add
                  (finiteJet_fourier_integrable L (m * primePNat p) n y hy)
                  ((finiteNumerator_fourier_integrable L (1 / 2) m n y hy).const_mul _),
                intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rw [hj]
        convert h.congr_of_eventuallyEq (Filter.Eventually.of_forall hf) using 1 <;>
          simp only [primeLog] <;> ring

end ImbalancedChen.Part3.FiniteOldformCentralFourierInterchange20261026b
