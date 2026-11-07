import ImbalancedChen.Part3PrimeCentralFourierDerivInterchange

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

A genuine central parameter jet of the literal finite completed oldform
numerator for an arbitrary prime list, with every repeated prime retained.
The finite jet is constructed from the derivative of the actual scalar
p^(-s), the actual full-level completed central family, and its proved
zero central derivative. It is then proved to be the actual derivative
of the parameter-varying oldform list. Continuous physical horizontal
traces of both the numerator and its jet are conclusions. This supplies
the all-level central Fourier derivative exchange without treating the
finite coefficients as parameter independent.
-/

noncomputable section
open Set Complex
open scoped UpperHalfPlane MatrixGroups
open ImbalancedChen.Part3.FiniteLevelEisensteinOldforms20261025a
open ImbalancedChen.Part3.CompletedActualEisensteinIdentity20261025a
open ImbalancedChen.Part3.CompletedEisensteinIntegerMean20261026a
open ImbalancedChen.Part3.CentralHeightLogEuler20261026b
open ImbalancedChen.Part3.PrimeScatteringLocal20261026b
open ImbalancedChen.Part3.PrimeCentralChannelDerivative20261026b
open ImbalancedChen.Part3.PrimitiveEisensteinFourierParameterAnalytic

namespace ImbalancedChen.Part3.AllLevelCompletedCentralJet20261026b

def completedListValue (T : List (ℕ+ × ℂ)) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  (T.map (fun t => t.2 * completedActualEisenstein s (pnatDilate t.1 z))).sum

/-- The literal finite numerator; coefficients retain their s-dependence. -/
def finiteCompletedNumerator (L : List PrimeIndex) (s : ℂ) (z : UpperHalfPlane) : ℂ :=
  completedListValue (oldformTerms L s) s z

private theorem completedListValue_raise (p : PrimeIndex) (T : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    completedListValue (T.map (fun t => (primePNat p * t.1, t.2))) s z =
      completedListValue T s (pnatDilate (primePNat p) z) := by
  induction T with
  | nil => simp [completedListValue]
  | cons t T ih =>
      simp only [completedListValue, List.map_cons, List.sum_cons, pnatDilate_mul] at ih ⊢
      rw [ih]

private theorem completedListValue_scale (a : ℂ) (T : List (ℕ+ × ℂ))
    (s : ℂ) (z : UpperHalfPlane) :
    completedListValue (T.map (fun t => (t.1, a * t.2))) s z = a * completedListValue T s z := by
  induction T with
  | nil => simp [completedListValue]
  | cons t T ih =>
      simp only [completedListValue, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      ring

theorem finiteCompletedNumerator_cons (p : PrimeIndex) (L : List PrimeIndex)
    (s : ℂ) (z : UpperHalfPlane) :
    finiteCompletedNumerator (p :: L) s z =
      if p.1 ∣ primeProduct L then finiteCompletedNumerator L s (pnatDilate (primePNat p) z)
      else finiteCompletedNumerator L s (pnatDilate (primePNat p) z) -
        primeRatio p.1 s * finiteCompletedNumerator L s z := by
  unfold finiteCompletedNumerator oldformTerms
  split_ifs
  · exact completedListValue_raise p _ s z
  · rw [show completedListValue
        ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2)) ++
          (oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) s z =
        completedListValue ((oldformTerms L s).map (fun t => (primePNat p * t.1, t.2))) s z +
          completedListValue ((oldformTerms L s).map (fun t => (t.1, -(p.1 : ℂ) ^ (-s) * t.2))) s z by
        simp only [completedListValue, List.map_append, List.sum_append]]
    rw [completedListValue_raise, completedListValue_scale]
    simp only [primeRatio]
    ring

/-- Explicit genuine numerator derivative. The log term differentiates the
coefficient -p^(-s); it cannot be deleted when extending beyond prime level. -/
def finiteCentralJet : List PrimeIndex → UpperHalfPlane → ℂ
  | [], _ => 0
  | p :: L, z =>
      if p.1 ∣ primeProduct L then finiteCentralJet L (pnatDilate (primePNat p) z)
      else finiteCentralJet L (pnatDilate (primePNat p) z) +
        primeLog p * primeRatio p.1 (1 / 2) * finiteCompletedNumerator L (1 / 2) z -
          primeRatio p.1 (1 / 2) * finiteCentralJet L z

/-- The central jet is proved from the actual parameter-varying finite
oldform expression, rather than used as a derivative supplier. -/
theorem finiteCompletedNumerator_hasDerivAt_center (L : List PrimeIndex) (z : UpperHalfPlane) :
    HasDerivAt (fun s : ℂ => finiteCompletedNumerator L s z) (finiteCentralJet L z) (1 / 2 : ℂ) := by
  induction L generalizing z with
  | nil =>
      simpa [finiteCompletedNumerator, completedListValue, oldformTerms, finiteCentralJet,
        pnatDilate_one] using completedActual_hasDerivAt_center_zero z
  | cons p L ih =>
      by_cases hd : p.1 ∣ primeProduct L
      · simpa only [finiteCompletedNumerator_cons, finiteCentralJet, if_pos hd] using
          ih (pnatDilate (primePNat p) z)
      · have hq := primeRatio_hasDerivAt p.2 (1 / 2 : ℂ)
        have h := (ih (pnatDilate (primePNat p) z)).sub (hq.mul (ih z))
        convert h using 1 <;>
          simp only [finiteCompletedNumerator_cons, finiteCentralJet, if_neg hd, primeLog] <;> ring

theorem completedListValue_dilation_continuous (T : List (ℕ+ × ℂ)) (s : ℂ)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => completedListValue T s (pnatDilate n (horizontalPoint y hy x))) := by
  induction T with
  | nil => simpa [completedListValue] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  | cons t T ih =>
      have hhead : Continuous (fun x : ℝ => t.2 * completedActualEisenstein s
          (pnatDilate t.1 (pnatDilate n (horizontalPoint y hy x)))) := by
        simpa only [pnatDilate_mul] using
          (continuous_const.mul (completed_integer_dilation_continuous s (n * t.1) y hy))
      simpa only [completedListValue, List.map_cons, List.sum_cons] using hhead.add ih

theorem finiteCompletedNumerator_dilation_continuous (L : List PrimeIndex) (s : ℂ)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => finiteCompletedNumerator L s (pnatDilate n (horizontalPoint y hy x))) :=
  completedListValue_dilation_continuous (oldformTerms L s) s n y hy

/-- Actual central derivative traces are continuous after every positive
integral dilation. This supplies the required Fourier integrability. -/
theorem finiteCentralJet_dilation_continuous (L : List PrimeIndex)
    (n : ℕ+) (y : ℝ) (hy : 0 < y) :
    Continuous (fun x : ℝ => finiteCentralJet L (pnatDilate n (horizontalPoint y hy x))) := by
  induction L generalizing n with
  | nil => simpa only [finiteCentralJet] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  | cons p L ih =>
      by_cases hd : p.1 ∣ primeProduct L
      · simpa only [finiteCentralJet, if_pos hd, pnatDilate_mul] using ih (n * primePNat p)
      · have hRaise := ih (n * primePNat p)
        have hValue := finiteCompletedNumerator_dilation_continuous L (1 / 2) n y hy
        have hBase := ih n
        simpa only [finiteCentralJet, if_neg hd, pnatDilate_mul] using
          (hRaise.add (continuous_const.mul hValue)).sub (continuous_const.mul hBase)

end ImbalancedChen.Part3.AllLevelCompletedCentralJet20261026b
