import ImbalancedChen.Part3ActualCompletedZeroDifferencePayment
import ImbalancedChen.Part3ActualOccupiedCountingScale
import ImbalancedChen.Part3OriginalSourcePoissonFamilyDictionary
import ImbalancedChen.Part3OriginalActualPolarizedProductCaller
import Mathlib.Tactic

/-! Source only / uncompiled / zero formal credit.
The true y=0 piece of the existing completed reciprocal square is evaluated
at the original occupied scales. The production divisor injection and full
completed-kernel bound are reused, not assumed. This is not a source identity
between the S3 Abel packets and the reciprocal square: that dictionary still
requires the original positive Cauchy and arithmetic-majorant proof.
-/

namespace ImbalancedChen.Part3.OriginalZeroDifferenceSourcePayment20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open CommonSmoothCutoff ActualCompletedZeroPaymentSourceOnly
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open ActualOriginalSpectralScales20261028 ActualSpectralDoubleCauchyNormalization20261028
open ActualOccupiedCountingScale20261102 ActualMediumVarianceAtomBindingSourceOnly
open MediumGlobalDyadicOwnership20261028 OriginalLambdaTrimPoissonFamily20261028
open OriginalSourcePoissonFamilyDictionary20261028
open OriginalActualThreePairPolarization20261102 OriginalActualPolarizedProductCaller20261102

/-- The existing zeroPiece, with the SAME real-H floor as the literal
S3 Poisson source dictionary and the original B,C,F scales. -/
def keyZeroPiece (A : ℕ) (atom : MediumAtom) (k : Key)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) : ℂ :=
  zeroPiece A atom.residue (factorCarrier (roughS k)) (sourceKeyH atom k)
    lambda omega (spectralB atom k) (spectralC atom k)
    (spectralC atom k) (countingF atom)

def keyZeroTau (atom : MediumAtom) (k : Key) : ℕ :=
  tauEnvelope (factorCarrier (roughS k))
    (poissonNonzeroFrequencyWindow (sourceKeyH atom k))

/-- This is the original normalized SQUARED zero charge. It is not the
norm of a nonzero-y coefficient, nor the Fourier m=0 contribution. -/
def normalizedZero (A : ℕ) (atom : MediumAtom) (k : Key)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) : ℝ :=
  (bareCauchyPrefactor atom k)^2 * ‖keyZeroPiece A atom k lambda omega‖ /
    (originalBareScale atom)^2

theorem normalizedZero_nonneg (A : ℕ) (atom : MediumAtom) (k : Key)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    0 ≤ normalizedZero A atom k lambda omega := by
  unfold normalizedZero
  positivity

/-- The independent production completedPiece is split, with its entire
nonzero-y source left unchanged, before either source is estimated. -/
theorem original_completedPiece_split (A : ℕ) (atom : MediumAtom) (k : Key)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    completedPiece A atom.residue (factorCarrier (roughS k)) (sourceKeyH atom k)
      lambda omega (spectralB atom k) (spectralC atom k) (spectralB atom k)
      (spectralC atom k) (countingF atom) =
    keyZeroPiece A atom k lambda omega +
      ∑ s ∈ nonzeroSource (carrier A atom.residue (factorCarrier (roughS k))
        (sourceKeyH atom k) (Icc (Int.ceil (-countingF atom)) (Int.floor (countingF atom)))),
        weight lambda omega s * completedKernel (spectralB atom k)
          (spectralC atom k) (spectralC atom k) atom.residue (output s) := by
  exact completedPiece_eq_zeroPiece_add_nonzero _ _ _ _ _ _ _ _ _ _ _

/-- Actual coincidence count and full b,c-Poisson kernel, using the
production nonzero |h|s' divisor injection. The one-bounded inputs are the
original scalar coefficient class; no zero-piece estimate is a premise. -/
theorem keyZeroPiece_norm_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key)
    (hk : k ∈ originalNumericKeys atom z) (A : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ s ∈ factorCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) :
    ‖keyZeroPiece A atom k lambda omega‖ ≤
      72 * (keyZeroTau atom k : ℝ) * zeroDifferenceCost atom k (poissonLoss atom k) := by
  obtain ⟨hU,hV,hQ,hx⟩ := scale_facts hA
  have hR : 0 < roughR k := zero_lt_one.trans_le (rough_scales_one_le k).1
  have hS : 0 < roughS k := zero_lt_one.trans_le (rough_scales_one_le k).2
  have hH : (sourceKeyH atom k : ℝ) ≤ countingH atom k (poissonLoss atom k) :=
    (Nat.floor_le (poisson_nonneg hA k).1).trans (actual_H_le_countingH hA z k hk)
  have hb := zeroPiece_norm_le A atom.residue (factorCarrier (roughS k))
    (sourceKeyH atom k) lambda omega
    (M := spectralB atom k) (N := spectralC atom k) (S := roughS k)
    (F := countingF atom) (spectralC atom k)
    (by dsimp [spectralB]; positivity) (by dsimp [spectralC]; positivity)
    hS.le (by dsimp [countingF]; positivity)
    (fun t ht => zero_factor_pos_small hS ht) (zero_factor_card_small hS)
    hlambda homega
  calc
    ‖keyZeroPiece A atom k lambda omega‖ ≤ _ := hb
    _ ≤ 72 * spectralB atom k * spectralC atom k * countingF atom *
        countingH atom k (poissonLoss atom k) * roughS k * (keyZeroTau atom k : ℝ) := by
      have hm := mul_le_mul_of_nonneg_left hH
        (show 0 ≤ 72 * spectralB atom k * spectralC atom k * countingF atom *
          roughS k * (keyZeroTau atom k : ℝ) by dsimp [spectralB,spectralC,countingF]; positivity)
      convert hm using 1 <;> dsimp [keyZeroTau] <;> ring
    _ = _ := by unfold zeroDifferenceCost; ring

/-- The new finite payment now feeds G's exact original D0 identity.
The preliminary d and log^5 are still explicit in poissonLoss. -/
theorem normalizedZero_le_D0 {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key)
    (hk : k ∈ originalNumericKeys atom z) (A : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ s ∈ factorCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) :
    normalizedZero A atom k lambda omega ≤
      72 * (keyZeroTau atom k : ℝ) * poissonLoss atom k * D0 atom k := by
  have hp := keyZeroPiece_norm_le hA z k hk A lambda omega hlambda homega
  calc
    normalizedZero A atom k lambda omega ≤
        (bareCauchyPrefactor atom k)^2 *
          (72 * (keyZeroTau atom k : ℝ) * zeroDifferenceCost atom k (poissonLoss atom k)) /
            (originalBareScale atom)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg _)) (sq_nonneg _)
    _ = 72 * (keyZeroTau atom k : ℝ) *
        ((bareCauchyPrefactor atom k)^2 * zeroDifferenceCost atom k (poissonLoss atom k) /
          (originalBareScale atom)^2) := by ring
    _ = _ := by rw [zeroDifference_normalization hA]; ring

/-- The original frozen gamma2 pair supplies the scalar norm for every
independent st=d choice. No new global bound on gamma2 is assumed. This
does not assert the still-missing Cauchy dictionary for frozenUpperPacket. -/
theorem original_gamma2_coefficient_bound {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (s s' : ℕ) (e : Fin 4) (u : ℕ) :
    ‖diagonal (gamma2Slot atom s) (gamma2Slot atom s') e u‖ ≤ 1 :=
  diagonal_norm_le_one _ _ e ((actual_slots_one_bounded hA).1 s)
    ((actual_slots_one_bounded hA).1 s') u

end
end ImbalancedChen.Part3.OriginalZeroDifferenceSourcePayment20261102
