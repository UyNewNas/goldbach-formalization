import ImbalancedChen.Part3OriginalZeroDifferenceLogPayment
import Mathlib.Tactic

/-! Source only / uncompiled / zero formal credit.
Consume the new y=0 estimate in the independently defined completedPiece,
and take the original first square root. The original S3/Abel-to-square
Cauchy map and Eq(16) aggregate are NOT supplied by this module.
-/

namespace ImbalancedChen.Part3.OriginalZeroDifferenceCompletedConsumer20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open CommonSmoothCutoff ActualReciprocalSquarePoissonSourceOnly
open ActualCompletedSquarePushforwardSourceOnly
open ActualOriginalSpectralScales20261028 ActualSpectralDoubleCauchyNormalization20261028
open ActualOccupiedCountingScale20261102 ActualMediumVarianceAtomBindingSourceOnly
open MediumGlobalDyadicOwnership20261028 OriginalSourcePoissonFamilyDictionary20261028
open OriginalZeroDifferenceSourcePayment20261102 OriginalZeroDifferenceLogPayment20261102
open OriginalActualThreePairPolarization20261102 OriginalActualPolarizedProductCaller20261102

/-- Exact actual completed-source consumer. The second source is the
literal nonzeroSource of completedPiece, including both signs of f and h,
fixed-unit gates and the complete m sum. No bound for it is assumed. -/
theorem exists_completedPiece_zero_paid (sigma L : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → kappa ≤ sigma/100 → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z, ∀ (A : ℕ)
        (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        (∀ s ∈ factorCarrier (roughS k), ‖lambda s‖ ≤ 1) →
        (∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) →
        atom.scale^(10*kappa) * (bareCauchyPrefactor atom k)^2 *
          ‖completedPiece A atom.residue (factorCarrier (roughS k)) (sourceKeyH atom k)
            lambda omega (spectralB atom k) (spectralC atom k) (spectralB atom k)
            (spectralC atom k) (countingF atom)‖ / (originalBareScale atom)^2 ≤
        atom.scale^(10*kappa) * (bareCauchyPrefactor atom k)^2 *
          ‖∑ s ∈ nonzeroSource (carrier A atom.residue (factorCarrier (roughS k))
            (sourceKeyH atom k) (Icc (Int.ceil (-countingF atom)) (Int.floor (countingF atom)))),
            weight lambda omega s * completedKernel (spectralB atom k)
              (spectralC atom k) (spectralC atom k) atom.residue (output s)‖ /
                (originalBareScale atom)^2 + 1 / Real.log atom.scale^L := by
  obtain ⟨x0,hx0,hpay⟩ := exists_normalizedZero_log_payment sigma L hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hA hkappa hx z k hk A lambda omega hlambda homega
  have hp := hpay B kappa c0 atom hA hkappa hx z k hk A lambda omega hlambda homega
  have hxpos : 0 < atom.scale := zero_lt_one.trans (scale_facts hA).2.2.2
  rw [original_completedPiece_split]
  have hnorm := norm_add_le (keyZeroPiece A atom k lambda omega)
    (∑ s ∈ nonzeroSource (carrier A atom.residue (factorCarrier (roughS k))
      (sourceKeyH atom k) (Icc (Int.ceil (-countingF atom)) (Int.floor (countingF atom)))),
      weight lambda omega s * completedKernel (spectralB atom k)
        (spectralC atom k) (spectralC atom k) atom.residue (output s))
  have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg (Real.rpow_nonneg hxpos.le _) (sq_nonneg _)))
      (sq_nonneg (originalBareScale atom))
  dsimp only [normalizedZero] at hp
  nlinarith only [hm,hp]

/-- The first square-root debit is exactly the D0 branch of (26), at
U^2/Q and with the once-retained phase x^(5*kappa). No whole bare bound
or Eq(16) source identification is asserted. -/
theorem exists_original_zero_sqrt_log_payment (sigma L : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → kappa ≤ sigma/100 → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z, ∀ (A : ℕ)
        (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        (∀ s ∈ factorCarrier (roughS k), ‖lambda s‖ ≤ 1) →
        (∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) →
        atom.scale^(5*kappa) * bareCauchyPrefactor atom k *
          Real.sqrt ‖keyZeroPiece A atom k lambda omega‖ ≤
            originalBareScale atom / Real.log atom.scale^L := by
  obtain ⟨x0,hx0,hpay⟩ := exists_normalizedZero_log_payment sigma (2*L) hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hA hkappa hx z k hk A lambda omega hlambda homega
  obtain ⟨hU,hV,hQ,hx1⟩ := scale_facts hA
  have hxpos : 0 < atom.scale := zero_lt_one.trans hx1
  have hlog : 0 < Real.log atom.scale := Real.log_pos hx1
  have hR : 0 < roughR k := zero_lt_one.trans_le (rough_scales_one_le k).1
  have hS : 0 < roughS k := zero_lt_one.trans_le (rough_scales_one_le k).2
  have hP : 0 ≤ bareCauchyPrefactor atom k := by dsimp [bareCauchyPrefactor]; positivity
  have hbase : 0 < originalBareScale atom := by dsimp [originalBareScale]; positivity
  have hp := hpay B kappa c0 atom hA hkappa hx z k hk A lambda omega hlambda homega
  have hphase : (atom.scale^(5*kappa))^2 = atom.scale^(10*kappa) := by
    rw [pow_two,← Real.rpow_add hxpos]
    congr 1
    ring
  have hlogpow : (Real.log atom.scale^L)^2 = Real.log atom.scale^(2*L) := by
    rw [pow_two,← Real.rpow_add hlog]
    congr 1
    ring
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [div_pow,hlogpow,mul_pow,mul_pow,hphase,Real.sq_sqrt (norm_nonneg _)]
  dsimp only [normalizedZero] at hp
  have hp' : atom.scale^(10*kappa) * (bareCauchyPrefactor atom k)^2 *
      ‖keyZeroPiece A atom k lambda omega‖ / (originalBareScale atom)^2 ≤
        1 / Real.log atom.scale^(2*L) := by
    convert hp using 1 <;> ring
  have hm := (div_le_iff₀ (sq_pos_of_pos hbase)).mp hp'
  calc
    atom.scale^(10*kappa) * (bareCauchyPrefactor atom k)^2 *
        ‖keyZeroPiece A atom k lambda omega‖ ≤
      (1 / Real.log atom.scale^(2*L)) * (originalBareScale atom)^2 := by
        convert hm using 1 <;> ring
    _ = _ := by ring

/-- The frozen original gamma2 polarization is accepted with its norm
proved from MediumAdmissible, for both independent smooth labels. -/
theorem exists_original_gamma2_zero_sqrt_log_payment (sigma L : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → kappa ≤ sigma/100 → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z, ∀ (A s s' : ℕ) (e : Fin 4)
        (omega : ℤ → ℂ),
        (∀ h ∈ poissonNonzeroFrequencyWindow (sourceKeyH atom k), ‖omega h‖ ≤ 1) →
        atom.scale^(5*kappa) * bareCauchyPrefactor atom k *
          Real.sqrt ‖keyZeroPiece A atom k
            (diagonal (gamma2Slot atom s) (gamma2Slot atom s') e) omega‖ ≤
              originalBareScale atom / Real.log atom.scale^L := by
  obtain ⟨x0,hx0,hpay⟩ := exists_original_zero_sqrt_log_payment sigma L hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hA hkappa hx z k hk A s s' e omega homega
  exact hpay B kappa c0 atom hA hkappa hx z k hk A _ omega
    (fun u _ => original_gamma2_coefficient_bound hA s s' e u) homega

end
end ImbalancedChen.Part3.OriginalZeroDifferenceCompletedConsumer20261102
