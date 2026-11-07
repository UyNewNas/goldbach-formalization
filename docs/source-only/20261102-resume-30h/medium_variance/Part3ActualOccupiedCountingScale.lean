import ImbalancedChen.Part3OriginalSignedCountingNorm
import ImbalancedChen.Part3ActualSpectralUniformGeometry
import ImbalancedChen.Part3ActualSpectralDoubleCauchyNormalization
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
The finite coefficient in the actual reciprocal-square Poisson expansion,
at the literal keyRealH, is paid in the countingMass used by the two
Cauchy normalizations. The divisor and harmonic costs remain explicit.
No spectral estimate, source-reduction estimate, or bare bound is an input.
-/

namespace ImbalancedChen.Part3.ActualOccupiedCountingScale20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open ActualMediumVarianceAtomBindingSourceOnly OriginalLambdaTrimPoissonFamily20261028
open ActualOriginalSpectralScales20261028 ActualSpectralDoubleCauchyNormalization20261028
open ActualSpectralUniformGeometry20261028 OriginalSignedCountingNorm20261028
open LichtmanSignedDifferenceMultiplicity

def poissonLoss (atom : MediumAtom) (k : Key) : ℝ :=
  16 * keyD k * (Real.log atom.scale)^5

def sourceNorm (atom : MediumAtom) (k : Key) (A : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ) : ℝ :=
  countingNorm (roughS k) (keyRealH atom k) (countingF atom)
    A atom.residue lambda omega eps nu

def sourceDivisorCost (atom : MediumAtom) (k : Key) : ℝ :=
  1152 * (divisorMaximum (roughS k) (keyRealH atom k) (countingF atom) : ℝ)^5 *
    (harmonic (Nat.floor (2 * roughS k)) : ℝ)

theorem sourceDivisorCost_nonneg (atom : MediumAtom) (k : Key) :
    0 ≤ sourceDivisorCost atom k := by
  have hh : 0 ≤ (harmonic (Nat.floor (2 * roughS k)) : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  unfold sourceDivisorCost
  positivity

theorem scale_facts {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) :
    0 < atom.U ∧ 0 < atom.V ∧ 0 < atom.Q1 ∧ 1 < atom.scale := by
  refine ⟨zero_lt_one.trans_le hA.1, zero_lt_one.trans_le hA.2.1,
    zero_lt_one.trans_le hA.2.2.1, ?_⟩
  exact (Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans hA.2.2.2.2.2.1

theorem countingF_one_le {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (hsigma : 0 < sigma) :
    1 ≤ countingF atom := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hpow : atom.scale^(-sigma) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hx.le (show -sigma ≤ 0 by linarith)
  have hQN : atom.Q1 ≤ atom.U :=
    hA.2.2.2.2.2.2.2.2.1.le.trans (by simpa using mul_le_mul_of_nonneg_left hpow hN.le)
  exact (le_div_iff₀ hQ).mpr (by simpa using hQN)

theorem poisson_nonneg {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) :
    0 ≤ keyRealH atom k ∧ 0 ≤ poissonLoss atom k := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hlog : 0 ≤ Real.log atom.scale := Real.log_nonneg hx.le
  have hD : 0 ≤ keyD k := by unfold keyD; positivity
  constructor <;> dsimp [keyRealH,poissonLoss] <;> positivity

/-- The actual occupied total-rough scale, not a fresh H parameter,
supplies the factor 16 in the counting mass. -/
theorem actual_H_le_countingH {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (z : ℝ) (k : Key)
    (hk : k ∈ originalNumericKeys atom z) :
    keyRealH atom k ≤ countingH atom k (poissonLoss atom k) := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hD : 0 ≤ keyD k := by unfold keyD; positivity
  have hlog : 0 ≤ (Real.log atom.scale)^5 := pow_nonneg (Real.log_nonneg hx.le) _
  have hW := (actual_rough_owner_geometry hA
    (MediumReceiverCutoffArithmetic20261028.strictReceiverCutoff z)
    (originalSmoothTrim atom) k hk).2.2
  have hW0 : 0 ≤ keyR k := by unfold keyR; positivity
  have hsquare := pow_le_pow_left₀ hW0 hW 2
  calc
    keyRealH atom k ≤ atom.Q1 * keyD k * (4*roughR k*roughS k)^2 *
        (Real.log atom.scale)^5 / atom.V := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsquare (mul_nonneg hQ.le hD)) hlog) hM.le
    _ = countingH atom k (poissonLoss atom k) := by
      dsimp [countingH,poissonLoss]
      ring

/-- Eq. (23) at the original retained H. The H<1 branch is exactly
zero and never calls the nonempty counting theorem. -/
theorem sourceNorm_le_countingMass {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (hsigma : 0 < sigma)
    (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (hshort : 1 + keyRealH atom k / roughS k ≤ 2)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nu : ℕ) (hnu : 0 < nu) :
    sourceNorm atom k A lambda omega eps nu ≤ sourceDivisorCost atom k *
      countingMass atom k (poissonLoss atom k) / (nu : ℝ) := by
  have hS := (rough_scales_one_le k).2
  have hS0 : 0 ≤ roughS k := zero_le_one.trans hS
  have hH0 := (poisson_nonneg hA k).1
  have hF := countingF_one_le hA hsigma
  have hF0 : 0 ≤ countingF atom := zero_le_one.trans hF
  have hK0 := sourceDivisorCost_nonneg atom k
  have hmass0 : 0 ≤ countingMass atom k (poissonLoss atom k) := by
    unfold countingMass
    positivity
  by_cases hH : 1 ≤ keyRealH atom k
  · have hb := (actual_countingNorm_bound (roughS k) (keyRealH atom k)
      (countingF atom) A atom.residue lambda omega eps hS hH hF
      hlambda homega heps nu hnu).1
    have hHbound := actual_H_le_countingH hA z k hk
    have hsq := pow_le_pow_left₀ (mul_nonneg hH0 hS0)
      (mul_le_mul_of_nonneg_right hHbound hS0) 2
    have hharm : 0 ≤ (harmonic (Nat.floor (2 * roughS k)) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      exact sum_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    calc
      sourceNorm atom k A lambda omega eps nu ≤ _ := hb
      _ ≤ sourceDivisorCost atom k *
          (keyRealH atom k * roughS k)^2 * countingF atom / (nu : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        apply mul_le_mul_of_nonneg_right _ hF0
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        dsimp only [sourceDivisorCost]
        have ht := mul_le_mul_of_nonneg_left hshort
          (show 0 ≤ 576 *
            (divisorMaximum (roughS k) (keyRealH atom k) (countingF atom) : ℝ)^5 *
            (harmonic (Nat.floor (2 * roughS k)) : ℝ) by positivity)
        nlinarith only [ht]
      _ ≤ sourceDivisorCost atom k * countingMass atom k (poissonLoss atom k) /
          (nu : ℝ) := by
        unfold countingMass
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        have ht := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq hK0) hF0
        convert ht using 1 <;> ring
  · rw [sourceNorm, countingNorm_zero_of_short_H _ _ _ _ _ _ _ _ _ hH0 (lt_of_not_ge hH)]
    exact div_nonneg (mul_nonneg hK0 hmass0) (Nat.cast_nonneg _)

/-- The geometry hypothesis above is supplied before all atom/key and
coefficient choices by the already proved original uniform threshold. -/
theorem exists_source_counting_threshold (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      MediumAdmissible B sigma kappa c0 atom → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
        D0 atom k < 1 ∧ (spectralB atom k)^2 < atom.scale ∧
        ∀ (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ),
          (∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1) →
          (∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1) →
          (∀ zy, ‖eps zy‖ ≤ 1) → ∀ nu : ℕ, 0 < nu →
          sourceNorm atom k A lambda omega eps nu ≤ sourceDivisorCost atom k *
            countingMass atom k (poissonLoss atom k) / (nu : ℝ) := by
  obtain ⟨x0,hx0,hgeometry⟩ := exists_actual_spectral_geometry_threshold sigma hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hA hx z k hk
  obtain ⟨hD,hB,hH,hshort⟩ := hgeometry B kappa c0 atom hA hx z k hk
  refine ⟨hD,hB,?_⟩
  intro A lambda omega eps hlambda homega heps nu hnu
  exact sourceNorm_le_countingMass hA hsigma z k hk hshort
    A lambda omega eps hlambda homega heps nu hnu

end
end ImbalancedChen.Part3.ActualOccupiedCountingScale20261102
