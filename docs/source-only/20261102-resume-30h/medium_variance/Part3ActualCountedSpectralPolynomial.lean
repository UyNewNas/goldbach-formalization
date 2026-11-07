import ImbalancedChen.Part3ActualReturnedPolynomialCompression
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Eq. (23) is consumed by the literal Eq. (25) polynomial, then the two
Cauchy normalizations give D1,D2. The actual coefficient is sourceNorm,
defined from the reciprocal-square Poisson output. The finite auxiliary
divisor sum stays explicit; no subpower theorem or spectral return is
postulated. The earlier zero-difference D0 identity remains separate.
-/

namespace ImbalancedChen.Part3.ActualCountedSpectralPolynomial20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open MediumGlobalDyadicOwnership20261028 OriginalSamePsiS1OwnedAtlas
open ActualMediumVarianceAtomBindingSourceOnly OriginalLambdaTrimPoissonFamily20261028
open ActualOriginalSpectralScales20261028 ActualSpectralDoubleCauchyNormalization20261028
open ActualSpectralUniformGeometry20261028 ActualOccupiedCountingScale20261102
open ActualReturnedPolynomialCompression20261102 LichtmanSignedDifferenceMultiplicity

def normalizingFactor (atom : MediumAtom) (k : Key) : ℝ :=
  (bareCauchyPrefactor atom k)^4 / (originalBareScale atom)^4

def auxiliaryWeight (nus : Finset ℕ) : ℝ :=
  ∑ nu ∈ nus, (nu : ℝ)^(theta-1)

/-- The Eq. (25) expression before its two square roots. In particular
the ordinary arithmetic packet factor is (|a| nu)^theta; m=0 uses the
all-source norm nu=1 and is retained separately from the nonzero
spectral terms. All these norms still concern the nonzero y source. -/
def countedPolynomial (atom : MediumAtom) (k : Key) (A : ℕ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (nus : Finset ℕ) : ℝ :=
  (∑ nu ∈ nus, ((atom.residue.natAbs : ℝ) * (nu : ℝ))^theta *
    regularPolynomial atom k nu * sourceNorm atom k A lambda omega eps nu) +
  (exceptionalPolynomial atom k + zeroPoissonPolynomial atom k) *
    sourceNorm atom k A lambda omega eps 1

theorem normalizingFactor_nonneg (atom : MediumAtom) (k : Key) :
    0 ≤ normalizingFactor atom k := by
  unfold normalizingFactor
  positivity

theorem normalizingFactor_mul_mass (atom : MediumAtom) (k : Key) (loss : ℝ) :
    normalizingFactor atom k * countingMass atom k loss =
      fourthNormalization atom k loss := by
  unfold normalizingFactor fourthNormalization
  ring

private theorem nu_power_div (nu : ℕ) (hnu : 0 < nu) :
    (nu : ℝ)^theta / (nu : ℝ) = (nu : ℝ)^(theta-1) := by
  have hnuR : (0 : ℝ) < nu := by exact_mod_cast hnu
  rw [Real.rpow_sub hnuR,Real.rpow_one]

theorem normalized_regular_source {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (hsigma : 0 < sigma) (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (hD0 : D0 atom k ≤ 1) (hshort : 1 + keyRealH atom k / roughS k ≤ 2)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nu : ℕ) (hnu : 0 < nu) :
    normalizingFactor atom k *
      (((atom.residue.natAbs : ℝ)*(nu : ℝ))^theta * regularPolynomial atom k nu *
        sourceNorm atom k A lambda omega eps nu) ≤
      sourceDivisorCost atom k * (poissonLoss atom k)^2 * (nu : ℝ)^(theta-1) *
        ((4+(atom.residue.natAbs : ℝ)/atom.scale)*D1 atom k) := by
  have hcount := sourceNorm_le_countingMass hA hsigma z k hk hshort
    A lambda omega eps hlambda homega heps nu hnu
  have hq0 := normalizingFactor_nonneg atom k
  have hreg0 := regularPolynomial_nonneg hA k nu
  have hK0 := sourceDivisorCost_nonneg atom k
  have hscale := normalized_regularPolynomial hA k hD0 (poissonLoss atom k) nu hnu
  calc
    _ ≤ normalizingFactor atom k *
        (((atom.residue.natAbs : ℝ)*(nu : ℝ))^theta * regularPolynomial atom k nu *
          (sourceDivisorCost atom k * countingMass atom k (poissonLoss atom k) /
            (nu : ℝ))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcount (by positivity)) hq0
    _ = sourceDivisorCost atom k * (nu : ℝ)^(theta-1) *
        (fourthNormalization atom k (poissonLoss atom k) *
          (atom.residue.natAbs : ℝ)^theta * regularPolynomial atom k nu) := by
      rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      calc
        _ = sourceDivisorCost atom k * ((nu : ℝ)^theta / (nu : ℝ)) *
            ((normalizingFactor atom k * countingMass atom k (poissonLoss atom k)) *
              (atom.residue.natAbs : ℝ)^theta * regularPolynomial atom k nu) := by ring
        _ = _ := by rw [normalizingFactor_mul_mass,nu_power_div nu hnu]
    _ ≤ sourceDivisorCost atom k * (nu : ℝ)^(theta-1) *
        ((poissonLoss atom k)^2 * (4+(atom.residue.natAbs : ℝ)/atom.scale)*D1 atom k) :=
      mul_le_mul_of_nonneg_left hscale (mul_nonneg hK0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    _ = _ := by ring

theorem normalized_exceptional_zero_source {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (hsigma : 0 < sigma) (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (hD0 : D0 atom k ≤ 1) (hB : (spectralB atom k)^2 ≤ atom.scale)
    (ha : 1 ≤ (atom.residue.natAbs : ℝ))
    (hshort : 1 + keyRealH atom k / roughS k ≤ 2)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) :
    normalizingFactor atom k *
      ((exceptionalPolynomial atom k+zeroPoissonPolynomial atom k) *
        sourceNorm atom k A lambda omega eps 1) ≤
      sourceDivisorCost atom k * (poissonLoss atom k)^2 * (4*D2 atom k+D1 atom k) := by
  have hcount := sourceNorm_le_countingMass hA hsigma z k hk hshort
    A lambda omega eps hlambda homega heps 1 (by norm_num)
  simp only [Nat.cast_one,div_one] at hcount
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hpoly0 : 0 ≤ exceptionalPolynomial atom k+zeroPoissonPolynomial atom k := by
    unfold exceptionalPolynomial zeroPoissonPolynomial
      ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalPolynomial
    positivity
  have hq0 := normalizingFactor_nonneg atom k
  have hK0 := sourceDivisorCost_nonneg atom k
  have hscale := add_le_add
    (normalized_exceptionalPolynomial hA k hD0 (poissonLoss atom k))
    (normalized_zeroPoissonPolynomial hA k hB ha (poissonLoss atom k))
  calc
    _ ≤ normalizingFactor atom k *
        ((exceptionalPolynomial atom k+zeroPoissonPolynomial atom k) *
          (sourceDivisorCost atom k * countingMass atom k (poissonLoss atom k))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount hpoly0) hq0
    _ = sourceDivisorCost atom k *
        (fourthNormalization atom k (poissonLoss atom k) * exceptionalPolynomial atom k +
          fourthNormalization atom k (poissonLoss atom k) * zeroPoissonPolynomial atom k) := by
      simp only [← normalizingFactor_mul_mass]
      ring
    _ ≤ sourceDivisorCost atom k *
        (4*(poissonLoss atom k)^2*D2 atom k+(poissonLoss atom k)^2*D1 atom k) :=
      mul_le_mul_of_nonneg_left hscale hK0
    _ = _ := by ring

/-- Full finite Eq. (25) normalization at the independently defined
Poisson coefficient. No bound on countedPolynomial is assumed. -/
theorem countedPolynomial_bound {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (hsigma : 0 < sigma) (z : ℝ) (k : Key) (hk : k ∈ originalNumericKeys atom z)
    (hD0 : D0 atom k ≤ 1) (hB : (spectralB atom k)^2 ≤ atom.scale)
    (ha : 1 ≤ (atom.residue.natAbs : ℝ))
    (hshort : 1 + keyRealH atom k / roughS k ≤ 2)
    (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nus : Finset ℕ) (hnus : ∀ nu ∈ nus, 0 < nu) :
    normalizingFactor atom k * countedPolynomial atom k A lambda omega eps nus ≤
      sourceDivisorCost atom k * (poissonLoss atom k)^2 *
        (auxiliaryWeight nus * (4+(atom.residue.natAbs : ℝ)/atom.scale)*D1 atom k +
          4*D2 atom k+D1 atom k) := by
  have hreg := sum_le_sum (fun nu hnu => normalized_regular_source hA hsigma z k hk
    hD0 hshort A lambda omega eps hlambda homega heps nu (hnus nu hnu))
  have hexc := normalized_exceptional_zero_source hA hsigma z k hk hD0 hB ha hshort
    A lambda omega eps hlambda homega heps
  unfold countedPolynomial
  rw [mul_add,mul_sum]
  calc
    _ ≤ (∑ nu ∈ nus, sourceDivisorCost atom k * (poissonLoss atom k)^2 *
        (nu : ℝ)^(theta-1) * ((4+(atom.residue.natAbs : ℝ)/atom.scale)*D1 atom k)) +
        sourceDivisorCost atom k * (poissonLoss atom k)^2 * (4*D2 atom k+D1 atom k) :=
      add_le_add hreg hexc
    _ = _ := by
      simp only [auxiliaryWeight, ← sum_mul, ← mul_sum]
      ring

/-- One threshold precedes every atom, occupied key, coefficient and
finite auxiliary support. All geometry premises of the preceding
finite theorem are discharged from the original MediumAdmissible. -/
theorem exists_countedPolynomial_threshold (sigma : ℝ) (hsigma : 0 < sigma) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ (B : ℕ) (kappa c0 : ℝ) (atom : MediumAtom),
      0 < c0 → MediumAdmissible B sigma kappa c0 atom → x0 ≤ atom.scale →
      ∀ z : ℝ, ∀ k ∈ originalNumericKeys atom z,
      ∀ (A : ℕ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ),
      (∀ s ∈ dyadicCarrier (roughS k), ‖lambda s‖ ≤ 1) →
      (∀ h ∈ frequencyCarrier (keyRealH atom k), ‖omega h‖ ≤ 1) →
      (∀ zy, ‖eps zy‖ ≤ 1) → ∀ nus : Finset ℕ, (∀ nu ∈ nus, 0 < nu) →
      normalizingFactor atom k * countedPolynomial atom k A lambda omega eps nus ≤
        sourceDivisorCost atom k * (poissonLoss atom k)^2 *
          (auxiliaryWeight nus * (4+(atom.residue.natAbs : ℝ)/atom.scale)*D1 atom k +
            4*D2 atom k+D1 atom k) := by
  obtain ⟨x0,hx0,hgeometry⟩ := exists_actual_spectral_geometry_threshold sigma hsigma
  refine ⟨x0,hx0,?_⟩
  intro B kappa c0 atom hc0 hA hx z k hk A lambda omega eps hlambda homega heps nus hnus
  obtain ⟨hD0,hB,hH,hshort⟩ := hgeometry B kappa c0 atom hA hx z k hk
  obtain ⟨hN,hM,hQ,hxone⟩ := scale_facts hA
  have haPos : (0 : ℝ) < atom.residue.natAbs :=
    (mul_pos hc0 (zero_lt_one.trans hxone)).trans_le hA.2.2.2.2.2.2.1
  have haNat : 0 < atom.residue.natAbs := by exact_mod_cast haPos
  have haOne : (1 : ℝ) ≤ atom.residue.natAbs := by
    exact_mod_cast (Nat.succ_le_iff.mpr haNat)
  exact countedPolynomial_bound hA hsigma z k hk hD0.le hB.le haOne hshort
    A lambda omega eps hlambda homega heps nus hnus

end
end ImbalancedChen.Part3.ActualCountedSpectralPolynomial20261102
