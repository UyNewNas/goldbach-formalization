import ImbalancedChen.Part3ActualOccupiedCountingScale
import Mathlib.Tactic

/-! Source only; uncompiled; zero formal credit.
Complete compression of the actual Eq. (25) regular, exceptional and
zero-Poisson polynomials. This is an inequality of the independently
defined returned polynomial; it does not assert Eq. (24) for a kernel.
-/

namespace ImbalancedChen.Part3.ActualReturnedPolynomialCompression20261102
noncomputable section
open ActualOriginalSpectralScales20261028 ActualSpectralDoubleCauchyNormalization20261028
open ActualOccupiedCountingScale20261102 MediumGlobalDyadicOwnership20261028

def regularPolynomial (atom : MediumAtom) (k : Key) (nu : ℕ) : ℝ :=
  spectralC atom k * (spectralU atom k / (nu : ℝ) + spectralZ k) *
    (spectralC atom k + spectralB atom k * spectralZ k) +
    (atom.residue.natAbs : ℝ) * spectralU atom k * spectralZ k

def exceptionalPolynomial (atom : MediumAtom) (k : Key) : ℝ :=
  ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalPolynomial
    (spectralU atom k) (spectralC atom k) (spectralB atom k) (spectralZ k) theta

def zeroPoissonPolynomial (atom : MediumAtom) (k : Key) : ℝ :=
  (spectralB atom k)^2 * spectralU atom k * spectralZ k

theorem positive_scales {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) :
    0 < spectralU atom k ∧ 0 < spectralC atom k ∧
      0 < spectralB atom k ∧ 0 < spectralZ k := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hR : 0 < roughR k := zero_lt_one.trans_le (rough_scales_one_le k).1
  have hS : 0 < roughS k := zero_lt_one.trans_le (rough_scales_one_le k).2
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [spectralU,spectralC,spectralB,spectralZ] <;> positivity

theorem regularPolynomial_nonneg {B : ℕ} {sigma kappa c0 : ℝ} {atom : MediumAtom}
    (hA : MediumAdmissible B sigma kappa c0 atom) (k : Key) (nu : ℕ) :
    0 ≤ regularPolynomial atom k nu := by
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  unfold regularPolynomial
  positivity

theorem regularPolynomial_le_monomials {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (hD0 : D0 atom k ≤ 1) (nu : ℕ) (hnu : 0 < nu) :
    regularPolynomial atom k nu ≤
      4 * (spectralC atom k * spectralB atom k * (spectralZ k)^2) +
      (atom.residue.natAbs : ℝ) * spectralU atom k * spectralZ k := by
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hUZ : spectralU atom k ≤ spectralZ k := by
    have ht : spectralU atom k / spectralZ k ≤ 1 := by
      rw [(actual_spectral_normalizations hA k).1]
      exact hD0
    simpa only [one_mul] using (div_le_iff₀ hZ).mp ht
  have hnu1 : (1 : ℝ) ≤ nu := by exact_mod_cast (Nat.succ_le_iff.mpr hnu)
  have hleft : spectralU atom k / (nu : ℝ) + spectralZ k ≤ 2 * spectralZ k := by
    linarith [(div_le_self hU.le hnu1).trans hUZ]
  have hright : spectralC atom k + spectralB atom k * spectralZ k ≤
      2 * (spectralB atom k * spectralZ k) := by
    linarith [(actual_spectral_normalizations hA k).2.2.2]
  have hproduct := mul_le_mul
    (mul_le_mul_of_nonneg_left hleft hC.le) hright
    (by positivity : 0 ≤ spectralC atom k + spectralB atom k * spectralZ k)
    (by positivity : 0 ≤ spectralC atom k * (2 * spectralZ k))
  unfold regularPolynomial
  nlinarith only [hproduct]

private theorem exceptional_power_product {C D Z : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hZ : 0 < Z) :
    C * (C * D * Real.sqrt Z)^(2*theta) *
      Z^(1-theta) * (D*Z)^(1-2*theta) =
      C^(1+2*theta) * D * Z^(2-2*theta) := by
  have hsqrt : (Real.sqrt Z)^(2*theta) = Z^theta := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZ.le]
    congr 1
    ring
  have hCp : C * C^(2*theta) = C^(1+2*theta) := by
    calc
      _ = C^(1 : ℝ) * C^(2*theta) := by rw [Real.rpow_one]
      _ = _ := (Real.rpow_add hC _ _).symm
  have hDp : D^(2*theta) * D^(1-2*theta) = D := by
    rw [← Real.rpow_add hD, show 2*theta+(1-2*theta) = (1 : ℝ) by ring,
      Real.rpow_one]
  have hZp : Z^theta * Z^(1-theta) * Z^(1-2*theta) = Z^(2-2*theta) := by
    rw [← Real.rpow_add hZ, ← Real.rpow_add hZ]
    congr 1
    ring
  rw [Real.mul_rpow (mul_nonneg hC.le hD.le) (Real.sqrt_nonneg Z),
    Real.mul_rpow hC.le hD.le, hsqrt, Real.mul_rpow hD.le hZ.le]
  calc
    _ = (C*C^(2*theta)) * (D^(2*theta)*D^(1-2*theta)) *
        (Z^theta*Z^(1-theta)*Z^(1-2*theta)) := by ring
    _ = _ := by rw [hCp,hDp,hZp]

/-- The two sums inside the enhanced exceptional polynomial are
compressed with their real powers, retaining the full Bspec factor. -/
theorem exceptionalPolynomial_le_monomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (hD0 : D0 atom k ≤ 1) :
    exceptionalPolynomial atom k ≤
      4 * ((spectralC atom k)^(1+2*theta) * spectralB atom k *
        (spectralZ k)^(2-2*theta)) := by
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hUZ : spectralU atom k ≤ spectralZ k := by
    have ht : spectralU atom k / spectralZ k ≤ 1 := by
      rw [(actual_spectral_normalizations hA k).1]
      exact hD0
    simpa only [one_mul] using (div_le_iff₀ hZ).mp ht
  have hleft := Real.rpow_le_rpow (by positivity : 0 ≤ spectralU atom k + spectralZ k)
    (show spectralU atom k + spectralZ k ≤ 2*spectralZ k by linarith)
    (show 0 ≤ 1-theta by norm_num [theta])
  have hright := Real.rpow_le_rpow
    (by positivity : 0 ≤ spectralC atom k + spectralB atom k * spectralZ k)
    (show spectralC atom k + spectralB atom k * spectralZ k ≤
      2*(spectralB atom k * spectralZ k) by
        linarith [(actual_spectral_normalizations hA k).2.2.2])
    (show 0 ≤ 1-2*theta by norm_num [theta])
  have htwo : (2 : ℝ)^(2-3*theta) ≤ 4 := by
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show 2-3*theta ≤ 2 by norm_num [theta])
    simpa only [Real.rpow_two] using hp
  unfold exceptionalPolynomial ImbalancedChen.P3ZExceptionalSpectralPolynomial.exceptionalPolynomial
  calc
    _ ≤ spectralC atom k * (spectralC atom k * spectralB atom k *
          Real.sqrt (spectralZ k))^(2*theta) * (2*spectralZ k)^(1-theta) *
          (2*(spectralB atom k*spectralZ k))^(1-2*theta) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hleft (by positivity)) hright
        (by positivity) (by positivity)
    _ = (2 : ℝ)^(2-3*theta) *
        ((spectralC atom k)^(1+2*theta) * spectralB atom k *
          (spectralZ k)^(2-2*theta)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hZ.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hD.le hZ.le)]
      calc
        _ = ((2 : ℝ)^(1-theta) * (2 : ℝ)^(1-2*theta)) *
            (spectralC atom k * (spectralC atom k*spectralB atom k*
              Real.sqrt (spectralZ k))^(2*theta) * (spectralZ k)^(1-theta) *
              (spectralB atom k*spectralZ k)^(1-2*theta)) := by ring
        _ = _ := by
          rw [exceptional_power_product hC hD hZ,
            ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
          congr 2
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)

theorem normalized_regularPolynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (hD0 : D0 atom k ≤ 1) (loss : ℝ) (nu : ℕ) (hnu : 0 < nu) :
    fourthNormalization atom k loss * (atom.residue.natAbs : ℝ)^theta *
      regularPolynomial atom k nu ≤
      loss^2 * (4 + (atom.residue.natAbs : ℝ)/atom.scale) * D1 atom k := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hF0 : 0 ≤ fourthNormalization atom k loss := by
    rw [fourthNormalization_eq_original hA]
    positivity
  have ht := mul_le_mul_of_nonneg_left
    (regularPolynomial_le_monomials hA k hD0 nu hnu)
    (mul_nonneg hF0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  obtain ⟨hmain,hresidue⟩ := regular_monomial_normalization hA k loss
  calc
    _ ≤ _ := ht
    _ = 4 * (fourthNormalization atom k loss * (atom.residue.natAbs : ℝ)^theta *
        (spectralC atom k*spectralB atom k*(spectralZ k)^2)) +
        fourthNormalization atom k loss * (atom.residue.natAbs : ℝ)^theta *
          ((atom.residue.natAbs : ℝ)*spectralU atom k*spectralZ k) := by ring
    _ = _ := by rw [hmain,hresidue]; ring

theorem normalized_exceptionalPolynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (hD0 : D0 atom k ≤ 1) (loss : ℝ) :
    fourthNormalization atom k loss * exceptionalPolynomial atom k ≤
      4 * loss^2 * D2 atom k := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  have hF0 : 0 ≤ fourthNormalization atom k loss := by
    rw [fourthNormalization_eq_original hA]
    positivity
  calc
    _ ≤ fourthNormalization atom k loss *
        (4*((spectralC atom k)^(1+2*theta)*spectralB atom k*
          (spectralZ k)^(2-2*theta))) :=
      mul_le_mul_of_nonneg_left (exceptionalPolynomial_le_monomial hA k hD0) hF0
    _ = 4 * (fourthNormalization atom k loss * (spectralC atom k)^(1+2*theta) *
        spectralB atom k * (spectralZ k)^(2-2*theta)) := by ring
    _ = _ := by rw [exceptional_monomial_normalization hA]; ring

/-- This is the genuine m=0 Poisson monomial, not the separately
excluded y=0 difference. The arithmetic residue factor is inserted
only after the original lower bound has supplied |a|>=1. -/
theorem normalized_zeroPoissonPolynomial {B : ℕ} {sigma kappa c0 : ℝ}
    {atom : MediumAtom} (hA : MediumAdmissible B sigma kappa c0 atom)
    (k : Key) (hB : (spectralB atom k)^2 ≤ atom.scale)
    (ha : 1 ≤ (atom.residue.natAbs : ℝ)) (loss : ℝ) :
    fourthNormalization atom k loss * zeroPoissonPolynomial atom k ≤
      loss^2 * D1 atom k := by
  obtain ⟨hN,hM,hQ,hx⟩ := scale_facts hA
  obtain ⟨hU,hC,hD,hZ⟩ := positive_scales hA k
  have hF0 : 0 ≤ fourthNormalization atom k loss := by
    rw [fourthNormalization_eq_original hA]
    positivity
  have haPow : 1 ≤ (atom.residue.natAbs : ℝ)^theta :=
    Real.one_le_rpow ha (by norm_num [theta])
  calc
    _ ≤ fourthNormalization atom k loss *
        (spectralC atom k*spectralB atom k*(spectralZ k)^2) :=
      mul_le_mul_of_nonneg_left (zeroPoisson_monomial_le_regular hA k hB) hF0
    _ ≤ fourthNormalization atom k loss * (atom.residue.natAbs : ℝ)^theta *
        (spectralC atom k*spectralB atom k*(spectralZ k)^2) := by
      have ht := mul_le_mul_of_nonneg_left haPow
        (show 0 ≤ fourthNormalization atom k loss *
          (spectralC atom k*spectralB atom k*(spectralZ k)^2) by positivity)
      convert ht using 1 <;> ring
    _ = _ := (regular_monomial_normalization hA k loss).1

end
end ImbalancedChen.Part3.ActualReturnedPolynomialCompression20261102
