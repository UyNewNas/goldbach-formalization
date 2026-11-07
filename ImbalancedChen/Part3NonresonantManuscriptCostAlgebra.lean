import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite completed-box manuscript cost algebra

SOURCE-ONLY CANDIDATE; HOLD. No compiler, checker, or build was run for this file.

Source binding: `.lake/proof-continuation/source-reviews/
20261021-manuscript-cost-gap-audit-HOLD.json`, SHA256
e0f6d0c61280b3b8937fa2fe0479d2efc7381fc6e763c140cfb3c53d88d37f0b.
Its bound Appendix A is `../goldbach-research/
distribution-medium-completion-20261010.txt`, SHA256
93c7f00f3b2c147fde73105fdbd6d7cb56b78ca6ba241901bf0ca729ecfaaad7.
Lines 323--333 specify P and the completed-box resonance; lines 335--347
retain F in the squared coefficient norm; lines 382--400 specify the spectral
polynomial and its substitution. The audit states the resulting finite cost
lemma explicitly. This file proves only that scalar algebra.

Here x = U*V, F = U/Q, B = U*R, C = U*R*S, Z = S^2,
H = Q*R^2*S^2/V and Y = F*H*S. The prefactor is represented by its
exact squared normalization U^2/(Q^2*R^2*S^3). Thus the resonance theorem
is the squared version of P*sqrt(Diag) = (U^2/Q)*sqrt(D0).
The spectral theorem retains the actual real powers in all four monomials.

No assertion here supplies a coefficient norm, spectral estimate, supported
Cauchy inequality, general-D packet bridge, ceil-frequency comparison, or
analytic kernel. In particular this file does not connect to hLower/hUpper
or certify the full manuscript theorem. Fourth roots and analytic losses
are outside this candidate.
-/

namespace ImbalancedChen.Part3NonresonantManuscriptCostAlgebra

noncomputable section

def prefactorSq (U Q R S : ℝ) : ℝ :=
  U ^ 2 / (Q ^ 2 * R ^ 2 * S ^ 3)

def normalizer (U R S : ℝ) : ℝ := U ^ 4 * R ^ 4 * S ^ 6

def D0 (U V R S : ℝ) : ℝ := U ^ 2 * R ^ 2 * S / (U * V)

def D1 (U V Q R S a θ : ℝ) : ℝ :=
  a ^ θ * U * Q * R ^ 2 * S ^ 5 / (U * V) ^ 2

def D2 (U V Q R S θ : ℝ) : ℝ :=
  (U * R / S) ^ (2 * θ) * U * Q * R ^ 2 * S ^ 5 / (U * V) ^ 2

def zeroModeCost (V Q R S : ℝ) : ℝ := Q * R ^ 4 * S ^ 5 / V ^ 3

def diagonalCost (U V Q R S : ℝ) : ℝ :=
  (Q * R ^ 2 * S ^ 2 / V) * S * (U * R) * (U / Q) * (U * R * S)

def spectralCost (U V Q R S a θ : ℝ) : ℝ :=
  let H := Q * R ^ 2 * S ^ 2 / V
  let F := U / Q
  let B := U * R
  let C := U * R * S
  let Z := S ^ 2
  let Y := F * H * S
  (a ^ θ * (C * B * Z + a * Y) * Z +
    C ^ (1 + 2 * θ) * B * Z ^ ((2 : ℝ) - 2 * θ) +
    B ^ 2 * Y * Z) * (H * S) ^ 2 * F

/-- Exact squared resonance normalization, with the completed F = U/Q count. -/
theorem completed_diagonal_normalization
    {U V Q R S : ℝ} (hU : 0 < U) (hV : 0 < V) (hQ : 0 < Q)
    (hR : 0 < R) (hS : 0 < S) :
    prefactorSq U Q R S * diagonalCost U V Q R S =
      (U ^ 2 / Q) ^ 2 * D0 U V R S := by
  unfold prefactorSq diagonalCost D0
  field_simp [hU.ne', hV.ne', hQ.ne', hR.ne', hS.ne']

/-- P^4/(U^2/Q)^4 is the reciprocal spectral normalizer. -/
theorem prefactor_fourth_normalization
    {U Q R S : ℝ} (hU : 0 < U) (hQ : 0 < Q)
    (hR : 0 < R) (hS : 0 < S) :
    (prefactorSq U Q R S) ^ 2 / (U ^ 2 / Q) ^ 4 =
      1 / normalizer U R S := by
  unfold prefactorSq normalizer
  field_simp [hU.ne', hQ.ne', hR.ne', hS.ne']

/-- An exact real-power rewrite of the source's exceptional monomial. -/
theorem spectral_second_monomial
    {C Z : ℝ} (hC : 0 < C) (hZ : 0 < Z) (B θ : ℝ) :
    C ^ (1 + 2 * θ) * B * Z ^ ((2 : ℝ) - 2 * θ) =
      C * B * Z ^ 2 * (C / Z) ^ (2 * θ) := by
  rw [Real.rpow_add hC 1 (2 * θ), Real.rpow_sub hZ 2 (2 * θ),
    Real.rpow_one, Real.rpow_two, Real.div_rpow hC.le hZ.le (2 * θ)]
  field_simp [(Real.rpow_pos_of_pos hZ (2 * θ)).ne']

/-- All four source monomials are retained: D1, (a/x)D1, D2 and the zero mode. -/
theorem completed_spectral_normalization
    {U V Q R S : ℝ} (hU : 0 < U) (hV : 0 < V) (hQ : 0 < Q)
    (hR : 0 < R) (hS : 0 < S) (a θ : ℝ) :
    spectralCost U V Q R S a θ / normalizer U R S =
      (1 + a / (U * V)) * D1 U V Q R S a θ +
        D2 U V Q R S θ + zeroModeCost V Q R S := by
  unfold spectralCost
  dsimp only
  rw [spectral_second_monomial (by positivity) (by positivity)]
  have hratio : U * R * S / S ^ 2 = U * R / S := by
    field_simp [hS.ne']
  rw [hratio]
  unfold normalizer D1 D2 zeroModeCost
  field_simp [hU.ne', hV.ne', hQ.ne', hR.ne', hS.ne']

/-- The original geometry and a^theta >= 1 pay the zero Poisson mode. -/
theorem zero_mode_le_D1
    {U V Q R S a θ : ℝ} (hU : 0 < U) (hV : 0 < V) (hQ : 0 < Q)
    (hR : 0 < R) (hS : 0 < S) (ha : 1 ≤ a) (hθ : 0 ≤ θ)
    (hgeom : (U * R) ^ 2 ≤ U * V) :
    zeroModeCost V Q R S ≤ D1 U V Q R S a θ := by
  let base := U * Q * R ^ 2 * S ^ 5 / (U * V) ^ 2
  have hbase : 0 ≤ base := by dsimp [base]; positivity
  have hratio : (U * R) ^ 2 / (U * V) ≤ 1 :=
    (div_le_one (by positivity)).mpr hgeom
  calc
    zeroModeCost V Q R S = (U * R) ^ 2 / (U * V) * base := by
      dsimp [zeroModeCost, base]
      field_simp [hU.ne', hV.ne']
    _ ≤ 1 * base := mul_le_mul_of_nonneg_right hratio hbase
    _ ≤ a ^ θ * base :=
      mul_le_mul_of_nonneg_right (Real.one_le_rpow ha hθ) hbase
    _ = D1 U V Q R S a θ := by dsimp [base, D1]; ring

/-- The finite normalized polynomial bound before taking fourth roots. -/
theorem completed_spectral_upper_bound
    {U V Q R S a θ : ℝ} (hU : 0 < U) (hV : 0 < V) (hQ : 0 < Q)
    (hR : 0 < R) (hS : 0 < S) (ha : 1 ≤ a) (hθ : 0 ≤ θ)
    (hgeom : (U * R) ^ 2 ≤ U * V) :
    spectralCost U V Q R S a θ / normalizer U R S ≤
      2 * ((1 + a / (U * V)) * D1 U V Q R S a θ + D2 U V Q R S θ) := by
  rw [completed_spectral_normalization hU hV hQ hR hS]
  have hzero := zero_mode_le_D1 hU hV hQ hR hS ha hθ hgeom
  have ha0 : 0 ≤ a := by linarith
  have hD1 : 0 ≤ D1 U V Q R S a θ := by unfold D1; positivity
  have hD2 : 0 ≤ D2 U V Q R S θ := by unfold D2; positivity
  have hproduct : 0 ≤ a / (U * V) * D1 U V Q R S a θ := by positivity
  nlinarith

end
end ImbalancedChen.Part3NonresonantManuscriptCostAlgebra
