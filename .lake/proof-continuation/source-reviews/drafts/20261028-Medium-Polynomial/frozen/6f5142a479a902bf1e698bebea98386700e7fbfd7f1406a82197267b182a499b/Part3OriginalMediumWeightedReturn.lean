import ImbalancedChen.Part3ZRegularSpectralPolynomial
import ImbalancedChen.Part3ZExceptionalSpectralPolynomial
import Mathlib.Tactic

-- Original completion module, equations (24)--(25), lines 369--390.
-- This aggregates actual returned quadratic coefficients, including the zero mode.
-- The two imported cutoff comparisons are guarded, uncompiled source dependencies.
-- No analytic estimate or spectral theorem is assumed or supplied here.

namespace ImbalancedChen.Part3OriginalMediumWeightedReturn

open scoped BigOperators

noncomputable section

def prefactor (A U C D V Z : ℝ) : ℝ :=
  (D / C) ^ 2 * (V * C ^ 4 * Z / (A * V * U + C ^ 2 * Z))

def ordinary (A U C D Z L : ℝ) : ℝ :=
  C * (L + Z) * (C + D * Z) + A * U * Z

def exceptional (U C D Z θ : ℝ) : ℝ :=
  C * (C * D * Real.sqrt Z) ^ (2 * θ) *
    (U + Z) ^ (1 - θ) * (C + D * Z) ^ (1 - 2 * θ)

-- Finite sums suffice for each actual spectral block. The zero Poisson
-- coefficient D² U Z is outside the spectral prefactor and remains present.
theorem weighted_return_le_polynomial {ι : Type*} (s : Finset ι)
    (w L : ι → ℝ) {A U C D V Z θ ρ b : ℝ}
    (hA : 0 < A) (hU : 0 < U) (hC : 0 < C) (hD : 0 < D)
    (hV : 0 < V) (hZ : 0 < Z) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1 / 2)
    (hρ : 1 ≤ ρ) (hcut : V ≤ ρ * C / D)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hL : ∀ i ∈ s, 0 ≤ L i) (hb : 0 ≤ b) :
    prefactor A U C D V Z *
        ((∑ i ∈ s, w i * (L i + Z + A * V * U / C ^ 2) *
            (V + Z + A * V * U / C ^ 2)) +
          (C ^ 2 * Z) ^ θ * (U + Z) ^ (1 - θ) *
            (V + Z) ^ (1 - 2 * θ) * b) +
        D ^ 2 * U * Z * b ≤
      ρ ^ 2 * ((∑ i ∈ s, w i * ordinary A U C D Z (L i)) +
        exceptional U C D Z θ * b + D ^ 2 * U * Z * b) := by
  have hs : prefactor A U C D V Z *
      (∑ i ∈ s, w i * (L i + Z + A * V * U / C ^ 2) *
        (V + Z + A * V * U / C ^ 2)) ≤
      ρ ^ 2 * (∑ i ∈ s, w i * ordinary A U C D Z (L i)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hp := P3ZRegularSpectralPolynomial.regular_return_le_inflated_cutoff
      hA hU hC hD (hL i hi) hV hZ hρ hcut
    have hm := mul_le_mul_of_nonneg_left hp (hw i hi)
    dsimp [prefactor, ordinary]
    dsimp [prefactor, ordinary] at hm
    nlinarith only [hm]
  have he := P3ZExceptionalSpectralPolynomial.exceptional_return_le_inflated_cutoff
    hA hU hC hD hV hZ hθ hθ' hρ hcut
  have he' := mul_le_mul_of_nonneg_right he hb
  have hz : D ^ 2 * U * Z * b ≤ ρ ^ 2 * (D ^ 2 * U * Z * b) := by
    have hρsq : 1 ≤ ρ ^ 2 := by nlinarith [sq_nonneg (ρ - 1)]
    nlinarith [mul_le_mul_of_nonneg_right hρsq
      (show 0 ≤ D ^ 2 * U * Z * b by positivity)]
  dsimp [P3ZExceptionalSpectralPolynomial.exceptionalReturn,
    P3ZExceptionalSpectralPolynomial.exceptionalPolynomial] at he'
  dsimp [prefactor, exceptional] at *
  nlinarith only [hs, he', hz]

end
end ImbalancedChen.Part3OriginalMediumWeightedReturn
