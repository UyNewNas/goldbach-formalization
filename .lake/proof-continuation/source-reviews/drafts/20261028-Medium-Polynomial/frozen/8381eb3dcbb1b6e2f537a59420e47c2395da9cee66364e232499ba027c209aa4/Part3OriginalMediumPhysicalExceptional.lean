import ImbalancedChen.Part3OriginalMediumPhysicalOrdinary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

-- Original completion equations (25)--(26), lines 382--403.
-- The exceptional normalized coefficient is identified with the actual D2.
-- This proves physical power algebra only, relative to a guarded source import.

namespace ImbalancedChen.Part3OriginalMediumPhysicalExceptional

open Part3OriginalMediumPhysicalOrdinary

noncomputable section

def D2Factored (N Q R S M θ : ℝ) : ℝ :=
  N * Q * R ^ 2 * S ^ 5 / (N * M) ^ 2 * (N * R / S) ^ (2 * θ)

def D2Paper (N Q R S M θ : ℝ) : ℝ :=
  N ^ (1 + 2 * θ) * Q * R ^ (2 + 2 * θ) * S ^ (5 - 2 * θ) / (N * M) ^ 2

theorem D2_factored_eq_paper {N Q R S M θ : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hS : 0 < S) :
    D2Factored N Q R S M θ = D2Paper N Q R S M θ := by
  have hn : N ^ (1 + 2 * θ) = N * N ^ (2 * θ) := by
    rw [Real.rpow_add hN, Real.rpow_one]
  have hr : R ^ (2 + 2 * θ) = R ^ (2 : ℕ) * R ^ (2 * θ) := by
    rw [Real.rpow_add hR, Real.rpow_two]
  have hs : S ^ (5 - 2 * θ) = S ^ (5 : ℕ) / S ^ (2 * θ) := by
    rw [Real.rpow_sub hS, Real.rpow_natCast]
  dsimp [D2Factored, D2Paper]
  rw [Real.div_rpow (mul_nonneg hN.le hR.le) hS.le,
    Real.mul_rpow hN.le hR.le, hn, hr, hs]
  ring

theorem physical_C_over_Z (N R S : ℝ) (hS : S ≠ 0) :
    C N R S / Z S = N * R / S := by
  dsimp [C, Z]
  field_simp [hS]
  <;> ring

-- The reduced exceptional coefficient CDZ²(C/Z)^(2θ), after the
-- actual positive-Cauchy multiplier and the counting norm, is D2.
theorem exceptional_normalized_coefficient {N Q R S M θ : ℝ}
    (hN : 0 < N) (hQ : 0 < Q) (hR : 0 < R) (hS : 0 < S) (hM : 0 < M) :
    outerFourth N Q R S * (H Q R S M * S) ^ 2 * F N Q *
        (C N R S * D N R * Z S ^ 2 * (C N R S / Z S) ^ (2 * θ)) =
      (N ^ 2 / Q) ^ 4 * D2Paper N Q R S M θ := by
  rw [physical_C_over_Z N R S hS.ne', ← D2_factored_eq_paper hN hR hS]
  dsimp [outerFourth, H, F, C, D, Z, D2Factored]
  field_simp [hN.ne', hQ.ne', hR.ne', hS.ne', hM.ne']
  <;> ring

-- Exact dictionary for the ordinary D1 used next to D2: aθ is |a|^θ,
-- not a frozen moving-residue constant or a desired estimate.
theorem D1_literal (A N Q R S M θ : ℝ) :
    D1 (A ^ θ) N Q R S M =
      A ^ θ * N * Q * R ^ 2 * S ^ 5 / (N * M) ^ 2 := rfl

theorem actual_theta_dictionary {N Q R S M : ℝ}
    (hN : 0 < N) (hR : 0 < R) (hS : 0 < S) :
    D2Factored N Q R S M ((7 : ℝ) / 32) =
      N ^ ((23 : ℝ) / 16) * Q * R ^ ((39 : ℝ) / 16) *
        S ^ ((73 : ℝ) / 16) / (N * M) ^ 2 := by
  rw [D2_factored_eq_paper hN hR hS]
  norm_num [D2Paper]

end
end ImbalancedChen.Part3OriginalMediumPhysicalExceptional
