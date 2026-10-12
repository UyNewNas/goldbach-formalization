import ImbalancedChen.AsymptoticTransfer
import ImbalancedChen.RationalPowers
import ImbalancedChen.SingularSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Current manuscript constants and conditional terminal transfer

This module records the constants and the three explicit conclusions in the
10 October 2026 manuscript.  Unlike the historical transfer modules, its
lower-count input is the actual `D12` count, which excludes receiver one and
matches the current definition of `D_{1,2}`.

The logarithmic margins and the common-threshold assembly are proved here.
The two analytic estimates remain explicit hypotheses: this file does not
prove the lower Chen-weight mean or the upper ordered-bad-semiprime estimate.
-/

namespace ImbalancedChen

noncomputable section

/-- The upper bad-semiprime coefficient in Theorem 1.1 (10 October 2026). -/
def currentK : ℝ := 8452171 / 1250000

/-- The lower `D_{1,2}` coefficient in Theorem 1.1 (10 October 2026). -/
def currentC : ℝ := 49044063 / 25000000

/-- Exact strict margin for the primary exponent `0.74816964`. -/
theorem current_gap_74816964 :
    (1 : ℝ) / 100000 <
      currentC - currentK * Real.log (25000000 / 18704241) := by
  have h := Real.log_div_le_sum_range_add
    (x := (6295759 : ℝ) / 43704241) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  dsimp [currentC, currentK]
  nlinarith only [h]

/-- Exact strict margin for the secondary exponent `0.74816865`. -/
theorem current_gap_74816865 :
    (1 : ℝ) / 1000000 <
      currentC - currentK * Real.log (20000000 / 14963373) := by
  have h := Real.log_div_le_sum_range_add
    (x := (5036627 : ℝ) / 34963373) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  dsimp [currentC, currentK]
  nlinarith only [h]

/-- Exact strict margin for the exponent `0.9`. -/
theorem current_gap_09 :
    (124889 : ℝ) / 100000 <
      currentC - currentK * Real.log (10 / 9) := by
  have h := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 19) (by norm_num) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  dsimp [currentC, currentK]
  nlinarith only [h]

/-- Conditional current-manuscript transfer at `b = 0.74816964`. -/
theorem eventually_RealDb_74816964_lower_of_current_bounds
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 18704241 25000000 N : ℝ) ≤
          (currentK * Real.log (25000000 / 18704241) + epsilon) *
            singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      singularNormalization N / 100000 ≤
        (RealDb (18704241 / 25000000 : ℝ) N : ℝ) := by
  have hTransfer := eventually_transfer_of_bounds
    (eventually_singularNormalization_pos.mono (fun _ hN _ => hN))
    hLower hUpper current_gap_74816964
  refine hTransfer.mono ?_
  intro N hN hEven
  have hCount : Db 18704241 25000000 N =
      RealDb (18704241 / 25000000 : ℝ) N := Db_eq_RealDb (by norm_num)
  calc
    singularNormalization N / 100000 =
        (1 / 100000 : ℝ) * singularNormalization N := by ring
    _ ≤ (Db 18704241 25000000 N : ℝ) := hN hEven
    _ = (RealDb (18704241 / 25000000 : ℝ) N : ℝ) := by rw [hCount]

/-- Conditional current-manuscript transfer at `b = 0.74816865`. -/
theorem eventually_RealDb_74816865_lower_of_current_bounds
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 14963373 20000000 N : ℝ) ≤
          (currentK * Real.log (20000000 / 14963373) + epsilon) *
            singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      singularNormalization N / 1000000 ≤
        (RealDb (14963373 / 20000000 : ℝ) N : ℝ) := by
  have hTransfer := eventually_transfer_of_bounds
    (eventually_singularNormalization_pos.mono (fun _ hN _ => hN))
    hLower hUpper current_gap_74816865
  refine hTransfer.mono ?_
  intro N hN hEven
  have hCount : Db 14963373 20000000 N =
      RealDb (14963373 / 20000000 : ℝ) N := Db_eq_RealDb (by norm_num)
  calc
    singularNormalization N / 1000000 =
        (1 / 1000000 : ℝ) * singularNormalization N := by ring
    _ ≤ (Db 14963373 20000000 N : ℝ) := hN hEven
    _ = (RealDb (14963373 / 20000000 : ℝ) N : ℝ) := by rw [hCount]

/-- Conditional current-manuscript transfer at `b = 0.9`. -/
theorem eventually_RealDb_09_lower_of_current_bounds
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 9 10 N : ℝ) ≤
          (currentK * Real.log (10 / 9) + epsilon) * singularNormalization N) :
    ∀ᶠ N in Filter.atTop, Even N →
      (124889 / 100000 : ℝ) * singularNormalization N ≤
        (RealDb (9 / 10 : ℝ) N : ℝ) := by
  have hTransfer := eventually_transfer_of_bounds
    (eventually_singularNormalization_pos.mono (fun _ hN _ => hN))
    hLower hUpper current_gap_09
  refine hTransfer.mono ?_
  intro N hN hEven
  have hCount : Db 9 10 N = RealDb (9 / 10 : ℝ) N := Db_eq_RealDb (by norm_num)
  calc
    (124889 / 100000 : ℝ) * singularNormalization N ≤ (Db 9 10 N : ℝ) := hN hEven
    _ = (RealDb (9 / 10 : ℝ) N : ℝ) := by rw [hCount]

/-- The three explicit conclusions in Corollary 1.2 share one threshold.

The hypotheses are precisely the current lower `D12` estimate and the three
corresponding upper estimates.  They remain analytic obligations. -/
theorem current_corollary_simultaneous_of_manuscript_bounds
    (hLower : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (currentC - epsilon) * singularNormalization N ≤ (D12 N : ℝ))
    (hUpper₁ : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 18704241 25000000 N : ℝ) ≤
          (currentK * Real.log (25000000 / 18704241) + epsilon) *
            singularNormalization N)
    (hUpper₂ : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 14963373 20000000 N : ℝ) ≤
          (currentK * Real.log (20000000 / 14963373) + epsilon) *
            singularNormalization N)
    (hUpper₃ : ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ N in Filter.atTop, Even N →
        (B 9 10 N : ℝ) ≤
          (currentK * Real.log (10 / 9) + epsilon) * singularNormalization N) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      singularNormalization N / 100000 ≤
          (RealDb (18704241 / 25000000 : ℝ) N : ℝ) ∧
      singularNormalization N / 1000000 ≤
          (RealDb (14963373 / 20000000 : ℝ) N : ℝ) ∧
      (124889 / 100000 : ℝ) * singularNormalization N ≤
          (RealDb (9 / 10 : ℝ) N : ℝ) := by
  have h₁ := eventually_RealDb_74816964_lower_of_current_bounds hLower hUpper₁
  have h₂ := eventually_RealDb_74816865_lower_of_current_bounds hLower hUpper₂
  have h₃ := eventually_RealDb_09_lower_of_current_bounds hLower hUpper₃
  apply Filter.eventually_atTop.mp
  refine (h₁.and (h₂.and h₃)).mono ?_
  rintro N ⟨h₁N, h₂N, h₃N⟩ hEven
  exact ⟨h₁N hEven, h₂N hEven, h₃N hEven⟩

end

end ImbalancedChen
