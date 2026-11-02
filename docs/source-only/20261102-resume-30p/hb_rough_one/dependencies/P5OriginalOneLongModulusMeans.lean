import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import Mathlib.Tactic

-- UNCOMPILED_ZERO_CREDIT. Original one-long (E5)/(6), fixed divisor orders.
-- Reuses the native elementary divisor means; no growing Brun rank enters J.
-- The arithmetic function fouvryTau k is the actual zeta convolution power.

namespace ImbalancedChen
namespace OriginalOneLongModulusMeans

noncomputable section
open Finset
open scoped BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def tauR (q : ℕ) : ℝ := q.divisors.card
def logBudget (D : ℕ) : ℝ := 1 + Real.log (D : ℝ)

theorem tau_power_le_ordered (J q : ℕ) (hq : q ≠ 0) :
    tauR q ^ J ≤ (fouvryTau (2 ^ J) q : ℝ) := by
  have h := fouvryTau_pow_le 2 J hq
  rw [fouvryTau_two] at h
  unfold tauR
  exact_mod_cast h

theorem fixed_tau_mean (J D : ℕ) (hD : 1 ≤ D) :
    (∑ q ∈ Ioc 0 D, tauR q ^ J) ≤
      (D : ℝ) * logBudget D ^ (2 ^ J - 1) := by
  calc
    _ ≤ ∑ q ∈ Ioc 0 D, (fouvryTau (2 ^ J) q : ℝ) :=
      Finset.sum_le_sum fun q hq => tau_power_le_ordered J q (mem_Ioc.mp hq).1.ne'
    _ ≤ _ := by
      simpa [logBudget] using sum_fouvryTau_le_real
        (k := 2 ^ J) (by positivity) (x := (D : ℝ)) (by exact_mod_cast hD)

theorem fixed_tau_reciprocal (J D : ℕ) :
    (∑ q ∈ Ioc 0 D, tauR q ^ J / (q : ℝ)) ≤ logBudget D ^ (2 ^ J) := by
  calc
    _ ≤ ∑ q ∈ Ioc 0 D, (fouvryTau (2 ^ J) q : ℝ) / (q : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_right
        (tau_power_le_ordered J q (mem_Ioc.mp hq).1.ne') (Nat.cast_nonneg _)
    _ ≤ _ := by simpa [logBudget] using sum_fouvryTau_div_le (2 ^ J) D

theorem fixed_tau_totient (J D : ℕ) (hD : 1 ≤ D) :
    (∑ q ∈ Ioc 0 D, tauR q ^ J / (q.totient : ℝ)) ≤
      logBudget D ^ (2 * 2 ^ J) := by
  calc
    _ ≤ ∑ q ∈ Ioc 0 D, (fouvryTau (2 ^ J) q : ℝ) / (q.totient : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      exact div_le_div_of_nonneg_right
        (tau_power_le_ordered J q (mem_Ioc.mp hq).1.ne') (Nat.cast_nonneg _)
    _ ≤ _ := by
      simpa [logBudget] using sum_fouvryTau_div_totient_le_real (2 ^ J)
        (x := (D : ℝ)) (by exact_mod_cast hD)

-- The actual physical bound |rho(q)|<=R*tau(q)^J is sufficient on ANY
-- selected positive modulus set Q. R is the fixed polylog factor, not x^o(1).
theorem physical_rho_moments (Q : Finset ℕ) (D J : ℕ) (R : ℝ) (rho : ℕ → ℂ)
    (hD : 1 ≤ D) (hR : 0 ≤ R) (hQ : Q ⊆ Ioc 0 D)
    (hrho : ∀ q ∈ Q, ‖rho q‖ ≤ R * tauR q ^ J) :
    (∑ q ∈ Q, ‖rho q‖) ≤ R * (D : ℝ) * logBudget D ^ (2 ^ J - 1) ∧
    (∑ q ∈ Q, ‖rho q‖ / (q : ℝ)) ≤ R * logBudget D ^ (2 ^ J) ∧
    (∑ q ∈ Q, ‖rho q‖ * tauR q / (q.totient : ℝ)) ≤
      R * logBudget D ^ (2 * 2 ^ (J + 1)) := by
  have hplain : (∑ q ∈ Q, ‖rho q‖) ≤ R * ∑ q ∈ Ioc 0 D, tauR q ^ J := by
    calc
      _ ≤ ∑ q ∈ Q, R * tauR q ^ J := Finset.sum_le_sum hrho
      _ = R * ∑ q ∈ Q, tauR q ^ J := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hQ (fun q _ _ => by unfold tauR; positivity)) hR
  have hrecip : (∑ q ∈ Q, ‖rho q‖ / (q : ℝ)) ≤
      R * ∑ q ∈ Ioc 0 D, tauR q ^ J / (q : ℝ) := by
    calc
      _ ≤ ∑ q ∈ Q, (R * tauR q ^ J) / (q : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact div_le_div_of_nonneg_right (hrho q hq) (Nat.cast_nonneg _)
      _ = R * ∑ q ∈ Q, tauR q ^ J / (q : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hQ (fun q _ _ => by unfold tauR; positivity)) hR
  have htotient : (∑ q ∈ Q, ‖rho q‖ * tauR q / (q.totient : ℝ)) ≤
      R * ∑ q ∈ Ioc 0 D, tauR q ^ (J + 1) / (q.totient : ℝ) := by
    calc
      _ ≤ ∑ q ∈ Q, (R * tauR q ^ J) * tauR q / (q.totient : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hrho q hq) (by unfold tauR; positivity))
          (Nat.cast_nonneg _)
      _ = R * ∑ q ∈ Q, tauR q ^ (J + 1) / (q.totient : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hQ (fun q _ _ => by unfold tauR; positivity)) hR
  refine ⟨?_, ?_, ?_⟩
  · exact hplain.trans (by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left (fixed_tau_mean J D hD) hR)
  · exact hrecip.trans (mul_le_mul_of_nonneg_left (fixed_tau_reciprocal J D) hR)
  · exact htotient.trans (mul_le_mul_of_nonneg_left (fixed_tau_totient (J + 1) D hD) hR)

end
end OriginalOneLongModulusMeans
end ImbalancedChen
