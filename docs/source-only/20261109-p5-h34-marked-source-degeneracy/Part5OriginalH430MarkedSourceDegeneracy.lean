import ImbalancedChen.Part5OriginalH430TrueCountMarkedGap

/-!
P5.6 / h34: sensitivity and degeneracy of the ACTUAL positive marked
source versus the ACTUAL arithmetic q-count.

This is a manuscript-local obstruction audit. The repaired 21-term
source comparison permits nonnegative (including zero) sigma. For zero
sigma, both the marked Phi source and Theta vanish while the arithmetic
q-receiver count is unchanged. Hence a positive arithmetic receiver
cannot have its unpaid q-versus-product gap paid by epsilon * Theta on
the primitive assumptions alone.

Support and coefficient monotonicity identify useful directions for
choosing the real marked family, but do NOT establish a source-to-count
injection, a positive normalized sigma, or an H430 owner.

SOURCE ONLY: uncompiled / no kernel replay / no axioms audit.
-/

namespace ImbalancedChen.Part5OriginalH430MarkedSourceDegeneracy

noncomputable section

open scoped Classical BigOperators
open P2EnhancedTwentyOneSameQWeighted
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430TrueCountMarkedGap

/-- Adding genuine marked indices with nonnegative coefficients cannot
decrease the original finite positive sieve source. This does not
identify any marked product d with an arithmetic quotient prime q. -/
theorem phi_support_mono (N : ℕ) (Q : ℝ)
    (D E : Finset ℕ) (sigma : ℕ → ℝ) (w : ℝ)
    (hDE : D ⊆ E) (hsigma : ∀ d ∈ E, 0 ≤ sigma d) :
    Phi N Q D sigma w ≤ Phi N Q E sigma w := by
  unfold Phi
  apply Finset.sum_le_sum_of_subset_of_nonneg hDE
  intro d hd _
  exact mul_nonneg (hsigma d hd) (Nat.cast_nonneg _)

/-- The source-to-q unpaid positive gap can only decrease when the
finite marked support grows with the same nonnegative weights. -/
theorem unpaid_gap_support_antitone
    (N precision p : ℕ) (k : Root) (tau : ℝ)
    (D E : Finset ℕ) (sigma : ℕ → ℝ)
    (hDE : D ⊆ E) (hsigma : ∀ d ∈ E, 0 ≤ sigma d) :
    unpaidOriginalMarkedGap N precision p k tau E sigma ≤
      unpaidOriginalMarkedGap N precision p k tau D sigma := by
  have hphi := phi_support_mono N (rootQ N precision k tau p)
    D E sigma (11/5) hDE hsigma
  unfold unpaidOriginalMarkedGap originalMarkedDiscrepancy
  apply max_le_max ?_ le_rfl
  linarith only [hphi]

/-- Increasing genuine nonnegative marked coefficients (at fixed
support) cannot decrease the exact finite positive source. -/
theorem phi_weights_mono (N : ℕ) (Q : ℝ)
    (D : Finset ℕ) (sigma rho : ℕ → ℝ) (w : ℝ)
    (hweights : ∀ d ∈ D, sigma d ≤ rho d) :
    Phi N Q D sigma w ≤ Phi N Q D rho w := by
  unfold Phi
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_right (hweights d hd) (Nat.cast_nonneg _)

/-- Coefficient monotonicity transfers to the full arithmetic-versus-
marked unpaid gap, preserving actual root-specific Q and the q count. -/
theorem unpaid_gap_weights_antitone
    (N precision p : ℕ) (k : Root) (tau : ℝ)
    (D : Finset ℕ) (sigma rho : ℕ → ℝ)
    (hweights : ∀ d ∈ D, sigma d ≤ rho d) :
    unpaidOriginalMarkedGap N precision p k tau D rho ≤
      unpaidOriginalMarkedGap N precision p k tau D sigma := by
  have hphi := phi_weights_mono N (rootQ N precision k tau p)
    D sigma rho (11/5) hweights
  unfold unpaidOriginalMarkedGap originalMarkedDiscrepancy
  apply max_le_max ?_ le_rfl
  linarith only [hphi]

/-- The primitive nonnegative-weight gate admits sigma=0 for ANY D:
then the original positive-part discrepancy is exactly the true q-card,
not a paid analytic error. -/
theorem zero_sigma_unpaid_eq_count
    (N precision p : ℕ) (k : Root) (tau : ℝ)
    (D : Finset ℕ) :
    unpaidOriginalMarkedGap N precision p k tau D (fun _ => (0 : ℝ)) =
      ((originalReceiver N p).card : ℝ) := by
  have hnonneg : (0 : ℝ) ≤ ((originalReceiver N p).card : ℝ) := by positivity
  simp [unpaidOriginalMarkedGap, originalMarkedDiscrepancy, Phi,
    max_eq_left hnonneg]

/-- The same zero-weight choice makes the exact Theta_Q normalizer 0. -/
theorem zero_sigma_theta_eq_zero (N : ℕ) (Q : ℝ) (D : Finset ℕ) :
    Theta N Q D (fun _ => (0 : ℝ)) = 0 := by
  simp [Theta]

/-- Real obstruction: if the original q-fibre is nonempty, no
epsilon*Theta payment of its gap follows for all nonnegative sigma.
The counterexample is the admissible zero-weight family, even with
a nonempty finite support D. A genuine quantitative source coverage
condition is necessary and remains a manuscript-INTERNAL obligation. -/
theorem zero_sigma_cannot_pay_positive_q_fibre
    (N precision p : ℕ) (k : Root) (tau epsilon : ℝ)
    (D : Finset ℕ) (hcount : 0 < (originalReceiver N p).card) :
    ¬ unpaidOriginalMarkedGap N precision p k tau D (fun _ => (0 : ℝ)) ≤
      epsilon * Theta N (rootQ N precision k tau p) D (fun _ => (0 : ℝ)) := by
  have hpositive : (0 : ℝ) < ((originalReceiver N p).card : ℝ) := by
    exact_mod_cast hcount
  rw [zero_sigma_unpaid_eq_count N precision p k tau D,
    zero_sigma_theta_eq_zero, mul_zero]
  exact not_le.mpr hpositive

end
end ImbalancedChen.Part5OriginalH430MarkedSourceDegeneracy
