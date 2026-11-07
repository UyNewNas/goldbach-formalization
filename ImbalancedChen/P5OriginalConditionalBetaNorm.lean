import ImbalancedChen.P5OriginalOrdinaryBetaRegroup
import ImbalancedChen.RoughAbsoluteDensity
import ImbalancedChen.TotientReciprocalBudget

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Quantitative norms for the actual conditional small coefficient lambda(e*d).
The rough factor d remains a parameter; no independent beta, distribution
estimate, or density hypothesis is substituted. Squared coefficients equal
their absolute values because the literal original Rosser values are 0,1,-1.
The small reciprocal-totient norms have both a finite Euler envelope and a
residual-level logarithmic envelope. Physical denominators retain phi(d).
-/

namespace ImbalancedChen.P5Z.OriginalConditionalBetaNorm

noncomputable section
open scoped BigOperators
open Classical
open OriginalOrdinaryBetaRegroup

/-- A slice of the original native coefficient, with its rough state intact. -/
def coefficient (N cap : ℕ) (Z L : ℝ) (d e : ℕ) : ℝ :=
  actualSmallRosserPlus N cap Z L (e*d)

def activeSmall (N cap : ℕ) (w Z L : ℝ) (d : ℕ) : Finset ℕ :=
  (actualSmallRosserSupport N cap w).filter (fun e => coefficient N cap Z L d e ≠ 0)

def l1Phi (N cap : ℕ) (w Z L : ℝ) (d : ℕ) : ℝ :=
  ∑ e ∈ actualSmallRosserSupport N cap w,
    |coefficient N cap Z L d e| / (Nat.totient e : ℝ)

/-- This is the squared weighted l2 norm, rather than its square root. -/
def l2PhiSq (N cap : ℕ) (w Z L : ℝ) (d : ℕ) : ℝ :=
  ∑ e ∈ actualSmallRosserSupport N cap w,
    (coefficient N cap Z L d e)^2 / (Nat.totient e : ℝ)

/-- The actual native coefficient is 0 or a sign, so there is no l2 loss. -/
theorem coefficient_sq_eq_abs (N cap : ℕ) (Z L : ℝ) (d e : ℕ) :
    (coefficient N cap Z L d e)^2 = |coefficient N cap Z L d e| := by
  change (MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
      (actualSmallPrimeProduct N cap Z) L (e*d))^2 =
    |MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
      (actualSmallPrimeProduct N cap Z) L (e*d)|
  rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply]
  simp only [neg_one_pow_eq_ite]
  split_ifs <;> norm_num

theorem l2PhiSq_eq_l1Phi (N cap : ℕ) (w Z L : ℝ) (d : ℕ) :
    l2PhiSq N cap w Z L d = l1Phi N cap w Z L d := by
  unfold l2PhiSq l1Phi
  apply Finset.sum_congr rfl
  intro e he
  rw [coefficient_sq_eq_abs]

/-- All small support, squarefreeness and target coprimality are actual;
small/rough separation also supplies the needed coprimality with d. -/
theorem activeSmall_arithmetic {N cap d e : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) (he : e ∈ activeSmall N cap w Z L d) :
    Squarefree e ∧ e.Coprime N ∧ e.Coprime d ∧ SmallPrimeSupportedAt w e := by
  have heS := (Finset.mem_filter.mp he).1
  have hsmall := actualSmallRosserSupport_smallPrimeSupportedAt N cap w heS
  exact ⟨actualSmallRosserSupport_squarefree N cap w heS,
    actualSmallRosserSupport_coprime_target N cap w heS,
    smallPrimeSupportedAt_coprime_roughPrimeSupportedAt hsmall (roughSupport_rough hd),
    hsmall⟩

/-- The level in a conditional small row is L/d, not L and not a fixed
independent presieve level. The strict endpoint remains strict. -/
theorem activeSmall_residual_level {N cap d e : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) (he : e ∈ activeSmall N cap w Z L d) :
    (e : ℝ) < L / (d : ℝ) := by
  have hdpos : (0 : ℝ) < d := by
    exact_mod_cast Nat.pos_of_ne_zero (roughSupport_rough hd).1
  apply (lt_div_iff₀ hdpos).mpr
  have h := (actualSmallRosserPlus_active (Finset.mem_filter.mp he).2).2.1
  simpa only [Nat.cast_mul] using h

theorem activeSmall_subset_residual_cap {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) :
    activeSmall N cap w Z L d ⊆ Finset.Icc 1 (Nat.ceil (L / (d : ℝ))) := by
  intro e he
  have he0 := (activeSmall_arithmetic hd he).1.ne_zero
  refine Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr he0, ?_⟩
  exact_mod_cast (activeSmall_residual_level hd he).le.trans (Nat.le_ceil _)

/-- Removing zero coefficients makes the true residual support available
for quantitative estimates without changing this norm. -/
theorem l1Phi_eq_active (N cap : ℕ) (w Z L : ℝ) (d : ℕ) :
    l1Phi N cap w Z L d = ∑ e ∈ activeSmall N cap w Z L d,
      |coefficient N cap Z L d e| / (Nat.totient e : ℝ) := by
  unfold l1Phi activeSmall
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hz : coefficient N cap Z L d e = 0 <;> simp [hz]

/-- Uniform in the actual rough state, with the exact finite small-prime
Euler product. No evenness or lower bound for the cutoff is required. -/
theorem l1Phi_le_eulerProduct (N cap : ℕ) (w Z L : ℝ) (d : ℕ) :
    l1Phi N cap w Z L d ≤
      ∏ p ∈ actualSmallPrimeFinset N cap w, (1 + 1 / ((p : ℝ) - 1)) := by
  have hcop : ∀ p ∈ actualSmallPrimeFinset N cap w, Nat.Coprime p N := by
    intro p hp
    exact (mem_actualSmallPrimeFinset.mp hp).2.1.coprime_iff_not_dvd.mpr
      (mem_actualSmallPrimeFinset.mp hp).2.2.1
  calc
    _ ≤ ∑ e ∈ actualSmallRosserSupport N cap w, 1 / (Nat.totient e : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      exact div_le_div_of_nonneg_right
        (actualSmallRosserPlus_abs_le_one N cap Z L (e*d)) (Nat.cast_nonneg _)
    _ = _ := reciprocalTotient_sum_divisors_primeProduct N _
      (actualSmallPrimeFinset_prime N cap w) hcop

theorem l2PhiSq_le_eulerProduct (N cap : ℕ) (w Z L : ℝ) (d : ℕ) :
    l2PhiSq N cap w Z L d ≤
      ∏ p ∈ actualSmallPrimeFinset N cap w, (1 + 1 / ((p : ℝ) - 1)) := by
  rw [l2PhiSq_eq_l1Phi]
  exact l1Phi_le_eulerProduct N cap w Z L d

/-- A second envelope uses the genuine conditional residual level, so a
large rough factor decreases the admissible small support. -/
theorem l1Phi_le_residual_log {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) :
    l1Phi N cap w Z L d ≤
      4 * (1 + Real.log (max 1 (Nat.ceil (L/(d:ℝ)) : ℝ))) := by
  rw [l1Phi_eq_active]
  calc
    _ ≤ ∑ e ∈ activeSmall N cap w Z L d, 1 / (Nat.totient e : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      exact div_le_div_of_nonneg_right
        (actualSmallRosserPlus_abs_le_one N cap Z L (e*d)) (Nat.cast_nonneg _)
    _ ≤ _ := sum_reciprocal_totient_subset_le_log _ _ (activeSmall_subset_residual_cap hd)

/-- Exact peeling for the denominator of the complete native modulus e*d.
The d-dependent coefficient remains INSIDE the conditional small sum. -/
theorem full_modulus_l1Phi_eq {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      |coefficient N cap Z L d e| / (Nat.totient (e*d) : ℝ)) =
      l1Phi N cap w Z L d / (Nat.totient d : ℝ) := by
  unfold l1Phi
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e he
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he) (roughSupport_rough hd)
  rw [Nat.totient_mul hcop, Nat.cast_mul, div_mul_eq_div_div]

/-- The physical-denominator mass has the same finite small Euler envelope
with its necessary rough reciprocal-totient factor. -/
theorem full_modulus_l1Phi_le {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∈ roughSupport N cap w Z) :
    (∑ e ∈ actualSmallRosserSupport N cap w,
      |coefficient N cap Z L d e| / (Nat.totient (e*d) : ℝ)) ≤
      (∏ p ∈ actualSmallPrimeFinset N cap w, (1 + 1 / ((p : ℝ) - 1))) /
        (Nat.totient d : ℝ) := by
  rw [full_modulus_l1Phi_eq hd]
  exact div_le_div_of_nonneg_right (l1Phi_le_eulerProduct N cap w Z L d) (Nat.cast_nonneg _)

/-- A single absolute constant works for all even targets, caps, original
levels and rough states. Both reciprocal-totient norms are O(log w). -/
theorem exists_uniform_small_log_envelope :
    ∃ C : ℝ, 0 < C ∧ ∀ (N cap : ℕ), Even N → ∀ (w Z L : ℝ), 2 ≤ w → ∀ d : ℕ,
      l1Phi N cap w Z L d ≤ C * Real.log w ∧
      l2PhiSq N cap w Z L d ≤ C * Real.log w := by
  obtain ⟨K, hK, hinterval⟩ :=
    MathlibNt.SieveTheory.MertensTheorem.exists_goldbach_inverse_interval_bound
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hKpos : 0 < K := zero_lt_one.trans hK
  let C : ℝ := (1 + K / Real.log 2) / Real.log 2
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N cap hN w Z L hw d
  have hodd : ∀ p ∈ actualSmallPrimeFinset N cap w, Nat.Prime p ∧ 2 < p := by
    intro p hp
    exact roughPrimeFinset_odd_of_even hN hp
  have hbound := hinterval (actualSmallPrimeFinset N cap w) hodd 2 w (by norm_num) hw (by
    intro p hp
    exact ⟨by exact_mod_cast (hodd p hp).1.two_le,
      (mem_actualSmallPrimeFinset.mp hp).2.2.2⟩)
  have hmass : l1Phi N cap w Z L d ≤ C * Real.log w := by
    calc
      _ ≤ ∏ p ∈ actualSmallPrimeFinset N cap w, (1 + 1 / ((p : ℝ) - 1)) :=
        l1Phi_le_eulerProduct N cap w Z L d
      _ ≤ ∏ p ∈ actualSmallPrimeFinset N cap w, (1 - 1 / ((p : ℝ) - 1))⁻¹ :=
        roughPrime_eulerProduct_le_inverseProduct N cap 0 w hN
      _ ≤ Real.log w / Real.log 2 * (1 + K / Real.log 2) := hbound
      _ = C * Real.log w := by dsimp only [C]; ring
  exact ⟨hmass, by simpa only [l2PhiSq_eq_l1Phi] using hmass⟩

end
end ImbalancedChen.P5Z.OriginalConditionalBetaNorm
