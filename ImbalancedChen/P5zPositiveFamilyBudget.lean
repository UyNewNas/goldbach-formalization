import ImbalancedChen.RealPhysicalUpperWeightBridge
import ImbalancedChen.ActualUpperDensityAssembly
import ImbalancedChen.Part3DistributionTargets

/-!
# Positive labelled-family finite U* budget, including J = 0

SOURCE ONLY / UNCOMPILED. Labels are never replaced by an unweighted
image of their products. The rho in every sum is literally the same.
No analytic licence, same-rho PP estimate or currentK density supplier
is asserted here. Those are explicit finite premises at their actual
objects, rather than a premise equivalent to the final U* upper bound.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

variable {α : Type*}

/-- The original labels retain repeated product representations. -/
def p5z_labelledMass (S : Finset α) (W : α → ℝ) : ℝ := ∑ t ∈ S, W t

def p5z_labelledPrimeMass (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N : ℕ) : ℝ :=
  ∑ t ∈ S, if f t < N ∧ Nat.Prime (N - f t) then W t else 0

/-- The exact small-prime partner mass, still with every original label. -/
def p5z_labelledSmallPrimeMass (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (N z : ℕ) : ℝ :=
  ∑ t ∈ S, if f t < N ∧ Nat.Prime (N - f t) ∧ N - f t < z then W t else 0

def p5z_labelledCongruenceMass (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (N q : ℕ) : ℝ :=
  ∑ t ∈ S, if Nat.ModEq q (f t) N then W t else 0

def p5z_labelledCoprimeMass (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (q : ℕ) : ℝ := ∑ t ∈ S, if Nat.Coprime (f t) q then W t else 0

/-- The correction from exact coprime mass to total positive source mass. -/
def p5z_labelledCoprimeCorrection (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q *
    ((p5z_labelledCoprimeMass S f W q - p5z_labelledMass S W) /
      (Nat.totient q : ℝ))

/-- The signed primitive discrepancy; absolute value is taken only after
summing every original label and every physical modulus. -/
def p5z_labelledDistributionError (S : Finset α) (f : α → ℕ) (W : α → ℝ)
    (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, rho q * (p5z_labelledCongruenceMass S f W N q -
    p5z_labelledCoprimeMass S f W q / (Nat.totient q : ℝ))

/-- Adaptation to the actual Part3 labelled prime-product signed error.
Repeated prime labels, slot order and exact coprime correction agree. -/
theorem p5z_labelledDistributionError_eq_primeProductSignedError
    (k P N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) :
    p5z_labelledDistributionError (Part3.labelledPrimeTuples k P)
        Part3.labelledProduct W N Q rho =
      Part3.primeProductSignedError k P N Q rho W := by
  classical
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass
    p5z_labelledCoprimeMass Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  simp_rw [mul_sub, ← mul_div_assoc, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_div]

/-- Label-preserving finite Fubini and recentering, with natural shifts
licensed on the entire source including its possible endpoint f(t)=N. -/
theorem p5z_labelled_physical_sum_eq_main_add_errors
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (hSN : ∀ t ∈ S, f t ≤ N) :
    (∑ t ∈ S, W t * physicalDivisorSum Q rho (N - f t)) =
      p5z_labelledMass S W * physicalDensitySum Q rho +
        p5z_labelledCoprimeCorrection S f W Q rho +
        p5z_labelledDistributionError S f W N Q rho := by
  classical
  have hFubini :
      (∑ t ∈ S, W t * physicalDivisorSum Q rho (N - f t)) =
        ∑ q ∈ Q, rho q * p5z_labelledCongruenceMass S f W N q := by
    unfold physicalDivisorSum
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    unfold p5z_labelledCongruenceMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hi : q ∣ N - f t ↔ Nat.ModEq q (f t) N :=
      dvd_sub_iff_modEq_of_le (hSN t ht)
    by_cases hmod : Nat.ModEq q (f t) N
    · simp only [if_pos (hi.mpr hmod), if_pos hmod, mul_comm]
    · have hnot : ¬ q ∣ N - f t := fun h => hmod (hi.mp h)
      simp only [if_neg hnot, if_neg hmod, mul_zero]
  rw [hFubini]
  unfold physicalDensitySum p5z_labelledCoprimeCorrection p5z_labelledDistributionError
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

/-- Positive family sieve comparison with the exact small-prime loss.
No injectivity of the product map is required. -/
theorem p5z_labelledPrimeMass_le_main_add_errors
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N z : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hW : ∀ t ∈ S, 0 ≤ W t) (hSN : ∀ t ∈ S, f t ≤ N)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n) :
    p5z_labelledPrimeMass S f W N ≤
      p5z_labelledMass S W * physicalDensitySum Q rho +
        p5z_labelledCoprimeCorrection S f W Q rho +
        p5z_labelledDistributionError S f W N Q rho +
        p5z_labelledSmallPrimeMass S f W N z := by
  classical
  have hnonneg (n : ℕ) : 0 ≤ physicalDivisorSum Q rho n := by
    have h := hmajor n
    split_ifs at h <;> linarith
  have hpoint : p5z_labelledPrimeMass S f W N ≤
      (∑ t ∈ S, W t * physicalDivisorSum Q rho (N - f t)) +
        p5z_labelledSmallPrimeMass S f W N z := by
    unfold p5z_labelledPrimeMass p5z_labelledSmallPrimeMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hg : f t < N ∧ Nat.Prime (N - f t)
    · by_cases hs : N - f t < z
      · have hproduct := mul_nonneg (hW t ht) (hnonneg (N - f t))
        simp only [if_pos hg, if_pos ⟨hg.1, hg.2, hs⟩]
        linarith
      · have hcop := prime_coprime_sieveProduct_of_cap_le hg.2 (Nat.le_of_not_gt hs)
        have hD : 1 ≤ physicalDivisorSum Q rho (N - f t) := by
          simpa only [if_pos hcop] using hmajor (N - f t)
        have hmul := mul_le_mul_of_nonneg_left hD (hW t ht)
        have hnot : ¬ (f t < N ∧ Nat.Prime (N - f t) ∧ N - f t < z) :=
          fun h => hs h.2.2
        simpa only [if_pos hg, if_neg hnot, add_zero, mul_one] using hmul
    · have hnot : ¬ (f t < N ∧ Nat.Prime (N - f t) ∧ N - f t < z) :=
        fun h => hg ⟨h.1, h.2.1⟩
      simp only [if_neg hg, if_neg hnot, add_zero]
      exact mul_nonneg (hW t ht) (hnonneg (N - f t))
  rw [p5z_labelled_physical_sum_eq_main_add_errors S f W N Q rho hSN] at hpoint
  exact hpoint

/-- A tolerance common to source mass, density and three finite errors.
The denominator is positive even when J = 0; J is never inverted. -/
theorem p5z_positive_family_budget_exists {J eta : ℝ}
    (hJ : 0 ≤ J) (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      (J + delta) * (currentK + delta) + 3 * delta ≤ currentK * J + eta := by
  have hK : 0 < currentK := by norm_num [currentK]
  let D := currentK + J + 4
  have hD : 0 < D := by dsimp [D]; linarith
  let delta := min 1 (eta / D)
  have hd : 0 < delta := lt_min zero_lt_one (div_pos heta hD)
  have hd1 : delta ≤ 1 := min_le_left _ _
  have hbudget : delta * D ≤ eta := (le_div_iff₀ hD).mp (min_le_right _ _)
  have hsquare : delta * delta ≤ delta := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 hd.le
  refine ⟨delta, hd, hd1, ?_⟩
  dsimp [D] at hbudget
  nlinarith only [hbudget, hsquare]

/-- The zero-source-mass coefficient case has the SAME positive tolerance
construction. Its denominator is currentK+4, never the vanishing J. -/
theorem p5z_positive_family_zero_mass_budget_exists {eta : ℝ}
    (heta : 0 < eta) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      delta * (currentK + delta) + 3 * delta ≤ eta := by
  simpa only [zero_add, mul_zero] using
    (p5z_positive_family_budget_exists (J := 0) (by norm_num) heta)
/-- Finite U* budget for an actual labelled positive family. Both mass and
density tolerances are retained multiplicatively. All three error bounds
refer to the exact same source and rho. This covers J=0 without a limit
argument or any division by J. -/
theorem p5z_labelled_positive_family_currentK_upper
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N z : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (J delta eta : ℝ)
    (hN : 2 ≤ N) (hJ : 0 ≤ J) (hdelta : 0 ≤ delta)
    (hbudget : (J + delta) * (currentK + delta) + 3 * delta ≤ currentK * J + eta)
    (hW : ∀ t ∈ S, 0 ≤ W t) (hSN : ∀ t ∈ S, f t ≤ N)
    (hmajor : ∀ n : ℕ,
      (if Nat.Coprime n (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho n)
    (hmass : p5z_labelledMass S W ≤
      (J + delta) * ((N : ℝ) / Real.log (N : ℝ)))
    (hdensity : physicalDensitySum Q rho ≤
      (currentK + delta) * (singularSeries N / Real.log (N : ℝ)))
    (hcop : |p5z_labelledCoprimeCorrection S f W Q rho| ≤ delta * singularNormalization N)
    (hPP : |p5z_labelledDistributionError S f W N Q rho| ≤ delta * singularNormalization N)
    (hsmall : p5z_labelledSmallPrimeMass S f W N z ≤ delta * singularNormalization N) :
    p5z_labelledPrimeMass S f W N ≤ (currentK * J + eta) * singularNormalization N := by
  have hK : 0 ≤ currentK := by norm_num [currentK]
  have hmass0 : 0 ≤ p5z_labelledMass S W := Finset.sum_nonneg fun t ht => hW t ht
  have hscale := (densityScale_pos hN).le
  have hH : 0 ≤ singularNormalization N :=
    div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have hmain : p5z_labelledMass S W * physicalDensitySum Q rho ≤
      ((J + delta) * (currentK + delta)) * singularNormalization N := by
    calc
      _ ≤ p5z_labelledMass S W *
          ((currentK + delta) * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_left hdensity hmass0
      _ ≤ ((J + delta) * ((N : ℝ) / Real.log (N : ℝ))) *
          ((currentK + delta) * (singularSeries N / Real.log (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hmass (mul_nonneg (add_nonneg hK hdelta) hscale)
      _ = ((J + delta) * (currentK + delta)) * singularNormalization N := by
        rw [← sourceMassScale_mul_densityScale N]
        ring
  have hc := (le_abs_self (p5z_labelledCoprimeCorrection S f W Q rho)).trans hcop
  have hp := (le_abs_self (p5z_labelledDistributionError S f W N Q rho)).trans hPP
  have hf := p5z_labelledPrimeMass_le_main_add_errors S f W N z Q rho hW hSN hmajor
  have hbudgetH := mul_le_mul_of_nonneg_right hbudget hH
  nlinarith only [hf, hmain, hc, hp, hsmall, hbudgetH]

end

end ImbalancedChen


