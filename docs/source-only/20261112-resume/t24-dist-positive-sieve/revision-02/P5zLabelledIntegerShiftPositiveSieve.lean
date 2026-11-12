import ImbalancedChen.P4BIntegerShiftOuterCarrier
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity

/-!
SOURCE ONLY / YELLOW / UNCOMPILED.

Finite labelled positive-sieve bridge on the complete outer carrier.
The shift is the existing integer natAbs shift; no product <= N premise
is imposed. Every mean and signed error uses the literal same Q and rho.
This supplies no density, smoothness, coprime budget or signed PP estimate.
-/
namespace ImbalancedChen.P5zLabelledIntegerShiftPositiveSieve

noncomputable section
open scoped BigOperators
open Classical

variable {α : Type*}

/-- Full-label Fubini. The old all-integer divisor/residue equivalence
is reused, including negative differences, zero difference and modulus zero. -/
theorem physical_sum_eq_congruence
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ t ∈ S, W t * physicalDivisorSum Q rho
      (((N : ℤ) - (f t : ℤ)).natAbs)) =
      ∑ q ∈ Q, rho q * p5z_labelledCongruenceMass S f W N q := by
  unfold physicalDivisorSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _hq
  unfold p5z_labelledCongruenceMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _ht
  have hi := P4B.integerShiftNatAbs_dvd_iff_modEq N (f t) q
  by_cases hmod : Nat.ModEq q (f t) N
  · simp only [if_pos (hi.mpr hmod), if_pos hmod, mul_comm]
  · have hnot : ¬q ∣ (((N : ℤ) - (f t : ℤ)).natAbs) := fun h => hmod (hi.mp h)
    simp only [if_neg hnot, if_neg hmod, mul_zero]

/-- Exact coprime mean plus the original whole signed distribution error.
No positivity of individual modulus coefficients is required. -/
theorem physical_sum_eq_exact_coprime_mean_add_error
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ t ∈ S, W t * physicalDivisorSum Q rho
      (((N : ℤ) - (f t : ℤ)).natAbs)) =
      (∑ q ∈ Q, rho q *
        (p5z_labelledCoprimeMass S f W q / (Nat.totient q : ℝ))) +
      p5z_labelledDistributionError S f W N Q rho := by
  rw [physical_sum_eq_congruence]
  unfold p5z_labelledDistributionError
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- Recenter the same exact mean at full positive source mass. -/
theorem physical_sum_eq_main_add_errors
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ t ∈ S, W t * physicalDivisorSum Q rho
      (((N : ℤ) - (f t : ℤ)).natAbs)) =
      p5z_labelledMass S W * physicalDensitySum Q rho +
        p5z_labelledCoprimeCorrection S f W Q rho +
        p5z_labelledDistributionError S f W N Q rho := by
  rw [physical_sum_eq_congruence]
  unfold physicalDensitySum p5z_labelledCoprimeCorrection p5z_labelledDistributionError
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  ring

/-- Prime tests are zero when f(t) >= N, while the complete outer
divisor polynomial is nonnegative there. Only a true prime-test branch
uses f(t) < N to identify integer natAbs with the old natural shift. -/
theorem primeMass_le_main_add_errors
    (S : Finset α) (f : α → ℕ) (W : α → ℝ) (N z : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (hW : ∀ t ∈ S, 0 ≤ W t)
    (hmajor : ∀ x : ℕ,
      (if Nat.Coprime x (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho x) :
    p5z_labelledPrimeMass S f W N ≤
      p5z_labelledMass S W * physicalDensitySum Q rho +
        p5z_labelledCoprimeCorrection S f W Q rho +
        p5z_labelledDistributionError S f W N Q rho +
        p5z_labelledSmallPrimeMass S f W N z := by
  have hnonneg (x : ℕ) : 0 ≤ physicalDivisorSum Q rho x := by
    have h := hmajor x
    split_ifs at h <;> linarith
  have hpoint : p5z_labelledPrimeMass S f W N ≤
      (∑ t ∈ S, W t * physicalDivisorSum Q rho
        (((N : ℤ) - (f t : ℤ)).natAbs)) +
        p5z_labelledSmallPrimeMass S f W N z := by
    unfold p5z_labelledPrimeMass p5z_labelledSmallPrimeMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hg : f t < N ∧ Nat.Prime (N - f t)
    · rw [P4B.integerShiftNatAbs_eq_natSub_of_le hg.1.le]
      by_cases hs : N - f t < z
      · have hp := mul_nonneg (hW t ht) (hnonneg (N - f t))
        simp only [if_pos hg, if_pos ⟨hg.1, hg.2, hs⟩]
        linarith
      · have hcop := prime_coprime_sieveProduct_of_cap_le hg.2 (Nat.le_of_not_gt hs)
        have hD : 1 ≤ physicalDivisorSum Q rho (N - f t) := by
          simpa only [if_pos hcop] using hmajor (N - f t)
        have hmul := mul_le_mul_of_nonneg_left hD (hW t ht)
        have hnot : ¬(f t < N ∧ Nat.Prime (N - f t) ∧ N - f t < z) :=
          fun h => hs h.2.2
        simpa only [if_pos hg, if_neg hnot, add_zero, mul_one] using hmul
    · have hnot : ¬(f t < N ∧ Nat.Prime (N - f t) ∧ N - f t < z) :=
        fun h => hg ⟨h.1, h.2.1⟩
      simp only [if_neg hg, if_neg hnot, add_zero]
      exact mul_nonneg (hW t ht) (hnonneg _)
  rw [physical_sum_eq_main_add_errors] at hpoint
  exact hpoint

/-- The tuple cap P and prime-test target N are independent. The only
filtered family here is the genuine small-prime-test support, for its
local fee; neither the mean nor the PP weight is filtered. -/
theorem smallPrimeMass_le {k P : ℕ}
    (S : Finset (Fin k → Fin (P + 1)))
    (hS : S ⊆ Part3.labelledPrimeTuples k P)
    (W : (Fin k → Fin (P + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ t ∈ S, W t ≤ B) (N z : ℕ) :
    p5z_labelledSmallPrimeMass S Part3.labelledProduct W N z ≤
      B * (k ^ k : ℕ) * (z : ℝ) := by
  let T := S.filter (fun t => Part3.labelledProduct t < N ∧
    Nat.Prime (N - Part3.labelledProduct t) ∧ N - Part3.labelledProduct t < z)
  let g := fun t : Fin k → Fin (P + 1) => N - Part3.labelledProduct t
  have hmaps : ∀ t ∈ T, g t ∈ Finset.range z := by
    intro t ht
    exact Finset.mem_range.mpr (Finset.mem_filter.mp ht).2.2.2
  have hf := Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range z)
    (g := g) hmaps W
  have heq : (∑ t ∈ T, W t) =
      p5z_labelledSmallPrimeMass S Part3.labelledProduct W N z := by
    exact Finset.sum_filter (s := S) (fun t => Part3.labelledProduct t < N ∧
      Nat.Prime (N - Part3.labelledProduct t) ∧ N - Part3.labelledProduct t < z) W
  rw [← heq, ← hf]
  calc
    _ ≤ ∑ _p ∈ Finset.range z, B * (k ^ k : ℕ) := by
      apply Finset.sum_le_sum
      intro p _hp
      have hsub : T.filter (fun t => g t = p) ⊆
          S.filter (fun t => Part3.labelledProduct t = N - p) := by
        intro t ht
        obtain ⟨htT, htp⟩ := Finset.mem_filter.mp ht
        obtain ⟨htS, htN, _hprime, _hz⟩ := Finset.mem_filter.mp htT
        apply Finset.mem_filter.mpr
        refine ⟨htS, ?_⟩
        dsimp only [g] at htp
        omega
      have hcard : ((T.filter (fun t => g t = p)).card : ℝ) ≤ (k ^ k : ℕ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans
          (p5z_marked_prime_product_fibre_card_le S hS (N - p))
      calc
        _ ≤ ∑ _t ∈ T.filter (fun t => g t = p), B :=
          Finset.sum_le_sum (fun t ht => hW t
            (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1)
        _ = B * ((T.filter (fun t => g t = p)).card : ℝ) := by simp; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hcard hB
    _ = _ := by simp; ring

/-- Every finite occurrence sum has the exact same main/error identity,
even when its occurrence coefficients and labelled weights have both
signs. This is an equality; it grants no upper bound after a negative
occurrence coefficient multiplies a one-sided sieve inequality. -/
theorem sum_physical_eq_main_add_errors
    {ι : Type*} {A : ι → Type*} (I : Finset ι) (a : ι → ℝ)
    (S : (i : ι) → Finset (A i)) (f : (i : ι) → A i → ℕ)
    (W : (i : ι) → A i → ℝ) (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ i ∈ I, a i * (∑ t ∈ S i, W i t * physicalDivisorSum Q rho
      (((N : ℤ) - (f i t : ℤ)).natAbs))) =
      (∑ i ∈ I, a i * p5z_labelledMass (S i) (W i)) * physicalDensitySum Q rho +
      (∑ i ∈ I, a i * p5z_labelledCoprimeCorrection (S i) (f i) (W i) Q rho) +
      (∑ i ∈ I, a i * p5z_labelledDistributionError (S i) (f i) (W i) N Q rho) := by
  simp_rw [physical_sum_eq_main_add_errors, mul_add, ← mul_assoc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul]

/-- Finite nonnegative occurrence coefficients may be assembled before
any signed-error bound. Branch types may depend on the occurrence, so
different ranks and every original repeated word are retained. -/
theorem sum_primeMass_le_main_add_errors
    {ι : Type*} {A : ι → Type*} (I : Finset ι) (a : ι → ℝ)
    (S : (i : ι) → Finset (A i)) (f : (i : ι) → A i → ℕ)
    (W : (i : ι) → A i → ℝ) (N z : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hW : ∀ i ∈ I, ∀ t ∈ S i, 0 ≤ W i t)
    (hmajor : ∀ x : ℕ,
      (if Nat.Coprime x (sieveProduct N z) then (1 : ℝ) else 0) ≤
        physicalDivisorSum Q rho x) :
    (∑ i ∈ I, a i * p5z_labelledPrimeMass (S i) (f i) (W i) N) ≤
      (∑ i ∈ I, a i * p5z_labelledMass (S i) (W i)) * physicalDensitySum Q rho +
      (∑ i ∈ I, a i * p5z_labelledCoprimeCorrection (S i) (f i) (W i) Q rho) +
      (∑ i ∈ I, a i * p5z_labelledDistributionError (S i) (f i) (W i) N Q rho) +
      (∑ i ∈ I, a i * p5z_labelledSmallPrimeMass (S i) (f i) (W i) N z) := by
  calc
    _ ≤ ∑ i ∈ I, a i *
        (p5z_labelledMass (S i) (W i) * physicalDensitySum Q rho +
          p5z_labelledCoprimeCorrection (S i) (f i) (W i) Q rho +
          p5z_labelledDistributionError (S i) (f i) (W i) N Q rho +
          p5z_labelledSmallPrimeMass (S i) (f i) (W i) N z) :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
        (primeMass_le_main_add_errors (S i) (f i) (W i) N z Q rho (hW i hi) hmajor)
        (ha i hi))
    _ = _ := by
      simp_rw [mul_add, ← mul_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul]

end
end ImbalancedChen.P5zLabelledIntegerShiftPositiveSieve
