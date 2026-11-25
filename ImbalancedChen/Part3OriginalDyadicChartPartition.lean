import ImbalancedChen.Part3DistributionTargets
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Exact original-group dyadic partition

The smooth difference of two neighboring cutoffs telescopes on a finite
dyadic range. Applying the identity in each labelled prime coordinate
splits the actual signed discrepancy before any Heath--Brown expansion.
-/

namespace ImbalancedChen.Part3

noncomputable section
open Classical Finset
open scoped BigOperators ContDiff

/-- The original-group dyadic window, sampled before the HB expansion. -/
def originalDyadicWindow (χ : ℝ → ℝ) (j : ℤ) (x : ℝ) : ℝ :=
  χ (x / (2 : ℝ)^j) - χ (2 * x / (2 : ℝ)^j)

theorem originalDyadicWindow_contDiff (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (j : ℤ) : ContDiff ℝ ∞ (originalDyadicWindow χ j) := by
  exact (hχ.comp (contDiff_id.div_const _)).sub
    (hχ.comp ((contDiff_const.mul contDiff_id).div_const _))

theorem originalDyadicWindow_support (χ : ℝ → ℝ) (j : ℤ) (x : ℝ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hx : originalDyadicWindow χ j x ≠ 0) :
    1 / 2 < x / (2 : ℝ)^j ∧ x / (2 : ℝ)^j < 2 := by
  have hscale : 2 * x / (2 : ℝ)^j = 2 * (x / (2 : ℝ)^j) := by ring
  constructor
  · by_contra! h
    have hsmall : x / (2 : ℝ)^j ≤ 1 := by linarith
    have hsmall' : 2 * x / (2 : ℝ)^j ≤ 1 := by rw [hscale]; linarith
    exact hx (by rw [originalDyadicWindow, χlo _ hsmall, χlo _ hsmall', sub_self])
  · by_contra! h
    have hlarge : 2 ≤ 2 * x / (2 : ℝ)^j := by rw [hscale]; linarith
    exact hx (by rw [originalDyadicWindow, χhi _ h, χhi _ hlarge, sub_self])

theorem originalDyadicWindow_nonneg (χ : ℝ → ℝ) (hχ : Antitone χ)
    (j : ℤ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ originalDyadicWindow χ j x := by
  exact sub_nonneg.mpr (hχ (div_le_div_of_nonneg_right (by linarith) (by positivity)))

theorem originalDyadicWindow_sum (χ : ℝ → ℝ) (L : ℤ) (H : ℕ) (x : ℝ) :
    (∑ j ∈ range H, originalDyadicWindow χ (L + (j : ℤ)) x) =
      χ (x / (2 : ℝ)^(L - 1 + (H : ℤ))) - χ (x / (2 : ℝ)^(L - 1)) := by
  let f (i : ℕ) := χ (x / (2 : ℝ)^(L - 1 + (i : ℤ)))
  have hwin (j : ℕ) : originalDyadicWindow χ (L + (j : ℤ)) x = f (j + 1) - f j := by
    unfold originalDyadicWindow f
    have hj : L - 1 + ((j + 1 : ℕ) : ℤ) = L + (j : ℤ) := by omega
    have hi : L - 1 + (j : ℤ) = L + (j : ℤ) - 1 := by omega
    rw [hj, hi, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, div_div_eq_mul_div,
      mul_comm x 2]
  simpa only [hwin, f, Nat.cast_zero, add_zero] using Finset.sum_range_sub f H

theorem originalDyadicWindow_sum_eq_one (χ : ℝ → ℝ) (L : ℤ) (H : ℕ) (x : ℝ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hxlo : 2 ≤ x / (2 : ℝ)^(L - 1))
    (hxhi : x / (2 : ℝ)^(L - 1 + (H : ℤ)) ≤ 1) :
    (∑ j ∈ range H, originalDyadicWindow χ (L + (j : ℤ)) x) = 1 := by
  rw [originalDyadicWindow_sum, χlo _ hxhi, χhi _ hxlo, sub_zero]

/-- A chart contributes one original window for each labelled prime. -/
def originalDyadicChartWeight {k P : ℕ} (χ : ℝ → ℝ) (L : ℤ)
    (j : Fin k → ℕ) (p : Fin k → Fin (P + 1)) : ℝ :=
  ∏ i, originalDyadicWindow χ (L + (j i : ℤ)) ((p i).val : ℝ)

theorem originalDyadicChartWeight_sum_eq_one
    {k P : ℕ} (χ : ℝ → ℝ) (L : ℤ) (H : ℕ) (p : Fin k → Fin (P + 1))
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hpLo : ∀ i : Fin k, 2 ≤ ((p i).val : ℝ) / (2 : ℝ)^(L - 1))
    (hpHi : ∀ i : Fin k, ((p i).val : ℝ) / (2 : ℝ)^(L - 1 + (H : ℤ)) ≤ 1) :
    (∑ j ∈ Fintype.piFinset (fun _ : Fin k => range H), originalDyadicChartWeight χ L j p) = 1 := by
  unfold originalDyadicChartWeight
  rw [Finset.sum_prod_piFinset (range H) (fun (i : Fin k) (j : ℕ) =>
    originalDyadicWindow χ (L + (j : ℤ)) ((p i).val : ℝ))]
  exact Finset.prod_eq_one fun i _ =>
    originalDyadicWindow_sum_eq_one χ L H ((p i).val : ℝ) χlo χhi (hpLo i) (hpHi i)

/-- Insert the actual smooth original-group windows into the literal
signed prime-product discrepancy. No modulus-dependent chart is used. -/
theorem primeProductSignedError_eq_sum_originalDyadicCharts
    (k P N : ℕ) (Q : Finset ℕ) (ρ : ℕ → ℝ)
    (W : (Fin k → Fin (P + 1)) → ℝ) (χ : ℝ → ℝ) (L : ℤ) (H : ℕ)
    (χlo : ∀ s ≤ 1, χ s = 1) (χhi : ∀ s ≥ 2, χ s = 0)
    (hlo : ∀ p ∈ labelledPrimeTuples k P, W p ≠ 0 → ∀ i : Fin k,
      2 ≤ ((p i).val : ℝ) / (2 : ℝ)^(L - 1))
    (hhi : ∀ p ∈ labelledPrimeTuples k P, W p ≠ 0 → ∀ i : Fin k,
      ((p i).val : ℝ) / (2 : ℝ)^(L - 1 + (H : ℤ)) ≤ 1) :
    primeProductSignedError k P N Q ρ W =
      ∑ j ∈ Fintype.piFinset (fun _ : Fin k => range H),
        primeProductSignedError k P N Q ρ (fun p => W p * originalDyadicChartWeight χ L j p) := by
  let S := labelledPrimeTuples k P
  let J := Fintype.piFinset (fun _ : Fin k => range H)
  let K (q : ℕ) (p : Fin k → Fin (P + 1)) : ℝ :=
    (if Nat.ModEq q (labelledProduct p) N then 1 else 0) -
      (if Nat.Coprime (labelledProduct p) q then 1 else 0) / (q.totient : ℝ)
  have hW (p) (hp : p ∈ S) : W p = ∑ j ∈ J, W p * originalDyadicChartWeight χ L j p := by
    by_cases hw : W p = 0
    · simp [hw]
    · rw [← mul_sum, originalDyadicChartWeight_sum_eq_one χ L H p χlo χhi
        (hlo p hp hw) (hhi p hp hw), mul_one]
  change (∑ q ∈ Q, ρ q * ∑ p ∈ S, W p * K q p) =
    ∑ j ∈ J, ∑ q ∈ Q, ρ q *
      ∑ p ∈ S, (W p * originalDyadicChartWeight χ L j p) * K q p
  rw [sum_comm]
  apply sum_congr rfl
  intro q _
  rw [← mul_sum]
  congr 1
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  exact (congrArg (fun v => v * K q p) (hW p hp)).trans (sum_mul _ _ _)

end

end ImbalancedChen.Part3
