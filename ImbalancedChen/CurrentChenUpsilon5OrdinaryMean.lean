import ImbalancedChen.CurrentChenPairDensity
import ImbalancedChen.CurrentChenPairMovingHarmonic
import ImbalancedChen.CurrentChenUpsilon5FiniteMean

/-!
# Actual fifth Chen counts with the ordinary Rosser density

The same row coefficient is summed over the actual strict pair selector.
Only its nonzero divisor rows enter the physical distribution cap. The
ordinary BV supplier and the complete centre cost are paid at that cap.
No selected prime-pair, pointwise sieve or analytic error bound is assumed.

The variable harmonic integral is supplied by the actual prime-box theorem
and compact uniform transport. The final theorem proves an ordinary fifth
mean without an analytic supplier premise. The manuscript's stronger causal
mean and the complete hLower remain separate obligations.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology
open scoped BigOperators
open Classical
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)
open MeasureTheory

/-- The actual same-coefficient density sum has the needed lower limit.
Only the proved analytic lower supplier is used; no two-sided density
convergence or finite odd-box reconstruction is needed. -/
theorem eventually_currentChenUpsilon5_ordinary_normalized_density_lower
    (B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      currentChenUpsilon5OrdinaryIntegral - epsilon ≤
        ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
          (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
            (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
              ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
                Real.log (N : ℝ) / singularSeries N) := by
  obtain ⟨M, hM, hmass⟩ := currentChenUpsilon5_reciprocalTotient_eventually_bounded
  let T := fun N : ℕ => chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
    ((N : ℝ) ^ (19 / 125 : ℝ))
  let w := fun (_N : ℕ) (t : ℕ × ℕ) => 1 / (Nat.totient (t.1 * t.2) : ℝ)
  let f := fun N (t : ℕ × ℕ) =>
    actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
      ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
        Real.log (N : ℝ) / singularSeries N
  let g := fun N (t : ℕ × ℕ) => currentChenUpsilon5OrdinaryFactor
    (chenQuotientRosserT B (417 / 5000) N (t.1 * t.2))
  let delta : ℝ := epsilon / (2 * (M + 1))
  have hden : 0 < 2 * (M + 1) := by linarith
  have hdeltap : 0 < delta := div_pos hepsilon hden
  have hcost : delta * M ≤ epsilon / 2 := by
    have h := mul_le_mul_of_nonneg_left (show M ≤ M + 1 by linarith) hdeltap.le
    have hid : delta * (M + 1) = epsilon / 2 := by
      dsimp [delta]
      field_simp [show M + 1 ≠ 0 by linarith]
    linarith only [h, hid]
  have hnear : ∀ᶠ N : ℕ in atTop,
      currentChenUpsilon5OrdinaryIntegral - epsilon / 2 <
        ∑ t ∈ T N, w N t * g N t :=
    (tendsto_currentChenUpsilon5_ordinary_moving_harmonic B).eventually
      (Ioi_mem_nhds (by linarith : currentChenUpsilon5OrdinaryIntegral - epsilon / 2 <
        currentChenUpsilon5OrdinaryIntegral))
  filter_upwards [hmass, hnear,
    eventually_currentChenUpsilon5_ordinary_row_density_lower B delta hdeltap]
    with N hmassN hnearN hrows
  intro hEven
  have hsum : (∑ t ∈ T N, w N t * g N t) - delta * (∑ t ∈ T N, w N t) ≤
      ∑ t ∈ T N, w N t * f N t := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have h := mul_le_mul_of_nonneg_left (hrows hEven t ht)
      (show 0 ≤ w N t by dsimp [w]; positivity)
    change w N t * (g N t - delta) ≤ w N t * f N t at h
    nlinarith only [h]
  have hmasscost := (mul_le_mul_of_nonneg_left hmassN hdeltap.le).trans hcost
  change currentChenUpsilon5OrdinaryIntegral - epsilon ≤ ∑ t ∈ T N, w N t * f N t
  linarith only [hsum, hmasscost, hnearN]

/-- An unconditional ordinary lower mean for the literal current fifth
Chen row. The variable-profile integral, same actual Rosser coefficient,
physical BV support, and all errors are supplied by proved theorems.

This is one of the eleven actual means, not the manuscript's stronger
causal h248 estimate and not an assertion of the complete hLower. -/
theorem eventually_currentChenUpsilon5_ge_ordinary_mean
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      (currentChenUpsilon5OrdinaryIntegral - epsilon) * singularNormalization N ≤
        currentChenUpsilon5 N := by
  by_cases hI : 0 < currentChenUpsilon5OrdinaryIntegral
  · obtain ⟨B, _hB, hpaid⟩ := eventually_currentChenUpsilon5_ge_ordinary_density_sum
    let delta : ℝ := min (epsilon / 2) (currentChenUpsilon5OrdinaryIntegral / 2)
    have hdeltap : 0 < delta := lt_min (half_pos hepsilon) (half_pos hI)
    have hdeltae : delta ≤ epsilon / 2 := min_le_left _ _
    have hdeltaI : delta ≤ currentChenUpsilon5OrdinaryIntegral / 2 := min_le_right _ _
    have hnear : ∀ᶠ N : ℕ in atTop, Even N →
        currentChenUpsilon5OrdinaryIntegral - delta <
          ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
            ((N : ℝ) ^ (19 / 125 : ℝ)),
            (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
              (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
                ((N : ℝ) ^ (417 / 5000 : ℝ))
                  (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
                    Real.log (N : ℝ) / singularSeries N) := by
      filter_upwards [eventually_currentChenUpsilon5_ordinary_normalized_density_lower
        B (delta / 2) (half_pos hdeltap)] with N hlower
      intro hEven
      have h := hlower hEven
      linarith only [h, hdeltap]
    filter_upwards [hnear, hpaid (epsilon / 2) (half_pos hepsilon),
      eventually_ge_atTop (2 : ℕ)] with N hnearN hpaidN hN
    intro hEven
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNp : (0 : ℝ) < N := zero_lt_one.trans hN1
    have hlogp := Real.log_pos hN1
    have hSSp := singularSeries_pos N
    have hH : 0 ≤ singularNormalization N :=
      div_nonneg (mul_nonneg hSSp.le hNp.le) (sq_nonneg _)
    let V : ℝ := ∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
      ((N : ℝ) ^ (19 / 125 : ℝ)),
        actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
          ((N : ℝ) ^ (417 / 5000 : ℝ)) (chenQuotientRosserD B N (t.1 * t.2) : ℝ) /
            (Nat.totient (t.1 * t.2) : ℝ)
    have hvnorm : currentChenUpsilon5OrdinaryIntegral - delta ≤
        V * Real.log (N : ℝ) / singularSeries N := by
      have h := (hnearN hEven).le
      have heq : (∑ t ∈ chenY5PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ))
          ((N : ℝ) ^ (19 / 125 : ℝ)),
          (1 / (Nat.totient (t.1 * t.2) : ℝ)) *
            (actualSmallRosserMinusDensity N (Nat.ceil ((N : ℝ) ^ (417 / 5000 : ℝ)))
              ((N : ℝ) ^ (417 / 5000 : ℝ))
                (chenQuotientRosserD B N (t.1 * t.2) : ℝ) *
                  Real.log (N : ℝ) / singularSeries N)) =
            V * Real.log (N : ℝ) / singularSeries N := by
        dsimp [V]
        rw [Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      rwa [heq] at h
    have hv : 0 ≤ V := by
      have hn : 0 < V * Real.log (N : ℝ) / singularSeries N :=
        (show 0 < currentChenUpsilon5OrdinaryIntegral - delta by linarith).trans_le hvnorm
      have hm := (div_pos_iff_of_pos_right hSSp).mp hn
      exact ((mul_pos_iff_of_pos_right hlogp).mp hm).le
    have hli : (N : ℝ) / Real.log (N : ℝ) ≤ trueLogarithmicIntegral N :=
      MathlibNt.SieveTheory.LiuWeight.div_log_le_liuLogarithmicIntegral
        (by exact_mod_cast hN)
    have hmain : (currentChenUpsilon5OrdinaryIntegral - delta) *
        singularNormalization N ≤ currentChenUpsilon5OrdinaryDensitySum B N := by
      calc
        _ ≤ (V * Real.log (N : ℝ) / singularSeries N) * singularNormalization N :=
          mul_le_mul_of_nonneg_right hvnorm hH
        _ = ((N : ℝ) / Real.log (N : ℝ)) * V := by
          unfold singularNormalization
          field_simp [hSSp.ne', hlogp.ne']
          <;> ring
        _ ≤ trueLogarithmicIntegral N * V := mul_le_mul_of_nonneg_right hli hv
        _ = _ := by
          unfold currentChenUpsilon5OrdinaryDensitySum V
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring
    have hfinite := hpaidN hEven
    have hbudget := mul_le_mul_of_nonneg_right hdeltae hH
    nlinarith only [hmain, hfinite, hbudget]
  · apply Eventually.of_forall
    intro N hEven
    have hH : 0 ≤ singularNormalization N :=
      div_nonneg (mul_nonneg (singularSeries_pos N).le (Nat.cast_nonneg N)) (sq_nonneg _)
    have hc : currentChenUpsilon5OrdinaryIntegral - epsilon ≤ 0 := by linarith
    have hnonneg : 0 ≤ currentChenUpsilon5 N := by
      unfold currentChenUpsilon5
      exact Finset.sum_nonneg (fun P hP => Nat.cast_nonneg _)
    exact (mul_nonpos_of_nonpos_of_nonneg hc hH).trans hnonneg

end

end ImbalancedChen
