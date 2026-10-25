import ImbalancedChen.P1OriginalFourthReciprocalBinRegrouping

/-!
# Finite summation of the original coarse fourth reciprocal-bin budget

The moving prime-interval estimate has a main term `2a/r²` and a uniform
error `6K/log N` per occupied natural reciprocal index. This module sums
those two terms over the actual original-policy occupied index set. The
terminal prime is at least three for even targets, so the index count is
bounded by `a log N/log 3 + 1`. No unproved prime distribution input is
needed for this finite summation. Source-only/uncompiled.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators
open Finset
open P1OriginalCoarseContinuation
open P1OriginalFourthSmallPrimeStratification
open P1OriginalFourthReciprocalBinRegrouping

namespace P1OriginalFourthFiniteBinBudget

/-- The elementary reciprocal-square telescope on a finite positive
integer interval. -/
private theorem sum_inv_sq_Icc_one_le (M : ℕ) :
    (∑ r ∈ Icc 1 M, ((r : ℝ)⁻¹) ^ 2) ≤ 2 := by
  by_cases hM : 1 ≤ M
  · calc
      _ ≤ ∑ r ∈ Icc 1 M,
            2 * ((r : ℝ)⁻¹ - ((r : ℝ) + 1)⁻¹) := by
        apply sum_le_sum
        intro r hr
        have hr0 : (0 : ℝ) < r := by
          exact_mod_cast (mem_Icc.mp hr).1
        have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
        calc
          _ = 1 / (r : ℝ) ^ 2 := by simp only [one_div, inv_pow]
          _ ≤ 2 / ((r : ℝ) * ((r : ℝ) + 1)) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos hr0) (mul_pos hr0 hr1)).mpr
            have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast (mem_Icc.mp hr).1
            nlinarith
          _ = _ := by field_simp; ring
      _ = 2 * ((1 : ℝ)⁻¹ - ((M : ℝ) + 1)⁻¹) := by
        rw [← mul_sum]
        congr 1
        have ht := sum_Icc_sub hM (fun r : ℕ => (r : ℝ)⁻¹)
        simp only [Nat.cast_add, Nat.cast_one] at ht
        have hneg :
            (∑ r ∈ Icc 1 M, (((r : ℝ) + 1)⁻¹ - (r : ℝ)⁻¹)) =
              -(∑ r ∈ Icc 1 M, ((r : ℝ)⁻¹ - ((r : ℝ) + 1)⁻¹)) := by
          rw [← sum_neg_distrib]
          apply sum_congr rfl
          intro r _
          ring
        linarith
      _ ≤ 2 := by
        have hpos : 0 ≤ ((M : ℝ) + 1)⁻¹ := inv_nonneg.mpr (by positivity)
        nlinarith
  · have hempty : Icc 1 M = ∅ := Icc_eq_empty_of_lt (Nat.lt_of_not_ge hM)
    simp only [hempty, sum_empty]
    norm_num

/-- Any finite set of distinct positive indices below a real ceiling has
bounded second inverse moment and bounded cardinality. -/
private theorem finite_index_terms_le
    (R : Finset ℕ) (T a K L : ℝ)
    (hT : 0 ≤ T) (ha : 0 ≤ a) (hK : 0 ≤ K) (hL : 0 < L)
    (hR : ∀ r ∈ R, 1 ≤ r ∧ (r : ℝ) ≤ T) :
    (∑ r ∈ R, 2 * a * ((r : ℝ)⁻¹) ^ 2 + 6 * K / L) ≤
      4 * a + (T + 1) * (6 * K / L) := by
  have hsubI : R ⊆ Icc 1 (Nat.floor T) := by
    intro r hr
    exact mem_Icc.mpr ⟨(hR r hr).1,
      (Nat.le_floor_iff hT).mpr (hR r hr).2⟩
  have hsubRange : R ⊆ range (Nat.floor T + 1) := by
    intro r hr
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp (hsubI hr)).2)
  have hsquares : (∑ r ∈ R, ((r : ℝ)⁻¹) ^ 2) ≤ 2 := by
    calc
      _ ≤ ∑ r ∈ Icc 1 (Nat.floor T), ((r : ℝ)⁻¹) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg hsubI (fun _ _ _ => sq_nonneg _)
      _ ≤ 2 := sum_inv_sq_Icc_one_le _
  have hcardNat : R.card ≤ Nat.floor T + 1 := by
    calc
      R.card ≤ (range (Nat.floor T + 1)).card := card_le_card hsubRange
      _ = Nat.floor T + 1 := card_range _
  have hfloor : (Nat.floor T : ℝ) ≤ T := Nat.floor_le hT
  have hcard : (R.card : ℝ) ≤ T + 1 := by
    have hcardR : (R.card : ℝ) ≤ (Nat.floor T : ℝ) + 1 := by
      exact_mod_cast hcardNat
    exact hcardR.trans (add_le_add_right hfloor 1)
  have hmain : 2 * a * (∑ r ∈ R, ((r : ℝ)⁻¹) ^ 2) ≤ 4 * a := by
    nlinarith [mul_le_mul_of_nonneg_left hsquares (by positivity : 0 ≤ 2 * a)]
  have herr : (R.card : ℝ) * (6 * K / L) ≤ (T + 1) * (6 * K / L) :=
    mul_le_mul_of_nonneg_right hcard (by positivity)
  calc
    (∑ r ∈ R, 2 * a * ((r : ℝ)⁻¹) ^ 2 + 6 * K / L) =
        2 * a * (∑ r ∈ R, ((r : ℝ)⁻¹) ^ 2) +
          (R.card : ℝ) * (6 * K / L) := by
      rw [sum_add_distrib, ← mul_sum]
      simp only [sum_const_zero, sum_const, nsmul_eq_mul]
    _ ≤ 4 * a + (T + 1) * (6 * K / L) := add_le_add hmain herr

/-- The original coarse-policy occupied natural indices are positive and
lie below `a log N/log 3`. This uses the actual source, not a box index
invented after the fact. -/
theorem occupied_reciprocal_indices_range
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (j : FourthCell m) :
    ∀ r ∈ reciprocalBins (smallCellTuples e chi m omega a N cap j) a N,
      1 ≤ r ∧ (r : ℝ) ≤ a * Real.log (N : ℝ) / Real.log 3 := by
  intro r hr
  obtain ⟨p, hpS, howner⟩ := Finset.mem_image.mp hr
  have hp : p ∈ reciprocalBin (smallCellTuples e chi m omega a N cap j) a N r :=
    Finset.mem_filter.mpr ⟨hpS, howner⟩
  let k : Bin := (r, ⌊residualS 0 N p⌋, ⌊residualS 0 N p⌋)
  have hfine : p ∈ sourceBin (smallCellTuples e chi m omega a N cap j)
      a 0 0 N k := by
    apply Finset.mem_filter.mpr
    refine ⟨hpS, ?_⟩
    change (reciprocalOwner a N p, ⌊residualS 0 N p⌋,
      ⌊residualS 0 N p⌋) = k
    rw [howner]
  exact ⟨(smallBin_cutoffs e chi m omega a 0 0 ha N cap hN j k p hfine).1,
    occupied_reciprocal_index_le_log3 e chi m omega a ha N cap hN hEven j r p hp⟩

/-- A single explicit logarithmic-size condition discharges the lower
endpoint `N^(a/(r+1)) ≥ 2` for *every* occupied original bin. The gap
between the actual odd-prime floor three and the analytic floor two pays
the extra `+1` in the reciprocal-bin denominator. -/
theorem occupied_lower_endpoint_two_of_log_scale
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (j : FourthCell m)
    (hscale : Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤
      a * Real.log (N : ℝ) *
        (Real.log (3 : ℝ) - Real.log (2 : ℝ))) :
    ∀ r ∈ reciprocalBins (smallCellTuples e chi m omega a N cap j) a N,
      2 ≤ (N : ℝ) ^ (a / ((r : ℝ) + 1)) := by
  intro r hr
  have hbounds := occupied_reciprocal_indices_range e chi m omega a ha
    N cap hN hEven j r hr
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN
  have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hR : (r : ℝ) * Real.log (3 : ℝ) ≤ a * Real.log (N : ℝ) :=
    (le_div_iff₀ hlog3).mp hbounds.2
  have hmult := mul_le_mul_of_nonneg_right hR hlog2.le
  have htarget : ((r : ℝ) + 1) * Real.log (2 : ℝ) ≤
      a * Real.log (N : ℝ) := by
    nlinarith [hmult, hscale]
  have hlogtarget : Real.log (2 : ℝ) ≤
      (a / ((r : ℝ) + 1)) * Real.log (N : ℝ) := by
    have h := (le_div_iff₀ hr1).mpr htarget
    convert h using 1 <;> ring
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    (2 : ℝ) = Real.exp (Real.log (2 : ℝ)) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp ((a / ((r : ℝ) + 1)) * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr hlogtarget
    _ = (N : ℝ) ^ (a / ((r : ℝ) + 1)) := by
      rw [Real.rpow_def_of_pos hNpos]
      congr 1
      ring

/-- The occupied-index summation is explicit and uniform after the
moving prime-interval estimate: its result is `O(a + 1/log N)` with
constants independent of the target, cap, and selected fourth cell. -/
theorem original_occupied_interval_terms_le
    (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ) (ha : 0 < a)
    (N cap : ℕ) (hN : 1 < N) (hEven : Even N) (j : FourthCell m)
    (K : ℝ) (hK : 0 ≤ K) :
    (∑ r ∈ reciprocalBins (smallCellTuples e chi m omega a N cap j) a N,
      2 * a / (r : ℝ) ^ 2 + 6 * K / Real.log (N : ℝ)) ≤
        4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)) := by
  have hlogN : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hT : 0 ≤ a * Real.log (N : ℝ) / Real.log 3 := by positivity
  have h := finite_index_terms_le
    (reciprocalBins (smallCellTuples e chi m omega a N cap j) a N)
    (a * Real.log (N : ℝ) / Real.log 3) a K (Real.log (N : ℝ))
    hT ha.le hK hlogN
    (occupied_reciprocal_indices_range e chi m omega a ha N cap hN hEven j)
  have hright :
      4 * a + (a * Real.log (N : ℝ) / Real.log 3 + 1) *
        (6 * K / Real.log (N : ℝ)) =
      4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)) := by
    field_simp [hlogN.ne', hlog3.ne']
    ring
  rw [hright] at h
  simpa only [div_eq_mul_inv, inv_pow] using h

/-- The genuine target-deleted last-prime interval masses sum uniformly
over all occupied original indices. The sole remaining geometric endpoint
condition is displayed: every occupied box lower endpoint is at least two.
The same pinned K works before the source parameters are chosen. -/
theorem exists_original_occupied_last_prime_mass_le :
    ∃ K : ℝ, 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ), 0 < a →
      ∀ (N cap : ℕ), 1 < N → Even N → ∀ j : FourthCell m,
        (∀ r ∈ reciprocalBins (smallCellTuples e chi m omega a N cap j) a N,
          2 ≤ (N : ℝ) ^ (a / ((r : ℝ) + 1))) →
        (∑ r ∈ reciprocalBins (smallCellTuples e chi m omega a N cap j) a N,
          (a / (r : ℝ)) *
            actualPrimeReciprocalMass N (a / ((r : ℝ) + 1))
              (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1)))) ≤
          4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)) := by
  obtain ⟨K, hKpos, hinterval⟩ :=
    P1OriginalFourthMovingPrimeIntervalBound.exists_uniform_reciprocal_interval_bound
  refine ⟨K, hKpos, ?_⟩
  intro e chi m omega a ha N cap hN hEven j hlow
  have hterms := original_occupied_interval_terms_le e chi m omega a ha
    N cap hN hEven j K (by linarith)
  apply (Finset.sum_le_sum (fun r hr => ?_)).trans hterms
  have hr1 := (occupied_reciprocal_indices_range e chi m omega a ha
    N cap hN hEven j r hr).1
  exact P1OriginalFourthMovingPrimeIntervalBound.weighted_last_prime_interval_le_terms
    K (by linarith) hinterval N hN hEven a ha r hr1 (hlow r hr)

/-- Supplier-free terminal-prime sum with the explicit eventual scale
condition in place of a per-bin endpoint hypothesis. -/
theorem exists_original_occupied_last_prime_mass_le_of_log_scale :
    ∃ K : ℝ, 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ), 0 < a →
      ∀ (N cap : ℕ), 1 < N → Even N → ∀ j : FourthCell m,
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤
          a * Real.log (N : ℝ) *
            (Real.log (3 : ℝ) - Real.log (2 : ℝ)) →
        (∑ r ∈ reciprocalBins (smallCellTuples e chi m omega a N cap j) a N,
          (a / (r : ℝ)) *
            actualPrimeReciprocalMass N (a / ((r : ℝ) + 1))
              (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1)))) ≤
          4 * a + 6 * K * (a / Real.log 3 + 1 / Real.log (N : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := exists_original_occupied_last_prime_mass_le
  refine ⟨K, hK, ?_⟩
  intro e chi m omega a ha N cap hN hEven j hscale
  exact hbound e chi m omega a ha N cap hN hEven j
    (occupied_lower_endpoint_two_of_log_scale e chi m omega a ha
      N cap hN hEven j hscale)

/-- The box has three identical original `omega` to `19/96` factors and
the one moving last-prime factor. -/
private theorem original_bin_boxMass_eq_prefix_cube (N : ℕ) (omega a : ℝ) (r : ℕ) :
    actualPrimeBoxMass N (binLo omega a r) (binHi a r) =
      (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
        actualPrimeReciprocalMass N (a / ((r : ℝ) + 1))
          (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1))) := by
  rw [actualPrimeBoxMass_eq_prod]
  simp [Fin.prod_univ_four, binLo, binHi]
  ring

/-- The literal original-coarse Fin4 small-cell weighted first moment is
bounded by its fixed prefix-prime mass cubed times the explicit uniform
terminal-prime budget. No `hSupplier` or alternate fourth carrier occurs.
The logarithmic scale hypothesis is eventually true for each fixed a>0. -/
theorem exists_original_smallCell_weighted_moment_le :
    ∃ K : ℝ, 1 < K ∧
      ∀ (e : ℚ) (chi : ℝ) (m : ℕ) (omega a : ℝ), 0 < a →
      ∀ (J4 : Finset (FourthCell m)) (N cap : ℕ), 1 < N → Even N →
      ∀ (j : FourthCell m), j ∈ selectedFourthCells e chi m omega J4 →
        Real.log (2 : ℝ) * Real.log (3 : ℝ) ≤
          a * Real.log (N : ℝ) *
            (Real.log (3 : ℝ) - Real.log (2 : ℝ)) →
        (∑ p ∈ smallCellTuples e chi m omega a N cap j,
          (∏ i, 1 / ((p i : ℝ) - 1)) * actualPrimeTupleLog N p (Fin.last 3)) ≤
          (actualPrimeReciprocalMass N omega (19 / 96 : ℝ)) ^ 3 *
            (4 * a + 6 * K *
              (a / Real.log 3 + 1 / Real.log (N : ℝ))) := by
  obtain ⟨K, hK, hterminal⟩ := exists_original_occupied_last_prime_mass_le_of_log_scale
  refine ⟨K, hK, ?_⟩
  intro e chi m omega a ha J4 N cap hN hEven j hj hscale
  let S := smallCellTuples e chi m omega a N cap j
  let R := reciprocalBins S a N
  let M := actualPrimeReciprocalMass N omega (19 / 96 : ℝ)
  have hM : 0 ≤ M := by
    unfold M actualPrimeReciprocalMass
    apply Finset.sum_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by
      exact_mod_cast (mem_roughPrimeFinset.mp hp).2.1.one_lt
    positivity
  have htail := hterminal e chi m omega a ha N cap hN hEven j hscale
  calc
    (∑ p ∈ S, (∏ i, 1 / ((p i : ℝ) - 1)) *
        actualPrimeTupleLog N p (Fin.last 3)) =
        ∑ r ∈ R, ∑ p ∈ reciprocalBin S a N r,
          (∏ i, 1 / ((p i : ℝ) - 1)) *
            actualPrimeTupleLog N p (Fin.last 3) :=
      sum_source_eq_reciprocalBins S a N _
    _ ≤ ∑ r ∈ R, (a / (r : ℝ)) *
        actualPrimeBoxMass N (binLo omega a r) (binHi a r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact weightedReciprocalBin_le_prime_box e chi m omega a 0 0 ha
        J4 N cap hN j hj r
    _ = M ^ 3 * ∑ r ∈ R,
        (a / (r : ℝ)) *
          actualPrimeReciprocalMass N (a / ((r : ℝ) + 1))
            (a / (r : ℝ) + a / ((r : ℝ) * ((r : ℝ) + 1))) := by
      simp_rw [original_bin_boxMass_eq_prefix_cube]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ M ^ 3 * (4 * a + 6 * K *
        (a / Real.log 3 + 1 / Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left htail (pow_nonneg hM _)

end P1OriginalFourthFiniteBinBudget

end

end ImbalancedChen
