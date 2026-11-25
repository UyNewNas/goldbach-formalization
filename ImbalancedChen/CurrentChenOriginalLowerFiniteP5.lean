import ImbalancedChen.CurrentChenInitialRosser
import ImbalancedChen.CurrentChenMeanLedger
import ImbalancedChen.ActualLowerFirstExitDensityProjection
import ImbalancedChen.PowerErrorBudget

/-!
Source-only candidate. No compilation, replay or audit has run.

The manuscript's original-prime lower route uses the genuine even-exit
small/rough rho. This file transfers that same coefficient to the actual
receiver source and retains its signed primitive discrepancy. In particular
it supplies no ordinary-BV assertion above the physical square-root level.
Both exceptional prime corrections are paid at every fixed sublinear level.
The causal policy, support licensing, sharp singleton distribution and raw
L1 density evaluation remain separate obligations.
-/

namespace ImbalancedChen.P5S1OriginalLower

noncomputable section

open Filter
open scoped BigOperators

/-- Finite Fubini on the genuine receiver source for the physical rho API. -/
theorem sum_physicalDivisorSum (N : ℕ) (S : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ n ∈ chenPrimeReceiverSource N, physicalDivisorSum S rho n) =
      ∑ q ∈ S, rho q * (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q) := by
  simpa only [physicalDivisorSum, supportedDivisorSum, Finset.sum_filter] using
    currentChen_sum_supportedDivisorSum N S rho

/-- No positivity of the lower rho or its divisor polynomial is required. -/
theorem causal_signed_sum_le_sifted
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) ≤
      ((chenSiftedPrimeSource N z).card : ℝ) := by
  classical
  rw [← sum_physicalDivisorSum]
  calc
    _ ≤ ∑ n ∈ chenPrimeReceiverSource N,
        if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro n _
      have h := actualLowerSmallRoughRho_minorant retainEven N cap w z L
        hL hwL hwz hzcap (n : ℤ)
      have hind : actualSmallRoughIndicator N z (n : ℤ) =
          if Nat.Coprime n (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [← actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (n : ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,
          Nat.coprime_comm]
      simpa only [Int.natAbs_natCast, hind] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Exact original-source mass and true sieve remainder, for the same rho. -/
theorem causal_main_and_remainder
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hEven : Even N) :
    (∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L q *
        (chenPrimeAPCount N N q - chenCentrePrimeAPCount N N q)) =
      ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) +
        ∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
          actualLowerSmallRoughRho retainEven N cap w z L q *
            (chenInitialBoundingSieve N z hEven).rem q := by
  classical
  simp only [physicalDensitySum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [chenInitialBoundingSieve_rem]
  ring

def active (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) : Finset ℕ := by
  classical
  exact (actualLowerSmallRoughModuli retainEven N cap w z).filter
    (fun q => actualLowerSmallRoughRho retainEven N cap w z L q ≠ 0)

/-- Inactive terms vanish for every tested function, including signed errors. -/
theorem sum_eq_active
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (f : ℕ → ℝ) :
    (∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
      actualLowerSmallRoughRho retainEven N cap w z L q * f q) =
      ∑ q ∈ active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L q * f q := by
  classical
  simp only [active, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : actualLowerSmallRoughRho retainEven N cap w z L q = 0 <;> simp [h]

/-- Actual squarefree positive moduli, with no reindexing or extra mask. -/
theorem active_subset_primitive
    (retainEven : List ℕ → Bool) (N cap Q : ℕ) (w z L : ℝ)
    (hQ : ∀ q ∈ active retainEven N cap w z L, q ≤ Q) :
    active retainEven N cap w z L ⊆ chenInitialPrimitiveModuli N Q := by
  classical
  intro q hq
  have hm := (Finset.mem_filter.mp hq).1
  have hq0 := (actualLowerSmallRoughModuli_squarefree retainEven N cap w z hm).ne_zero
  exact mem_chenInitialPrimitiveModuli.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr hq0, hQ q hq,
      actualLowerSmallRoughModuli_coprime_target retainEven N cap w z hm⟩

/-- Signed recentering preserves the negative modulus-prime atom. -/
theorem causal_signed_correction_le_cost
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    |∑ q ∈ active retainEven N cap w z L,
      actualLowerSmallRoughRho retainEven N cap w z L q * chenInitialPrimitiveCorrection N q| ≤
        chenInitialCorrectionCost N (active retainEven N cap w z L) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro q _
  rw [abs_mul]
  calc
    _ ≤ |chenInitialPrimitiveCorrection N q| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L q) (abs_nonneg _)
    _ ≤ _ := abs_chenInitialPrimitiveCorrection_le N q

/-- The exact finite lower transfer to the primitive discrepancy needed by
the permitted sharp singleton theorem. No discrepancy estimate is assumed. -/
theorem causal_primitive_lower
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hEven : Even N)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    ((chenAdditivePrimeCarrier N).card : ℝ) *
        physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
          (actualLowerSmallRoughRho retainEven N cap w z L) +
      (∑ q ∈ active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
      chenInitialCorrectionCost N (active retainEven N cap w z L) ≤
        ((chenSiftedPrimeSource N z).card : ℝ) := by
  have hfinite := causal_signed_sum_le_sifted retainEven N cap w z L hL hwL hwz hzcap
  rw [causal_main_and_remainder retainEven N cap w z L hEven,
    sum_eq_active] at hfinite
  have hrem :
      (∑ q ∈ active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L q *
          (chenInitialBoundingSieve N z hEven).rem q) =
      (∑ q ∈ active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L q *
          finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) +
      ∑ q ∈ active retainEven N cap w z L,
        actualLowerSmallRoughRho retainEven N cap w z L q * chenInitialPrimitiveCorrection N q := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have h := chenInitialBoundingSieve_rem_sub_primitive_error N z hEven q
    have heq : (chenInitialBoundingSieve N z hEven).rem q =
        finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q +
          chenInitialPrimitiveCorrection N q := by linarith only [h]
    rw [heq]
    ring
  rw [hrem] at hfinite
  have hcost := (abs_le.mp (causal_signed_correction_le_cost retainEven N cap w z L)).1
  linarith

/-- Both correction types are sublinear whenever the genuine physical
moduli have a sublinear envelope. This extends the old sqrt-only supplier. -/
theorem correctionCost_le_envelope {N Q : ℕ} {X : ℝ}
    (hN : 0 < N) (hlog : 1 ≤ Real.log (N : ℝ))
    (hX1 : 1 ≤ X) (hXN : X ≤ (N : ℝ)) (hQX : (Q : ℝ) ≤ X)
    (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 Q) :
    chenInitialCorrectionCost N S ≤ (17 / Real.log 2) * X * Real.log (N : ℝ) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := hX1.trans hXN
  have hQN : Q ≤ N := by exact_mod_cast hQX.trans hXN
  have hlogQ : Real.log (max 1 (Q : ℝ)) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
      (max_le hN1 (hQX.trans hXN))
  have hB : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (by linarith) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hbracket : (Q : ℝ) + 8 * (1 + Real.log (max 1 (Q : ℝ))) ≤
      17 * X * Real.log (N : ℝ) := by
    have hm1 := mul_nonneg (sub_nonneg.mpr hX1) (sub_nonneg.mpr hlog)
    have hm2 := mul_nonneg (zero_le_one.trans hX1) (sub_nonneg.mpr hlog)
    nlinarith
  calc
    _ ≤ (Real.log (N : ℝ) / Real.log 2) *
        ((Q : ℝ) + 8 * (1 + Real.log (max 1 (Q : ℝ)))) :=
      chenInitialCorrectionCost_le_log hN hQN S hS
    _ ≤ (Real.log (N : ℝ) / Real.log 2) * (17 * X * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hbracket hB
    _ = _ := by ring

/-- Uniform in all subsequent supports; theta may lie above one half. -/
theorem eventually_correctionCost_le_normalized
    (theta eta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℕ, ∀ S : Finset ℕ,
      (Q : ℝ) ≤ (N : ℝ) ^ theta → S ⊆ Finset.Icc 1 Q →
        chenInitialCorrectionCost N S ≤ eta * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization
    (17 / Real.log 2) theta 2 htheta1 eta heta,
    eventually_one_le_nat_log, eventually_ge_atTop (1 : ℕ)] with N hp hlog hN
  intro Q S hQ hS
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX1 : 1 ≤ (N : ℝ) ^ theta := Real.one_le_rpow hN1 htheta0
  have hXN : (N : ℝ) ^ theta ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hN1 htheta1.le
  exact (correctionCost_le_envelope (by omega) hlog hX1 hXN hQ S hS).trans hp

/-- The actual lower rho receives this payment with its exact signed
primitive error left untouched. This is a concrete finite prerequisite to
the original L1 route, not an assertion of its causal density constant. -/
theorem eventually_causal_primitive_lower_paid
    (theta eta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap Q : ℕ) (w z L : ℝ),
      Even N → 1 < L → w ≤ L → w ≤ z → z ≤ (cap : ℝ) →
      (Q : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ q ∈ active retainEven N cap w z L, q ≤ Q) →
      ((chenAdditivePrimeCarrier N).card : ℝ) *
          physicalDensitySum (actualLowerSmallRoughModuli retainEven N cap w z)
            (actualLowerSmallRoughRho retainEven N cap w z L) +
        (∑ q ∈ active retainEven N cap w z L,
          actualLowerSmallRoughRho retainEven N cap w z L q *
            finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
        eta * singularNormalization N ≤ ((chenSiftedPrimeSource N z).card : ℝ) := by
  filter_upwards [eventually_correctionCost_le_normalized theta eta htheta0 htheta1 heta]
    with N hpaid
  intro retainEven cap Q w z L hEven hL hwL hwz hzcap hQ hsupport
  have hS := (active_subset_primitive retainEven N cap Q w z L hsupport).trans
    (chenInitialPrimitiveModuli_subset N Q)
  have hcost := hpaid Q (active retainEven N cap w z L) hQ hS
  have hfinite := causal_primitive_lower retainEven N cap w z L hEven hL hwL hwz hzcap
  linarith

/-- The literal adopted first Chen row receives this same causal lower rho,
at a = 417/5000. This does not substitute the old beta = 4/33 row. -/
theorem eventually_currentUpsilon1_causal_primitive_lower_paid
    (theta eta : ℝ) (htheta0 : 0 ≤ theta) (htheta1 : theta < 1) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (retainEven : List ℕ → Bool) (cap Q : ℕ) (w L : ℝ),
      Even N → 1 < L → w ≤ L → w ≤ (N : ℝ) ^ (417 / 5000 : ℝ) →
      (N : ℝ) ^ (417 / 5000 : ℝ) ≤ (cap : ℝ) →
      (Q : ℝ) ≤ (N : ℝ) ^ theta →
      (∀ q ∈ active retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L, q ≤ Q) →
      ((chenAdditivePrimeCarrier N).card : ℝ) *
          physicalDensitySum
            (actualLowerSmallRoughModuli retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)))
            (actualLowerSmallRoughRho retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L) +
        (∑ q ∈ active retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L,
          actualLowerSmallRoughRho retainEven N cap w ((N : ℝ) ^ (417 / 5000 : ℝ)) L q *
            finitePrimitiveDiscrepancy (chenPrimePrefix N) (fun _ => 1) N q) -
        eta * singularNormalization N ≤ currentChenUpsilon1 N := by
  filter_upwards [eventually_causal_primitive_lower_paid theta eta htheta0 htheta1 heta]
    with N hpaid
  intro retainEven cap Q w L hEven hL hwL hwz hzcap hQ hsupport
  rw [currentChenUpsilon1_eq_actual_sifted_card N hEven]
  exact hpaid retainEven cap Q w ((N : ℝ) ^ (417 / 5000 : ℝ)) L
    hEven hL hwL hwz hzcap hQ hsupport

end

end ImbalancedChen.P5S1OriginalLower
