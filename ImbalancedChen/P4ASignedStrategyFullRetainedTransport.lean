import ImbalancedChen.P4AHistoricalNegativeMassReserve

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

A finite signed family of actual retention strategies shares one attachment
precision and one threshold. Each summand keeps its own literal physical rho.
The reserve is the larger of the positive and negative external coefficient
masses, not the signed sum of those coefficients. The full retained source is
at w=0, and its signed presieve continuation correction remains explicit.

This supplies finite transport, not the missing original all22 policy binding,
full retained integral limit, or an enclosure at currentK. The existing
fixed-epsilon attachment envelope need not tend to zero.
-/

namespace ImbalancedChen.P4ASignedStrategyFullRetainedTransport

noncomputable section
open scoped BigOperators

variable {ι : Type*}

def positiveWeight (s : Finset ι) (a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, max (a i) 0

def negativeWeight (s : Finset ι) (a : ι → ℝ) : ℝ :=
  ∑ i ∈ s, max (-a i) 0

def reserveWeight (s : Finset ι) (a : ι → ℝ) : ℝ :=
  max (positiveWeight s a) (negativeWeight s a)

/-- The sharp common-interval charge for arbitrary real external weights.
The internal errors are nonnegative; the external weights need not be. -/
theorem signed_interval_sum_abs_le (s : Finset ι) (a err : ι → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (herr : ∀ i ∈ s, 0 ≤ err i ∧ err i ≤ B) :
    |∑ i ∈ s, a i * err i| ≤ B * reserveWeight s a := by
  have hpoint : ∀ i ∈ s,
      -(B * max (-a i) 0) ≤ a i * err i ∧
        a i * err i ≤ B * max (a i) 0 := by
    intro i hi
    obtain ⟨he0, heB⟩ := herr i hi
    by_cases ha : 0 ≤ a i
    · rw [max_eq_left ha, max_eq_right (neg_nonpos.mpr ha)]
      constructor <;> nlinarith
    · have ha' : a i ≤ 0 := (lt_of_not_ge ha).le
      rw [max_eq_right ha', max_eq_left (neg_nonneg.mpr ha')]
      constructor <;> nlinarith
  have hlo := Finset.sum_le_sum (fun i hi => (hpoint i hi).1)
  have hhi := Finset.sum_le_sum (fun i hi => (hpoint i hi).2)
  have hlo' : -(B * negativeWeight s a) ≤ ∑ i ∈ s, a i * err i := by
    simpa only [negativeWeight, Finset.sum_neg_distrib, Finset.mul_sum] using hlo
  have hhi' : (∑ i ∈ s, a i * err i) ≤ B * positiveWeight s a := by
    simpa only [positiveWeight, Finset.mul_sum] using hhi
  have hp : B * positiveWeight s a ≤ B * reserveWeight s a :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hB
  have hn : B * negativeWeight s a ≤ B * reserveWeight s a :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hB
  exact abs_le.mpr ⟨by linarith, hhi'.trans hp⟩

/-- The physical-minus-full difference retains the signed sum of the
literal negative-mass corrections, including its sign for each strategy. -/
theorem signed_physical_full_ledger (s : Finset ι) (a : ι → ℝ)
    (retain : ι → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hwz : w ≤ z) :
    (∑ i ∈ s, a i * p4aReservePhysicalDensity (retain i) N cap w z L) -
        (∑ i ∈ s, a i * p4aReserveRawDensity (retain i) N cap 0 z) =
      (∑ i ∈ s, a i *
        (p4aReserveRawDensity (retain i) N cap w z *
          (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
            actualSmallEulerProduct N cap w) +
          p4aReserveNegativeMass (retain i) N cap w z *
            (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
              HistoricalPrefixCapData.p4aSmallMinusDensity N cap w L))) -
        (∑ i ∈ s, a i * p4aActualPresieveCorrection (retain i) N cap w z) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  have hfull := p4a_fullRaw_eq_euler_presieved_add_correction
    (retain i) N cap w z hwz
  have hphys : p4aReservePhysicalDensity (retain i) N cap w z L =
      p4aReserveRawDensity (retain i) N cap w z *
          HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L +
        p4aReserveNegativeMass (retain i) N cap w z *
          (HistoricalPrefixCapData.p4aSmallPlusDensity N cap w L -
            HistoricalPrefixCapData.p4aSmallMinusDensity N cap w L) := by
    unfold p4aReservePhysicalDensity
    rw [actualSmallRoughRho_density_eq]
    exact p4a_signSensitiveDensity_eq_raw_add_negativeMass _ _ _ _
  rw [hphys, hfull]
  ring

/-- Exact transport of the full retained source and its presieve correction
to a signed sum of the same physical attachment errors. -/
theorem signed_corrected_full_defect_eq (s : Finset ι) (a : ι → ℝ)
    (retain : ι → List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (hwz : w ≤ z) :
    (∑ i ∈ s, a i * p4aReservePhysicalDensity (retain i) N cap w z L) -
        ((∑ i ∈ s, a i * p4aReserveRawDensity (retain i) N cap 0 z) -
          ∑ i ∈ s, a i * p4aActualPresieveCorrection (retain i) N cap w z) =
      ∑ i ∈ s, a i *
        (p4aReservePhysicalDensity (retain i) N cap w z L -
          actualSmallEulerProduct N cap w *
            p4aReserveRawDensity (retain i) N cap w z) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [p4a_fullRaw_eq_euler_presieved_add_correction (retain i) N cap w z hwz]
  ring

/-- One epsilon and threshold precede the entire signed strategy family.
No sign restriction is imposed on a, no common coefficient replaces the
actual rho, and the projection corrections are not dropped. -/
theorem exists_signed_family_full_transport
    (nu r eta epsilonMax : ℝ) (hnu : 0 < nu) (hr : 0 < r)
    (heta : 0 < eta) (hepsilonMax : 0 < epsilonMax) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < 1 / 8 ∧
      epsilon < epsilonMax ∧ epsilon ^ 2 ≤ r ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
        ∀ cap : ℕ, (N : ℝ) ^ (nu * r) ≤ (cap : ℝ) →
          ∀ (s : Finset ι) (a : ι → ℝ) (retain : ι → List ℕ → Bool),
            let w := (N : ℝ) ^ (nu * epsilon ^ 2)
            let z := (N : ℝ) ^ (nu * r)
            let L := (N : ℝ) ^ (nu * epsilon)
            |(∑ i ∈ s, a i * p4aReservePhysicalDensity (retain i) N cap w z L) -
              ((∑ i ∈ s, a i * p4aReserveRawDensity (retain i) N cap 0 z) -
                ∑ i ∈ s, a i * p4aActualPresieveCorrection (retain i) N cap w z)| ≤
              (eta * singularSeries N / Real.log (N : ℝ)) * reserveWeight s a := by
  obtain ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr,
      N₀, hN₀, hbound⟩ :=
    exists_actualSmallRoughRho_density_error_le_target_reserve
      nu r eta epsilonMax hnu hr heta hepsilonMax
  refine ⟨epsilon, hepsilon, hepsilon8, hepsilonMax', hepsilonr, N₀, hN₀, ?_⟩
  intro N hN hEven cap hcap s a retain
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hwz : (N : ℝ) ^ (nu * epsilon ^ 2) ≤ (N : ℝ) ^ (nu * r) :=
    Real.rpow_le_rpow_of_exponent_le hN1.le
      (mul_le_mul_of_nonneg_left hepsilonr hnu.le)
  dsimp only
  rw [signed_corrected_full_defect_eq s a retain N cap _ _ _ hwz]
  apply signed_interval_sum_abs_le
  · exact div_nonneg (mul_nonneg heta.le (singularSeries_pos N).le)
      (Real.log_pos hN1).le
  · intro i _hi
    exact hbound N hN hEven cap hcap (retain i)

end
end ImbalancedChen.P4ASignedStrategyFullRetainedTransport
