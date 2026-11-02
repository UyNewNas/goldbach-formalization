import ImbalancedChen.P5OriginalJointCausalOverlapSource
import ImbalancedChen.P4BPrimorialDivisorEnvelope
import ImbalancedChen.P5ZU1011JointNearCapPrimeReserve
import ImbalancedChen.P5OriginalJointSameMaskParentGainPayment
import ImbalancedChen.PowerErrorBudget

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pay the literal p1-overlap of the full joint causal rho. The displayed
causal support need not have a polynomial modulus cap: the full primorial
reciprocal-totient bound is enough. One threshold precedes every causal
policy, its small parameters and every outer mask. The original minimum
and same17572 J gain are then attached to an actual arithmetic count with
the STILL UNPAID causal-density discrepancy and signed AP/centre visible.
There is no whole joint count, cost, density, or h1011 premise.
-/

namespace ImbalancedChen.P5OriginalJointCausalOverlapPayment

noncomputable section
open Classical Filter Topology
open scoped BigOperators
open P5U10OriginalMean P5U1011JointOverlap P5OriginalJointCausalOverlapSource
open P5Z.U1011OriginalSixteenArithmeticProducts
open P5Z.U1011AdaptivePrimeError P5Z.JointNearCapPrimeReserve

theorem abs_overlapCorrection_le_primorial {N : ℕ} {E : ℕ × ℕ → Prop} {t : Label}
    (ht : t ∈ jointSelector N E) (R : Policy) (w L : ℝ) :
    |overlapCorrection R N t w L| ≤
      ∑ d ∈ (sieveProduct N t.1.2).divisors, 1 / (Nat.totient d : ℝ) := by
  have hp := (mem_sievePrimes.mp (joint_first_mem_sievePrimes ht)).2.1
  have hpb : t.1.1 ∣ multiplier t :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hcop := (joint_multiplier_coprime_residualProduct ht).of_dvd_left hpb
  have hsub : (residualProduct N t).divisors ⊆ (sieveProduct N t.1.2).divisors := by
    intro e he
    have hRP : residualProduct N t ∣ sieveProduct N t.1.2 := by
      refine ⟨t.1.1, ?_⟩
      simpa only [mul_comm] using (joint_first_mul_residualProduct ht).symm
    exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp he).1.trans hRP,
      (sieveProduct_squarefree N t.1.2).ne_zero⟩
  unfold overlapCorrection
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ e ∈ (residualProduct N t).divisors, 1 / (Nat.totient e : ℝ) := by
      apply Finset.sum_le_sum
      intro e he
      have he0 : 0 < e := Nat.pos_of_mem_divisors he
      have hphi : (0 : ℝ) < Nat.totient e := Nat.cast_pos.mpr (Nat.totient_pos.mpr he0)
      have hpPhi : (1 : ℝ) ≤ Nat.totient t.1.1 := by
        exact_mod_cast (show 1 ≤ Nat.totient t.1.1 from Nat.totient_pos.mpr hp.pos)
      have hphiLe : (Nat.totient e : ℝ) ≤ Nat.totient (t.1.1 * e) := by
        rw [Nat.totient_mul (hcop.of_dvd_right (Nat.mem_divisors.mp he).1), Nat.cast_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hpPhi hphi.le
      rw [abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
      exact (div_le_div_of_nonneg_right
        (actualSmallRoughRho_abs_le_one R N t.1.2 w (t.1.2 : ℝ) L (t.1.1 * e))
        (Nat.cast_nonneg _)).trans (one_div_le_one_div_of_le hphi hphiLe)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun _ _ _ => one_div_nonneg.mpr (Nat.cast_nonneg _))

/-- A real arithmetic estimate, uniform in the complete causal policy.
The first prime is at least N^a; no size bound for the rough word is used. -/
theorem exists_uniform_row_overlap_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 < N → Even N →
      ∀ E : ℕ × ℕ → Prop, ∀ t ∈ jointSelector N E, ∀ R : Policy, ∀ w L : ℝ,
        w ≤ (t.1.2 : ℝ) →
        |effectiveDensity R N t w L - rawDensity R N t w L| ≤
          C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := P4BPrimorialDivisorEnvelope.exists_sievePrimorial_divisor_mass_le_log
  refine ⟨C, hC, ?_⟩
  intro N hN hEven E t ht R w L hw
  have hc := joint_carrier_order ht
  have hp1 := (mem_chenAdditivePrimeCarrier.mp hc.1).2.1
  have hp2 := (mem_chenAdditivePrimeCarrier.mp hc.2.1).2.1
  have hp2N : (t.1.2 : ℝ) ≤ N := by
    exact_mod_cast (mem_chenAdditivePrimeCarrier.mp hc.2.1).1.le
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN.le)
  have hp1R : (0 : ℝ) < t.1.1 := Nat.cast_pos.mpr hp1.pos
  have hpow : 0 < (N : ℝ) ^ (417 / 5000 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hrow := abs_overlapCorrection_le_primorial ht R w L
  have hM := hmass N t.1.2 hEven (by exact_mod_cast hp2.two_le)
  have hlogLe := Real.log_le_log (Nat.cast_pos.mpr hp2.pos) hp2N
  rw [effectiveDensity_eq_raw_sub_overlap ht R w L hw]
  have heq : rawDensity R N t w L - overlapCorrection R N t w L / (t.1.1 : ℝ) -
      rawDensity R N t w L = -(overlapCorrection R N t w L / (t.1.1 : ℝ)) := by ring
  rw [heq, abs_neg, abs_div, abs_of_pos hp1R]
  calc
    _ ≤ (C * Real.log (t.1.2 : ℝ)) / (t.1.1 : ℝ) :=
      div_le_div_of_nonneg_right (hrow.trans hM) hp1R.le
    _ ≤ (C * Real.log (N : ℝ)) / (t.1.1 : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogLe hC.le) hp1R.le
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hC.le hlog) hpow
      (joint_band_and_mask ht).1

def normalizedRaw (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  Real.log (N : ℝ) / singularSeries N * jointRawDensity N E R w L

def normalizedEffective (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  Real.log (N : ℝ) / singularSeries N * jointEffectiveDensity N E R w L

theorem joint_prefix_mass_le_box {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ)) ≤
      actualPrimeBoxMass N (fun _ : Fin 4 => (417 / 5000 : ℝ)) (fun _ => (59 / 250 : ℝ)) := by
  have heq : (∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ)) =
      jointMass N E (fun _ => True) (fun _ => 1) := by
    simp only [jointMass, if_true, fullPrefix_eq_multiplier]
  rw [heq, jointMass_eq_box hN]
  change (∑ q ∈ P5Z.BufferedPrimeErrorPayment.tuples N,
    if jointKept N E (fun _ => True) q then P5Z.BufferedPrimeErrorPayment.weight q * 1 else 0) ≤
      ∑ q ∈ P5Z.BufferedPrimeErrorPayment.tuples N, P5Z.BufferedPrimeErrorPayment.weight q
  apply Finset.sum_le_sum
  intro q hq
  by_cases hk : jointKept N E (fun _ => True) q
  · simp only [if_pos hk, mul_one, le_refl]
  · simpa only [if_neg hk] using actualPrimeBoxWeight_nonneg hq

/-- The whole overlap is o(1) in the original native normalization.
ONE N threshold precedes E, every tuple-dependent causal policy and all
small parameters. Neither enhanced density nor distribution is assumed. -/
theorem eventually_all_causal_overlap_paid (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ E : ℕ × ℕ → Prop, ∀ R : Label → Policy, ∀ w L : Label → ℝ,
        (∀ t ∈ jointSelector N E, w t ≤ (t.1.2 : ℝ)) →
        |normalizedEffective N E R w L - normalizedRaw N E R w L| < epsilon := by
  obtain ⟨C, hC, hrow⟩ := exists_uniform_row_overlap_bound
  have hB : 0 ≤ originalCubeMassBound := by unfold originalCubeMassBound; positivity
  have hlim : Tendsto (fun N : ℕ =>
      (C * originalCubeMassBound / twinPrimeConstant) *
        (Real.log (N : ℝ) ^ 2 / (N : ℝ) ^ (417 / 5000 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_nat_log_pow_div_rpow 2 (by norm_num : (0 : ℝ) < 417 / 5000)).const_mul
        (C * originalCubeMassBound / twinPrimeConstant)
  filter_upwards [hlim.eventually (gt_mem_nhds hepsilon),
    eventually_originalCube_mass_bounded, eventually_gt_atTop (1 : ℕ)] with N hsmall hbox hN
  intro hEven E R w L hw
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN.le)
  have hscale : 0 ≤ Real.log (N : ℝ) / singularSeries N := div_nonneg hlog (singularSeries_pos N).le
  have hpow : 0 < (N : ℝ) ^ (417 / 5000 : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  have hbnd : 0 ≤ C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ) :=
    div_nonneg (mul_nonneg hC.le hlog) hpow.le
  have hmass := (joint_prefix_mass_le_box hN E).trans hbox
  have hsum : |jointEffectiveDensity N E R w L - jointRawDensity N E R w L| ≤
      (C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) * originalCubeMassBound := by
    unfold jointEffectiveDensity jointRawDensity
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      _ ≤ ∑ t ∈ jointSelector N E,
          (C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) /
            (Nat.totient (multiplier t) : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg _)]
        exact div_le_div_of_nonneg_right (hrow N hN hEven E t ht (R t) (w t) (L t) (hw t ht))
          (Nat.cast_nonneg _)
      _ = (C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) *
          ∑ t ∈ jointSelector N E, 1 / (Nat.totient (multiplier t) : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hbnd
  have hscaleLe : Real.log (N : ℝ) / singularSeries N ≤ Real.log (N : ℝ) / twinPrimeConstant :=
    div_le_div_of_nonneg_left hlog twinPrimeConstant_pos (twinPrimeConstant_le_singularSeries N)
  unfold normalizedEffective normalizedRaw
  rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
  calc
    _ ≤ (Real.log (N : ℝ) / singularSeries N) *
        ((C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) * originalCubeMassBound) :=
      mul_le_mul_of_nonneg_left hsum hscale
    _ ≤ (Real.log (N : ℝ) / twinPrimeConstant) *
        ((C * Real.log (N : ℝ) / (N : ℝ) ^ (417 / 5000 : ℝ)) * originalCubeMassBound) :=
      mul_le_mul_of_nonneg_right hscaleLe (mul_nonneg hbnd hB)
    _ = (C * originalCubeMassBound / twinPrimeConstant) *
        (Real.log (N : ℝ) ^ 2 / (N : ℝ) ^ (417 / 5000 : ℝ)) := by ring
    _ < epsilon := hsmall

def normalizedSignedAP (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  (jointAP N E R w L ((N : ℝ) / Real.log (N : ℝ)) - jointCentre N E R w L) /
    singularNormalization N

theorem joint_count_normalized {N : ℕ} (hN : 1 < N) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ)
    (hgates : ∀ t ∈ jointSelector N E, 1 < L t ∧ w t ≤ L t ∧ w t ≤ (t.1.2 : ℝ)) :
    (currentChenUpsilon10 N + currentChenUpsilon11 N E) / singularNormalization N ≤
      normalizedEffective N E R w L + normalizedSignedAP N E R w L := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  have hlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos hn).ne'
  have hn0 : (N : ℝ) ≠ 0 := (zero_lt_one.trans hn).ne'
  have hS : singularSeries N ≠ 0 := (singularSeries_pos N).ne'
  have hH : 0 < singularNormalization N := by
    unfold singularNormalization
    exact div_pos (mul_pos (singularSeries_pos N) (zero_lt_one.trans hn)) (sq_pos_of_ne_zero hlog)
  have h := div_le_div_of_nonneg_right
    (joint_count_upper_actual_causal hn.le E R w L ((N : ℝ) / Real.log (N : ℝ)) hgates) hH.le
  convert h using 1
  unfold normalizedEffective normalizedSignedAP singularNormalization
  field_simp [hlog, hn0, hS]
  <;> ring

/-- This is a DEFINED unpaid signed defect, not a supplied smallness or
density hypothesis. Its rho is the actual causal one above, not the
ordinary-F initialization of the native all16 compiler. -/
def actualCausalDensityExcess (N : ℕ) (E : ℕ × ℕ → Prop)
    (R : Label → Policy) (w L : Label → ℝ) : ℝ :=
  normalizedRaw N E R w L -
    P5Z.U1011OriginalJointHarmonic.nativeJoint N E P5Z.U1011OriginalJointHarmonic.actualMinimum

/-- J's original n48/fine17572 payment now reaches the ACTUAL arithmetic
joint count. The full causal-density and signed AP/centre gaps are kept
with their true signs. Their endpoint estimates are still OPEN. The
newly proved p1-overlap error is already paid, uniformly before policy.
-/
theorem eventually_actual_joint_count_with_J_gain (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ R : Label → Policy, ∀ w L : Label → ℝ,
        (∀ t ∈ jointSelector N (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ)),
          1 < L t ∧ w t ≤ L t ∧ w t ≤ (t.1.2 : ℝ)) →
        -(P2N48WholePriorityOmegaFunctional.wholePriorityOmegaUpper / 4) +
          P2FullMaskActualNativeGain.nativeGain 0 N -
          (actualCausalDensityExcess N (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ)) R w L +
            normalizedSignedAP N (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ)) R w L) / 4 -
          epsilon <
          -(currentChenUpsilon10 N + currentChenUpsilon11 N
            (Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ))) /
              (4 * singularNormalization N) := by
  filter_upwards [eventually_all_causal_overlap_paid epsilon hepsilon,
    P5OriginalJointSameMaskParentGainPayment.eventually_native_joint_with_actual_native_gain_proposal
      (epsilon / 2) (half_pos hepsilon), eventually_gt_atTop (1 : ℕ)] with N hpaid hJ hN
  intro hEven R w L hgates
  let E := Certificates.PairedV2.FullMask.P1E0E1.deletionMask (N : ℝ)
  have hnorm := joint_count_normalized hN E R w L hgates
  have herr := (abs_lt.mp (hpaid hEven E R w L (fun t ht => (hgates t ht).2.2))).2
  have hsource : (currentChenUpsilon10 N + currentChenUpsilon11 N E) / singularNormalization N <
      P5Z.U1011OriginalJointHarmonic.nativeJoint N E P5Z.U1011OriginalJointHarmonic.actualMinimum +
        actualCausalDensityExcess N E R w L + normalizedSignedAP N E R w L + epsilon := by
    unfold actualCausalDensityExcess
    linarith only [hnorm, herr]
  change -(P2N48WholePriorityOmegaFunctional.wholePriorityOmegaUpper / 4) +
    P2FullMaskActualNativeGain.nativeGain 0 N -
      (actualCausalDensityExcess N E R w L + normalizedSignedAP N E R w L) / 4 - epsilon < _
  have htarget : -(currentChenUpsilon10 N + currentChenUpsilon11 N E) /
      (4 * singularNormalization N) =
      -((currentChenUpsilon10 N + currentChenUpsilon11 N E) / singularNormalization N) / 4 := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [htarget]
  change -(P2N48WholePriorityOmegaFunctional.wholePriorityOmegaUpper / 4) +
    P2FullMaskActualNativeGain.nativeGain 0 N - epsilon / 2 <
      -(P5Z.U1011OriginalJointHarmonic.nativeJoint N E P5Z.U1011OriginalJointHarmonic.actualMinimum / 4) at hJ
  linarith only [hsource, hJ, hepsilon]

end
end ImbalancedChen.P5OriginalJointCausalOverlapPayment
