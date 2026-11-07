import ImbalancedChen.P5ZU1011OriginalSixteenJointNearCapModulusConvolution
import ImbalancedChen.P5PrimeDivisorMeanCorrection
import ImbalancedChen.ChenInitialCorrectionBudget

/-!
# Actual joint native coefficient: primitive-prime mean and correction payment

SOURCE ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual near-cap joint U10/U11 coefficient is the same signed sigma in
the original row estimator, its reciprocal-totient main and the singleton
prime-product discrepancy. Its support, unit amplitude and squarefreeness
are DERIVED from the original all16 compiler, not provided as hypotheses.

The exact primitive mean differs from the total prime-prefix mean by the
modulus-prime correction. The original source additionally deletes centre
primes. Both corrections are paid here, uniformly in the fixed geometric
mesh, its positive rational precision and EVERY actual outer mask E.
The centre payment uses the genuine q<N^(153/256) support; it introduces
neither a row-count multiplier nor an unproved absolute AP estimate.

This does not prove a uniform strong AP/PP licence or identify the literal
ordinary Rosser density with an enhanced H248 score or with currentK.
-/

namespace ImbalancedChen.P5Z.U1011SameRhoNativePrimeMeanTransport

noncomputable section

open Classical Filter Topology
open scoped BigOperators
open U1011OriginalSixteenJointNearCapModulusConvolution

def piMass (N : ℕ) : ℝ := ((chenPrimePrefix N).card : ℝ)

def piMain (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  piMass N * physicalDensitySum (modulusSupport n N eta E) (sigma n N eta E)

def singletonPP (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  Part3.primeProductSignedError 1 N N (modulusSupport n N eta E) (sigma n N eta E)
    (P5S1SingletonPP.singletonWeight N (fun _ => 1))

def modulusPrimeCorrection (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  P5PrimeDivisorMean.correction N (modulusSupport n N eta E) (sigma n N eta E) (fun _ => 1)

def centreCorrection (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ q ∈ modulusSupport n N eta E, sigma n N eta E q * chenCentrePrimeAPCount N N q

def primitiveCorrection (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) : ℝ :=
  modulusPrimeCorrection n N eta E + centreCorrection n N eta E

theorem modulusSupport_subset_physicalCap {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    modulusSupport n N eta E ⊆ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ))) := by
  intro q hq
  have hd := modulusSupport_profile hN heta hq
  exact Finset.mem_Icc.mpr ⟨hd.1, Nat.le_floor hd.2.2.2.le⟩

theorem modulusSupport_subset_target {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    modulusSupport n N eta E ⊆ Finset.Icc 1 N := by
  intro q hq
  have hd := modulusSupport_profile hN heta hq
  have hpow : (N : ℝ) ^ (153 / 256 : ℝ) ≤ N := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (show (1 : ℝ) ≤ N by exact_mod_cast (Nat.le_of_lt hN)) theta_lt_one.le
  exact Finset.mem_Icc.mpr ⟨hd.1, by exact_mod_cast hd.2.2.2.le.trans hpow⟩

theorem modulusSupport_card_bound {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    ((modulusSupport n N eta E).card : ℝ) ≤ (N : ℝ) ^ (153 / 256 : ℝ) := by
  have hc : (modulusSupport n N eta E).card ≤ Nat.floor ((N : ℝ) ^ (153 / 256 : ℝ)) := by
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      Finset.card_le_card (modulusSupport_subset_physicalCap hN heta E)
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))

theorem modulusPrimeCorrection_eq_literal (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) :
    modulusPrimeCorrection n N eta E =
      ∑ q ∈ modulusSupport n N eta E, sigma n N eta E q *
        (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
  unfold modulusPrimeCorrection P5PrimeDivisorMean.correction
  apply Finset.sum_congr rfl
  intro q hq
  simp only [P5PrimeDivisorMean.modulusPrimeMass, chenPrimeDivisorCount,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- No distribution input: this is the exact primitive-coprime singleton
mean, at the SAME actual full physical modulus coefficient. -/
theorem estimator_eq_piMain_add_singletonPP_sub_correction
    (n N : ℕ) (eta : ℚ) (E : ℕ × ℕ → Prop) :
    (∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.ordinaryTuples n N E,
      U1011OriginalSixteenJointNearCapCompiler.estimator n N eta t) =
        piMain n N eta E + singletonPP n N eta E - primitiveCorrection n N eta E := by
  rw [estimator_pushforward]
  have h := P5S1SingletonPP.original_signed_AP_mass_eq_PP N
    (modulusSupport n N eta E) (sigma n N eta E)
  rw [← modulusPrimeCorrection_eq_literal] at h
  change _ = piMain n N eta E + singletonPP n N eta E -
    modulusPrimeCorrection n N eta E - centreCorrection n N eta E at h
  unfold primitiveCorrection
  linarith only [h]

theorem abs_modulusPrimeCorrection_le {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    |modulusPrimeCorrection n N eta E| ≤ 4 * (1 + Real.log (N : ℝ)) ^ 2 := by
  have h := P5PrimeDivisorMean.abs_correction_le_log_square N N
    (modulusSupport n N eta E) (sigma n N eta E) (fun _ => 1)
    (modulusSupport_subset_target hN heta E)
    (fun q hq => (modulusSupport_profile hN heta hq).2.1)
    (fun q _ => sigma_abs_le_one hN heta E q) (fun _ _ => by norm_num)
  simpa only [modulusPrimeCorrection, max_eq_right
    (show (1 : ℝ) ≤ N by exact_mod_cast Nat.le_of_lt hN)] using h

/-- The centre is not declared empty and not multiplied by the number
of native rows. Injective actual full moduli give the sublinear support
cardinality, and each AP centre is a subset of the true prime divisors. -/
theorem abs_centreCorrection_le {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    |centreCorrection n N eta E| ≤
      (N : ℝ) ^ (153 / 256 : ℝ) * (Real.log (N : ℝ) / Real.log 2) := by
  have hlog : 0 ≤ Real.log (N : ℝ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.le_of_lt hN))
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hc (q : ℕ) : chenCentrePrimeAPCount N N q ≤ Real.log (N : ℝ) / Real.log 2 :=
    (chenCentrePrimeAPCount_le_divisorCount N N q).trans
      (chenPrimeDivisorCount_le_log N (by omega : 0 < N))
  unfold centreCorrection
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _q ∈ modulusSupport n N eta E, Real.log (N : ℝ) / Real.log 2 := by
      apply Finset.sum_le_sum
      intro q hq
      rw [abs_mul, abs_of_nonneg (chenCentrePrimeAPCount_nonneg N N q)]
      exact (mul_le_mul_of_nonneg_right (sigma_abs_le_one hN heta E q)
        (chenCentrePrimeAPCount_nonneg N N q)).trans (by simpa only [one_mul] using hc q)
    _ = ((modulusSupport n N eta E).card : ℝ) * (Real.log (N : ℝ) / Real.log 2) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (modulusSupport_card_bound hN heta E) hlog

theorem abs_primitiveCorrection_le {n N : ℕ} {eta : ℚ}
    (hN : 1 < N) (heta : 0 < eta) (E : ℕ × ℕ → Prop) :
    |primitiveCorrection n N eta E| ≤ 4 * (1 + Real.log (N : ℝ)) ^ 2 +
      (N : ℝ) ^ (153 / 256 : ℝ) * (Real.log (N : ℝ) / Real.log 2) :=
  (abs_add_le _ _).trans (add_le_add (abs_modulusPrimeCorrection_le hN heta E)
    (abs_centreCorrection_le hN heta E))

/-- ONE threshold precedes every mesh n, every positive rational eta
and every outer pair mask E. No same-rho PP estimate is assumed here. -/
theorem eventually_all_native_primitiveCorrections_paid (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ∀ eta : ℚ, 0 < eta → ∀ E : ℕ × ℕ → Prop,
      |primitiveCorrection n N eta E| ≤ epsilon * singularNormalization N := by
  have hhalf : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [P5PrimeDivisorMean.eventually_log_square_cap_le_normalization (epsilon / 2) hhalf,
    eventually_powerLog_le_singularNormalization (1 / Real.log 2) (153 / 256) 1 theta_lt_one
      (epsilon / 2) hhalf, eventually_gt_atTop (1 : ℕ)] with N hmod hcentre hN
  intro n eta heta E
  have hmp := (abs_modulusPrimeCorrection_le (n := n) hN heta E).trans (by
    simpa only [max_eq_right (show (1 : ℝ) ≤ N by exact_mod_cast Nat.le_of_lt hN)] using hmod N le_rfl)
  have hcp : |centreCorrection n N eta E| ≤ (epsilon / 2) * singularNormalization N := by
    apply (abs_centreCorrection_le hN heta E).trans
    simpa only [pow_one, div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using hcentre
  have hh := (abs_add_le (modulusPrimeCorrection n N eta E) (centreCorrection n N eta E)).trans
    (add_le_add hmp hcp)
  change |primitiveCorrection n N eta E| ≤ _ at hh
  linarith only [hh]

/-- The actual original count is bounded by its unchanged tag0 count,
the literal native prime-density main and the ONE same-sigma signed PP
error, plus an arbitrarily small paid primitive correction. This is not
an analytic estimate of that PP term or of the density main. -/
theorem eventually_original_count_upper_primitivePP (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, ∀ eta : ℚ, 0 < eta → ∀ E : ℕ × ℕ → Prop,
      currentChenUpsilon10 N + currentChenUpsilon11 N E ≤
        (∑ t ∈ U1011OriginalSixteenJointNearCapCompiler.fallbackTuples n N E,
          U11Adaptive.weight N t) + piMain n N eta E + singletonPP n N eta E +
        epsilon * singularNormalization N := by
  filter_upwards [eventually_all_native_primitiveCorrections_paid epsilon hepsilon,
    eventually_gt_atTop (1 : ℕ)] with N hpaid hN
  intro n eta heta E
  have hupper := original_count_upper_sigma (n := n) hN heta E
  have hid := estimator_eq_piMain_add_singletonPP_sub_correction n N eta E
  rw [estimator_pushforward] at hid
  rw [hid] at hupper
  have hc := (neg_le_abs (primitiveCorrection n N eta E)).trans (hpaid n eta heta E)
  linarith only [hupper, hc]

end

end ImbalancedChen.P5Z.U1011SameRhoNativePrimeMeanTransport
