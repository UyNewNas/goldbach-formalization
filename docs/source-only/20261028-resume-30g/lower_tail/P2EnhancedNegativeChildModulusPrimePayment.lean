import ImbalancedChen.P2EnhancedNegativeChildMultiplicity
import ImbalancedChen.ChenInitialCorrectionBudget
import ImbalancedChen.P2EnhancedThetaReciprocalMass
import ImbalancedChen.P2EnhancedCollisionThetaPayment

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Pay the actual modulus-prime part of the finite-coprime-to-li mean shift,
uniformly over the original three child windows and real marked sigma.
The proof derives rho's norm from its actual occurrence fibre. No hrho,
squarefree full modulus, desired AP estimate, K or H248 bound is assumed.
PNT and the remaining signed AP distribution packet remain separate. -/

namespace ImbalancedChen.P2EnhancedNegativeChildModulusPrimePayment

noncomputable section
open scoped Classical BigOperators Topology
open Filter Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedNegativeChildSignedModulus
open P2EnhancedNegativeChildMultiplicity P2EnhancedThetaReciprocalMass
open MathlibNt.SieveTheory.SingularSeries

def modulusPrimeShift (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ q ∈ (modulusSupport N Q D).filter (fun q => q.Coprime N),
    physicalCoefficient N Q D sigma q * (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))

/-- The elementary logarithmic prime-factor bound pays arbitrary positive
moduli, including the ORIGINAL p|d rows, without a false squarefree gate. -/
theorem divisor_mean_sum_le_log_square (N : ℕ) (S : Finset ℕ)
    (hlog : 1 ≤ Real.log (N : ℝ)) (hS : S ⊆ Finset.Icc 1 N) :
    (∑ q ∈ S, chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) ≤
      (8 / Real.log 2) * Real.log (N : ℝ) ^ 2 := by
  have hNpos : 0 < N := by
    by_contra h
    have hz : N = 0 := by omega
    simpa [hz] using hlog
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have htot : (∑ q ∈ S, 1 / (Nat.totient q : ℝ)) ≤ 4 * (1 + Real.log (N : ℝ)) := by
    calc
      _ ≤ ∑ q ∈ Finset.Icc 1 N, 1 / (Nat.totient q : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
      _ ≤ _ := by simpa only [max_eq_right hNr] using sum_reciprocal_totient_le_log N
  calc
    _ ≤ ∑ q ∈ S, (Real.log (N : ℝ) / Real.log 2) * (1 / (Nat.totient q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hdata := Finset.mem_Icc.mp (hS hq)
      have hb := div_le_div_of_nonneg_right
        (chenPrimeDivisorCount_le_log_center (by omega : 0 < q) hdata.2)
        (Nat.cast_nonneg (Nat.totient q))
      convert hb using 1 <;> ring
    _ = (Real.log (N : ℝ) / Real.log 2) * ∑ q ∈ S, 1 / (Nat.totient q : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (Real.log (N : ℝ) / Real.log 2) * (4 * (1 + Real.log (N : ℝ))) :=
      mul_le_mul_of_nonneg_left htot (div_nonneg hlog0 htwo.le)
    _ = (4 / Real.log 2) * Real.log (N : ℝ) * (1 + Real.log (N : ℝ)) := by ring
    _ ≤ (4 / Real.log 2) * Real.log (N : ℝ) * (2 * Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

/-- The full signed modulus-prime shift is bounded using its DERIVED
three-occurrence rho norm, with actual support 0<q<Q<=N. -/
theorem abs_modulusPrimeShift_le_log_budget (N : ℕ) (Q : ℝ) (D : Finset ℕ)
    (sigma : ℕ → ℝ) (hlog : 1 ≤ Real.log (N : ℝ)) (hQN : Q ≤ (N : ℝ))
    (hd : ∀ d ∈ D, 0 < d) (hsigma : ∀ d ∈ D, 0 ≤ sigma d) :
    |modulusPrimeShift N Q D sigma| ≤
      (24 / Real.log 2) * (∑ d ∈ D, sigma d) * Real.log (N : ℝ) ^ 2 := by
  let S := (modulusSupport N Q D).filter (fun q => q.Coprime N)
  have hS : S ⊆ Finset.Icc 1 N := by
    intro q hq
    have hp := physical_support hd (Finset.mem_filter.mp hq).1
    exact Finset.mem_Icc.mpr ⟨by omega, by exact_mod_cast hp.2.le.trans hQN⟩
  have hm : 0 ≤ ∑ d ∈ D, sigma d := Finset.sum_nonneg hsigma
  calc
    |modulusPrimeShift N Q D sigma| ≤
        ∑ q ∈ S, |physicalCoefficient N Q D sigma q| *
          (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
      have hpoint (q : ℕ) :
          |physicalCoefficient N Q D sigma q *
            (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))| =
          |physicalCoefficient N Q D sigma q| *
            (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
        rw [abs_mul, abs_of_nonneg (div_nonneg
          (chenPrimeDivisorCount_nonneg N q) (Nat.cast_nonneg _))]
      unfold modulusPrimeShift
      simpa only [hpoint] using Finset.abs_sum_le_sum_abs
        (fun q => physicalCoefficient N Q D sigma q *
          (chenPrimeDivisorCount N q / (Nat.totient q : ℝ))) S
    _ ≤ ∑ q ∈ S, (3 * ∑ d ∈ D, sigma d) *
        (chenPrimeDivisorCount N q / (Nat.totient q : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right
        (physicalCoefficient_abs_le_three_mass N Q D sigma hd hsigma q)
        (div_nonneg (chenPrimeDivisorCount_nonneg N q) (Nat.cast_nonneg _))
    _ = (3 * ∑ d ∈ D, sigma d) *
        ∑ q ∈ S, chenPrimeDivisorCount N q / (Nat.totient q : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (3 * ∑ d ∈ D, sigma d) * ((8 / Real.log 2) * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (divisor_mean_sum_le_log_square N S hlog hS) (by positivity)
    _ = _ := by ring

/-- The ACTUAL lower cutoff implies a sublinear old-prefix bound. Only
a<=Q/d is used, so no fictitious pointwise enhancement is involved. -/
theorem old_prefix_bound_of_actual_cutoff {N d : ℕ} {Q eta : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hQN : Q ≤ (N : ℝ)) (hR : 1 < Q / (d : ℝ))
    (hcut : (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) :
    (d : ℝ) ≤ (N : ℝ) / (N : ℝ) ^ eta := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hpow : 0 < (N : ℝ) ^ eta := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _
  have ha : cutoff Q d (227 / 50) ≤ Q / (d : ℝ) := by
    simpa only [cutoff, Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hR.le (by norm_num : 1 / (227 / 50 : ℝ) ≤ 1)
  have hm := (le_div_iff₀ hdR).mp (hcut.trans ha)
  apply (le_div_iff₀ hpow).mpr
  simpa only [mul_comm] using hm.trans hQN

theorem sigma_mass_le_reciprocal_mass {N : ℕ} {Q eta : ℝ} (D : Finset ℕ) (sigma : ℕ → ℝ)
    (hN : 0 < N) (hQN : Q ≤ (N : ℝ)) (hd : ∀ d ∈ D, 0 < d)
    (hsigma : ∀ d ∈ D, 0 ≤ sigma d) (hR : ∀ d ∈ D, 1 < Q / (d : ℝ))
    (hcut : ∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) :
    (∑ d ∈ D, sigma d) ≤ ((N : ℝ) / (N : ℝ) ^ eta) * ∑ d ∈ D, sigma d / (d : ℝ) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hmem
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr (hd d hmem)
  calc
    sigma d = (d : ℝ) * (sigma d / (d : ℝ)) := by field_simp [hdR.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (old_prefix_bound_of_actual_cutoff hN (hd d hmem) hQN (hR d hmem) (hcut d hmem))
      (div_nonneg (hsigma d hmem) hdR.le)

/-- A genuine analytic payment of the full original modulus-prime mean
correction. One threshold precedes Q,D,sigma and every child occurrence.
There is no AP distribution, desired count, K or enhancement premise. -/
theorem actual_modulus_prime_shift_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      |modulusPrimeShift N Q D sigma| ≤ epsilon * Theta N Q D sigma := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hU := liuUniversalProduct_pos
  obtain ⟨T1, hT1, hpay⟩ := ninth_power_log_error_budget 2
    (C := 24 / Real.log 2) (α := eta) (ε := 2 * liuUniversalProduct * epsilon)
    (by positivity) heta (by positivity)
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T2, hlog⟩ := eventually_atTop.mp (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T1 T2, by omega, ?_⟩
  intro N hNT Q D sigma hQN hd hsigma hR hcut
  have hN1 := (le_max_left T1 T2).trans hNT
  have hlog1 := hlog N ((le_max_right T1 T2).trans hNT)
  have hN4 : 4 ≤ N := by omega
  have hm : 0 ≤ ∑ d ∈ D, sigma d / (d : ℝ) :=
    Finset.sum_nonneg (fun d hdD => div_nonneg (hsigma d hdD) (Nat.cast_nonneg d))
  have hmass := sigma_mass_le_reciprocal_mass D sigma (by omega : 0 < N) hQN hd hsigma hR hcut
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hdD => ⟨hR d hdD, P2EnhancedCollisionThetaPayment.residual_level_le_N (hd d hdD) hQN⟩)
  calc
    |modulusPrimeShift N Q D sigma| ≤
        (24 / Real.log 2) * (∑ d ∈ D, sigma d) * Real.log (N : ℝ) ^ 2 :=
      abs_modulusPrimeShift_le_log_budget N Q D sigma hlog1 hQN hd hsigma
    _ ≤ (24 / Real.log 2) *
        (((N : ℝ) / (N : ℝ) ^ eta) * ∑ d ∈ D, sigma d / (d : ℝ)) * Real.log (N : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by positivity)) (sq_nonneg _)
    _ = ((24 / Real.log 2) * N * Real.log (N : ℝ) ^ 2 / (N : ℝ) ^ eta) *
        ∑ d ∈ D, sigma d / (d : ℝ) := by ring
    _ ≤ ((2 * liuUniversalProduct * epsilon) * N / Real.log (N : ℝ) ^ 2) *
        ∑ d ∈ D, sigma d / (d : ℝ) := mul_le_mul_of_nonneg_right (hpay N hN1) hm
    _ = epsilon * ((2 * liuUniversalProduct * N / Real.log (N : ℝ) ^ 2) *
        ∑ d ∈ D, sigma d / (d : ℝ)) := by ring
    _ ≤ epsilon * Theta N Q D sigma := mul_le_mul_of_nonneg_left htheta hepsilon.le

def primitivePhysicalDensity (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ q ∈ (modulusSupport N Q D).filter (fun q => q.Coprime N),
    physicalCoefficient N Q D sigma q / (Nat.totient q : ℝ)

/-- Identify the paid term in the existing finite-to-li shift, with the
same physical coefficient. The independent pi-li PNT term is explicit. -/
theorem finite_mean_shift_split (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteCoprimeMean N Q D sigma -
      P2EnhancedTwentyOneChildCorrection.negativeMean N Q D sigma =
      (((chenPrimePrefix N).card : ℝ) -
        AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) *
          primitivePhysicalDensity N Q D sigma - modulusPrimeShift N Q D sigma := by
  rw [finite_mean_minus_model_exact]
  unfold primitivePhysicalDensity modulusPrimeShift
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hcop : q.Coprime N <;> simp only [hcop, if_true, if_false, mul_zero, zero_sub]
  all_goals ring

/-- Genuine uniform analytic payment for the exact finite-coprime mean
after retaining the literal pi-li PNT term. It neither assumes PNT at a
requested accuracy nor claims the full signed AP remainder is small. -/
theorem actual_centered_finite_mean_shift_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      |P2EnhancedTwentyOneChildCorrection.negativeFiniteCoprimeMean N Q D sigma -
        P2EnhancedTwentyOneChildCorrection.negativeMean N Q D sigma -
        (((chenPrimePrefix N).card : ℝ) -
          AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) *
            primitivePhysicalDensity N Q D sigma| ≤ epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, hpay⟩ := actual_modulus_prime_shift_theta_payment heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT Q D sigma hQN hd hsigma hR hcut
  rw [finite_mean_shift_split]
  have heq :
      ((((chenPrimePrefix N).card : ℝ) -
        AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) *
          primitivePhysicalDensity N Q D sigma - modulusPrimeShift N Q D sigma) -
      (((chenPrimePrefix N).card : ℝ) -
        AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418.logarithmicIntegral N) *
          primitivePhysicalDensity N Q D sigma = - modulusPrimeShift N Q D sigma := by ring
  rw [heq, abs_neg]
  exact hpay N hNT Q D sigma hQN hd hsigma hR hcut

def piCenteredPhysicalError (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) : ℝ :=
  ∑ q ∈ modulusSupport N Q D, physicalCoefficient N Q D sigma q *
    (P2EnhancedNegativeChildRosser.rawPrimeAPCount N q -
      if q.Coprime N then ((chenPrimePrefix N).card : ℝ) / (Nat.totient q : ℝ) else 0)

/-- Exact same-rho transition from finite coprime normalization to the
original total-pi prime AP packet. Nonprimitive raw counts remain intact. -/
theorem finite_error_eq_pi_packet_add_shift (N : ℕ) (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ) :
    P2EnhancedTwentyOneChildCorrection.negativeFiniteSignedRemainder N Q D sigma =
      piCenteredPhysicalError N Q D sigma + modulusPrimeShift N Q D sigma := by
  rw [finite_error_pushforward]
  unfold piCenteredPhysicalError modulusPrimeShift
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hcop : q.Coprime N
  · simp only [P2EnhancedNegativeChildRosser.finiteCoprimeAPMean, hcop, if_true,
      population_eq_pi_sub_prime_divisors]
    ring
  · simp only [P2EnhancedNegativeChildRosser.finiteCoprimeAPMean, hcop, if_false,
      sub_zero, add_zero]

/-- The exact finite-coprime signed error differs from the actual
total-pi packet by a uniformly paid analytic term. The remaining AP
packet is EXPLICIT, not assumed small or relabelled an external PP. -/
theorem actual_finite_error_to_pi_packet_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      |P2EnhancedTwentyOneChildCorrection.negativeFiniteSignedRemainder N Q D sigma -
        piCenteredPhysicalError N Q D sigma| ≤ epsilon * Theta N Q D sigma := by
  obtain ⟨T, hT, hpay⟩ := actual_modulus_prime_shift_theta_payment heta hepsilon
  refine ⟨T, hT, ?_⟩
  intro N hNT Q D sigma hQN hd hsigma hR hcut
  rw [finite_error_eq_pi_packet_add_shift, add_sub_cancel_left]
  exact hpay N hNT Q D sigma hQN hd hsigma hR hcut

end
end ImbalancedChen.P2EnhancedNegativeChildModulusPrimePayment
