import ImbalancedChen.P2EnhancedNegativeChildDensityBudget
import ImbalancedChen.P2MarkedThetaLiNormalization
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrincipalPNT

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
Pay the actual pi-minus-literal-li term of the original child mean shift.
The existing PanPrincipal prime-count theorem is used at its true-li
normalization and the additive 2/log 2 is paid explicitly.  No PNT/AP
bound for this family, K, positive-pair or H248 conclusion is assumed. -/

namespace ImbalancedChen.P2EnhancedNegativeChildPNTPayment

noncomputable section
open scoped Classical BigOperators Topology
open Filter Wu2008DoubleSieve
open P2EnhancedTwentyOneSameQWeighted P2EnhancedThetaReciprocalMass
open P2EnhancedNegativeChildSignedModulus P2EnhancedNegativeChildModulusPrimePayment
open P2EnhancedNegativeChildDensityBudget
open MathlibNt.SieveTheory.SingularSeries
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418 (logarithmicIntegral)
open MathlibNt.SieveTheory.BombieriVinogradov (trueLogarithmicIntegral)

/-- The reused PNT counts precisely the independently defined inclusive
prime prefix, including its integer endpoint. -/
theorem prefix_card_eq_pan_primeCount (N : ℕ) :
    ((chenPrimePrefix N).card : ℝ) =
      AnalyticNumberTheory.LargeSieve.PanPrincipal.primeCount N := by
  simp [chenPrimePrefix, AnalyticNumberTheory.LargeSieve.PanPrincipal.primeCount,
    Finset.sum_boole]

/-- A quantitative consequence of the EXISTING natural prime-count PNT.
The literal integral, rather than the shifted true-li, is used here.
The threshold depends only on delta, before any child/source data. -/
theorem eventually_pi_literalLi_log_four {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop,
      |((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N| ≤
        delta * (N : ℝ) / Real.log (N : ℝ) ^ 4 := by
  obtain ⟨C, hC, M, hPNT⟩ :=
    AnalyticNumberTheory.LargeSieve.PanPrincipal.primeCount_li_pnt 5 (by norm_num)
  let c0 : ℝ := 2 / Real.log 2
  have hc0 : 0 < c0 := by
    dsimp [c0]
    exact div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlargeLog : ∀ᶠ N : ℕ in atTop, 2 * C / delta ≤ Real.log (N : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop _)
  have hconstant : ∀ᶠ N : ℕ in atTop,
      (2 * c0 / delta) * Real.log (N : ℝ) ^ 4 ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using
      box_eventually_log_power_budget 4 (c := 2 * c0 / delta) (α := 1)
        (by positivity) (by norm_num)
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (2 : ℕ),
    hlargeLog, hconstant] with N hNM hN hCL hconstantN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmain : |((chenPrimePrefix N).card : ℝ) - trueLogarithmicIntegral N| ≤
      C * (N : ℝ) / Real.log (N : ℝ) ^ 5 := by
    rw [prefix_card_eq_pan_primeCount]
    simpa only [trueLogarithmicIntegral, Real.rpow_natCast] using hPNT N hNM
  have hCsmall : C ≤ (delta / 2) * Real.log (N : ℝ) := by
    have := (div_le_iff₀ hdelta).mp hCL
    nlinarith
  have hmainSmall : C * (N : ℝ) / Real.log (N : ℝ) ^ 5 ≤
      (delta / 2) * (N : ℝ) / Real.log (N : ℝ) ^ 4 := by
    calc
      _ ≤ ((delta / 2) * Real.log (N : ℝ)) * N / Real.log (N : ℝ) ^ 5 :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCsmall (Nat.cast_nonneg N)) (by positivity)
      _ = _ := by field_simp [hlog.ne']; ring
  have hconstantSmall : c0 ≤ (delta / 2) * (N : ℝ) / Real.log (N : ℝ) ^ 4 := by
    apply (le_div_iff₀ (pow_pos hlog 4)).mpr
    have h := (div_le_iff₀ hdelta).mp
      (show (2 * c0 * Real.log (N : ℝ) ^ 4) / delta ≤ (N : ℝ) by
        convert hconstantN using 1 <;> ring)
    nlinarith
  calc
    _ = |(((chenPrimePrefix N).card : ℝ) - trueLogarithmicIntegral N) + c0| := by
      rw [P2MarkedThetaLiNormalization.trueLi_eq_literalLi_add]
      congr 1
      dsimp [c0]
      ring
    _ ≤ |((chenPrimePrefix N).card : ℝ) - trueLogarithmicIntegral N| + |c0| :=
      abs_add _ _
    _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ 5 + c0 := by
      rw [abs_of_pos hc0]
      exact add_le_add_right hmain _
    _ ≤ _ := by linarith [hmainSmall, hconstantSmall]

/-- Real payment of the previously unpaid PNT component.  In particular,
the density norm is proved from its actual source and is not an input. -/
theorem actual_pnt_density_theta_payment {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      |(((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N) *
        primitivePhysicalDensity N Q D sigma| ≤ epsilon * Theta N Q D sigma := by
  let delta : ℝ := (2 * liuUniversalProduct * epsilon) / 24
  have hdelta : 0 < delta := by
    have hU := liuUniversalProduct_pos
    dsimp [delta]
    positivity
  have hlogTop : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T1, hPNT⟩ := eventually_atTop.mp (eventually_pi_literalLi_log_four hdelta)
  obtain ⟨T2, hlog⟩ := eventually_atTop.mp
    (hlogTop.eventually (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hNT Q D sigma hQN hd hsigma hR
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hNT
  have hT12 : max T1 T2 ≤ N := (le_max_right _ _).trans hNT
  have hp := hPNT N ((le_max_left _ _).trans hT12)
  have hl := hlog N ((le_max_right _ _).trans hT12)
  have hlp : 0 < Real.log (N : ℝ) := by linarith
  have hmass : 0 ≤ ∑ d ∈ D, sigma d / (d : ℝ) :=
    Finset.sum_nonneg (fun d hdD => div_nonneg (hsigma d hdD) (Nat.cast_nonneg d))
  have htheta := Theta_lower hN4 Q D sigma hd hsigma
    (fun d hdD => ⟨hR d hdD,
      P2EnhancedCollisionThetaPayment.residual_level_le_N (hd d hdD) hQN⟩)
  calc
    _ = |((chenPrimePrefix N).card : ℝ) - logarithmicIntegral N| *
        |primitivePhysicalDensity N Q D sigma| := abs_mul _ _
    _ ≤ (delta * (N : ℝ) / Real.log (N : ℝ) ^ 4) *
        (24 * Real.log (N : ℝ) ^ 2 * ∑ d ∈ D, sigma d / (d : ℝ)) :=
      mul_le_mul hp (primitivePhysicalDensity_abs_le N Q D sigma hl hQN hd hsigma)
        (abs_nonneg _) (by positivity)
    _ = epsilon * ((2 * liuUniversalProduct * (N : ℝ) / Real.log (N : ℝ) ^ 2) *
        ∑ d ∈ D, sigma d / (d : ℝ)) := by
      dsimp [delta]
      field_simp [hlp.ne'] <;> ring
    _ ≤ epsilon * Theta N Q D sigma :=
      mul_le_mul_of_nonneg_left htheta hepsilon.le

/-- The complete original finite-coprime to li mean shift is now paid.
G supplies the modulus-prime term, H supplies PNT with the actual norm.
One threshold precedes Q,D,sigma and the complete three-window family. -/
theorem actual_finite_to_model_mean_theta_payment {eta epsilon : ℝ}
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (Q : ℝ) (D : Finset ℕ) (sigma : ℕ → ℝ), Q ≤ (N : ℝ) →
      (∀ d ∈ D, 0 < d) → (∀ d ∈ D, 0 ≤ sigma d) →
      (∀ d ∈ D, 1 < Q / (d : ℝ)) →
      (∀ d ∈ D, (N : ℝ) ^ eta ≤ cutoff Q d (227 / 50)) →
      |P2EnhancedTwentyOneChildCorrection.negativeFiniteCoprimeMean N Q D sigma -
        P2EnhancedTwentyOneChildCorrection.negativeMean N Q D sigma| ≤
        epsilon * Theta N Q D sigma := by
  obtain ⟨T1, hT1, hPNT⟩ := actual_pnt_density_theta_payment (half_pos hepsilon)
  obtain ⟨T2, hT2, hmod⟩ := actual_modulus_prime_shift_theta_payment heta (half_pos hepsilon)
  refine ⟨max T1 T2, hT1.trans (le_max_left _ _), ?_⟩
  intro N hNT Q D sigma hQN hd hsigma hR hcut
  have hp := hPNT N ((le_max_left _ _).trans hNT) Q D sigma hQN hd hsigma hR
  have hm := hmod N ((le_max_right _ _).trans hNT) Q D sigma hQN hd hsigma hR hcut
  rw [finite_mean_shift_split]
  exact (abs_sub _ _).trans (by linarith only [hp, hm])

end
end ImbalancedChen.P2EnhancedNegativeChildPNTPayment
