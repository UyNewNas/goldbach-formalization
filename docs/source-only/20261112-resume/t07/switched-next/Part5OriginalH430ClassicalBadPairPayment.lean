import ImbalancedChen.Part5OriginalH430ClassicalBadPairPool

/-! The original classical bad Γ5 source and its genuinely tested fibre
share one complete-modulus budget. The error is relative to the entire
classical clamp, uniformly in the original freeze after τ is fixed. -/
namespace ImbalancedChen.Part5OriginalH430ClassicalBadPairPayment
noncomputable section
open Finset Real Filter Wu2008DoubleSieve
open MathlibNt.SieveTheory.BombieriVinogradov MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedBadGamma5ArithmeticGeometry (badLabels)
open P2EnhancedSwitchedUnsiftedSource (originalBadPairCount)
open P2EnhancedSwitchedTrueNormalization (thetaConversion)
open P2SeedOmegaLiteralFibre (K)
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RootIntervalTheta
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalRootThetaPayment
open Part5OriginalH430SeedPurifiedPrimeFibres (fibre badFibre)
open Part5OriginalH430ClassicalBadPairReceivers
open Part5OriginalH430ClassicalBadPairPool
open scoped Classical Topology BigOperators

private theorem pool_log {τ : ℝ} (ht : 0<τ) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      (∑ k∈pool N τ,major N k)≤C*(N:ℝ)/log (N:ℝ)^3 := by
  obtain ⟨B,hB,C,hC,hbv⟩ := part3_chenQuotientPrimeAPError_pool_log_saving (3:ℝ) (by norm_num)
  have hs : ∀ᶠ N : ℕ in atTop, ⌊(N:ℝ)^(1/2-τ)⌋₊≤panModulusCutoff N B := by
    simpa only [liuSourceDEpsilon] using eventually_liuSourceDEpsilon_le_panModulusCutoff τ B ht hB
  refine ⟨C+1,by linarith,?_⟩
  filter_upwards [hbv,hs,eventually_one_le_nat_log,eventually_ge_atTop (2:ℕ),
    eventually_powerLog_le_logAccuracy (3/log 2) (1/2) 1 3 (by norm_num) 1 zero_lt_one]
    with N hBV hcap hlog hN hpower
  let D := ⌊(N:ℝ)^(1/2-τ)⌋₊
  have ha : (∑ k∈pool N τ,trueError N k)≤C*(N:ℝ)/log (N:ℝ)^3 := by
    simpa only [pool,trueError,Real.rpow_natCast] using hBV D hcap
  have hc : (pool N τ).card≤D := by simpa [pool,D] using
    (card_le_card (filter_subset (fun k : ℕ => k.Coprime N) (Icc 1 D)))
  have hcard : ((pool N τ).card:ℝ)≤(N:ℝ)^(1/2:ℝ) := (Nat.cast_le.mpr hc).trans
    ((Nat.floor_le (rpow_nonneg (Nat.cast_nonneg N) _)).trans
      (rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤N by omega)) (by linarith)))
  have hcent : ((pool N τ).card:ℝ)*((3/log 2)*log (N:ℝ)) ≤ (N:ℝ)/log (N:ℝ)^3 := by
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (3/log 2)*(N:ℝ)^(1/2:ℝ)*log (N:ℝ) := by ring
      _ ≤ _ := by simpa only [pow_one,one_mul] using hpower
  simp only [major,sum_add_distrib,sum_const,nsmul_eq_mul]
  linarith only [ha,hcent]

theorem actual_bad_all_labels {τ ε : ℝ} (ht : 0<τ) (ht' : τ≤1/12) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1)≤11/384 → ∀ B ⊆ classicalBand N,
      (∑ p∈B,∑ l∈badLabels N (rootQ N n .U3 τ p) p,
        difference N p (rootQ N n .U3 τ p) l) ≤ ε*clampMass N n τ := by
  obtain ⟨C,_,hC⟩ := pool_log ht
  let I := intervalMass clampStart (1/3) (1/2)
  obtain ⟨hi,hw⟩ := uniform_clamp_witness
  have hI : 0<I := hi
  let c := (2*200^3:ℝ)
  filter_upwards [actual_bad_whole_pool,hC,hw,
    p5z_eventually_logCube_le_singularNormalization (c*C) (ε*(I/2)) (by positivity)]
    with N hwhole hpool hw hnorm
  intro heven n hn B hB
  have htot := hwhole heven n τ ht.le ht' hn B hB
  calc
    _ ≤ _ := htot
    _ ≤ c*(C*(N:ℝ)/log (N:ℝ)^3) := mul_le_mul_of_nonneg_left hpool (by norm_num [c])
    _ = (c*C)*(N:ℝ)/log (N:ℝ)^3 := by ring
    _ ≤ _ := hnorm
    _ = ε*((I/2)*singularNormalization N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hw n τ ht.le ht' hn) he.le

def originalDebt (N p : ℕ) (Q : ℝ) : ℝ :=
  max (originalBadPairCount N Q p) (badFibre true N Q p)-
    (K/4)*thetaConversion N p*badFibre false N Q p

private theorem original_local (N p : ℕ) (Q : ℝ) :
    originalDebt N p Q ≤ ∑ l∈badLabels N Q p,difference N p Q l := by
  unfold originalDebt originalBadPairCount badFibre difference
  dsimp only
  rw [mul_sum,sum_sub_distrib]
  apply sub_le_sub_right
  apply max_le
  · exact sum_le_sum (fun l _ => le_max_left (sourceAt N p Q l) _)
  · exact sum_le_sum (fun l _ => le_max_right _ _)

theorem actual_Gamma5_at_common_mass {τ ε : ℝ} (ht : 0<τ) (ht' : τ≤1/12) (he : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n : ℕ, 1/((n:ℝ)+1)≤11/384 → ∀ B ⊆ classicalBand N,
      (∑ p∈B,originalDebt N p (rootQ N n .U3 τ p)) ≤ ε*clampMass N n τ := by
  filter_upwards [actual_bad_all_labels ht ht' he] with N h
  intro heven n hn B hB
  exact (sum_le_sum (fun p _ => original_local N p (rootQ N n .U3 τ p))).trans (h heven n hn B hB)

end
end ImbalancedChen.Part5OriginalH430ClassicalBadPairPayment
