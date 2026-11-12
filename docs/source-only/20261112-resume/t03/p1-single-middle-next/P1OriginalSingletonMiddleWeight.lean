import ImbalancedChen.P1OriginalSingletonMiddleRank
import ImbalancedChen.P5CanonicalTentNarrowSingletonTransfer

/-! Attach the original, independently defined one-prime log-collar profile
to the actual final rectangular upper coefficient. The two old divisor
budgets precede all choices of moduli and have coefficient-uniform inputs. -/
namespace ImbalancedChen.P1OriginalSingletonMiddleWeight
noncomputable section
open Classical Filter
open scoped BigOperators
open P4BOriginalCollisionWords (Params)
open P4AHeldTaggedCompilerSupport (J0)
open P4BOriginalFiniteSmoothCount (Q)
open P1OriginalSharpFiniteReceiver (middle)
open P1OriginalSingletonMiddleRank (live live_data read_live)
open P5OriginalSharpPrime
open P5OriginalPrimeEndpoint
open P5OriginalSingletonLowerTrimPaid
open P5CanonicalTentNarrowSingletonTransfer
  (lowerReserve upperReserve fullSmoothWeight smoothNatural smooth_range original_source_exact_reserves
   upperWidth upperWidth_le_original_endpoint original_upper_tail original_middle)

private theorem lower_paid (kappa eta : ℝ) (hk : 0<kappa) (hk1 : kappa<1) (hu : 0<eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (S : Finset ℕ) (c : ℕ→ℝ), S ⊆ Finset.Icc 1 N →
      (∀ d∈S, |c d|≤1) → |lowerReserve kappa 6 N S c| ≤ eta*singularNormalization N := by
  obtain ⟨C,hC,H⟩ := exists_prefix_primitive_budget (show 0<kappa/2 by positivity)
  filter_upwards [eventually_originalLowerCut_lt kappa hk hk1,
    eventually_powerLog_le_singularNormalization (3*C) (1-kappa/2) 0 (by linarith) (eta/3) (by positivity),
    eventually_powerLog_le_singularNormalization 12 (1-kappa) 0 (by linarith) (eta/3) (by positivity),
    eventually_powerLog_le_singularNormalization 12 (1-kappa) 1 (by linarith) (eta/3) (by positivity),
    eventually_ge_atTop (2:ℕ)] with N hY h1 h2 h3 hN
  intro S c hS hc
  let T := originalLowerCut kappa N
  let W := smoothNatural kappa 6 N
  have hn : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have h := H N T N (chenPrimePrefix T) S c (lowerTrim N T W) hY.1
    (fun p hp => Finset.mem_Icc.mpr ⟨(mem_chenPrimePrefix.mp hp).2.pos,(mem_chenPrimePrefix.mp hp).1⟩)
    hS hc (fun p _ => by
      obtain ⟨ha,hb⟩ := lowerTrim_range_of_le N T p W hY.1.le (smooth_range kappa 6 N p)
      simpa only [abs_of_nonneg ha] using hb)
  rw [max_eq_right hN1] at h
  unfold lowerReserve
  rw [lowerTrim_singleton_eq_prefix (2*N) N T (by omega)]
  have power : (N:ℝ)^(1-kappa)*(N:ℝ)^(kappa/2)=(N:ℝ)^(1-kappa/2) := by
    rw [←Real.rpow_add hn]; congr 1; ring
  have hlog := Real.log_nonneg hN1
  calc
    _ ≤ (3*(N:ℝ)^(1-kappa))*(C*(N:ℝ)^(kappa/2)+4*(1+Real.log (N:ℝ))) :=
      h.trans (mul_le_mul_of_nonneg_right hY.2 (by positivity))
    _ = 3*C*(N:ℝ)^(1-kappa/2)+12*(N:ℝ)^(1-kappa)+12*(N:ℝ)^(1-kappa)*Real.log (N:ℝ) := by
      linear_combination 3*C*power
    _ ≤ _ := by simp only [pow_zero,pow_one,mul_one] at h1 h2 h3; linarith only [h1,h2,h3]

private theorem upper_paid (kappa eta : ℝ) (hu : 0<eta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ (S : Finset ℕ) (c : ℕ→ℝ), S ⊆ Finset.Icc 1 N →
      (∀ d∈S, |c d|≤1) → |upperReserve kappa 6 N S c| ≤ eta*singularNormalization N := by
  filter_upwards [eventually_log_window_cost_le 3,p5z_eventually_logCube_le_singularNormalization 40 eta hu,
    eventually_ge_atTop (4:ℕ)] with N hwin hfee hN
  intro hev S c hS hc
  let T := originalLowerCut kappa N
  let W := smoothNatural kappa 6 N
  let D := upperWidth 6 N
  let E := endpointCarrier (2*N) N D
  have hw := hwin D (upperWidth_le_original_endpoint 6 (by omega))
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hlog := Real.log_nonneg hn
  have hDlog : Real.log (D:ℝ)≤Real.log (N:ℝ) := by
    by_cases hz : D=0
    · simpa [hz] using hlog
    · exact Real.log_le_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)) (Nat.cast_le.mpr hw.1)
  have hE (p : ℕ) (hp : p∈E) : p≠N ∧ distance N p≤D := by
    obtain ⟨hprime,hD⟩ := Finset.mem_filter.mp hp
    exact ⟨fun h => (chen_not_prime_of_even_four_le hev hN) (h ▸ (mem_chenPrimePrefix.mp hprime).2),hD⟩
  have agree := sharp_eq_patched_off_endpoint (2*N) N D T W
    (fun p _ ht hp => original_middle (by omega) kappa 6 p ht (by omega))
    (fun p _ hp => original_upper_tail (by omega) kappa 6 p hp)
  have hab := abs_signed_primitive_endpoint_le E S c (fun p => sharp N p-patched N T W p) N D hE hc
    (fun p _ => abs_sharp_sub_patched_le_one N T p W (smooth_range kappa 6 N p))
  have hrec : (∑ d∈S,|c d|/(d.totient:ℝ)) ≤ 4*(1+Real.log (N:ℝ)) := by
    apply (Finset.sum_le_sum (fun d hd => div_le_div_of_nonneg_right (hc d hd) (Nat.cast_nonneg _))).trans
    simpa only [max_eq_right hn] using sum_reciprocal_totient_subset_le_log S N hS
  have hsum := (sum_divisors_card_le_log D).trans
    (mul_le_mul_of_nonneg_left (add_le_add_left hDlog 1) (Nat.cast_nonneg _))
  unfold upperReserve
  rw [singleton_test_difference_eq_endpoint (2*N) N E S c (sharp N) (patched N T W)
    (Finset.filter_subset _ _) agree]
  apply hab.trans
  have hprod := mul_le_mul (endpoint_card_le E N D hE) hrec (by positivity) (by positivity)
  have htwo := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2)
  exact (show _ ≤ 10*(D:ℝ)*(1+Real.log (N:ℝ)) by linarith only [hprod,htwo]).trans (hw.2.trans hfee)

/-- The true sharp middle is within an arbitrary reserve of the original
smooth one-prime primitive discrepancy on the entire high-rank carrier. -/
theorem eventually_smooth (kappa eta : ℝ) (hk : 0<kappa) (hk1 : kappa<1) (hu : 0<eta) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ P : Params, P.N=N → 0≤P.e → 0<P.omega →
      P.ell<1/1000 → P.ell+P.T*(J0 P.omega : ℝ)<1/1000 →
      |middle N (Q P.omega N) P.rho -
        Part3.primeProductSignedError 1 (2*N) N P.S P.rho (fullSmoothWeight kappa 6 N)| ≤
        eta*singularNormalization N := by
  filter_upwards [P1OriginalSingletonMiddleRank.eventually_primitive (eta/3) (by positivity),
    lower_paid kappa (eta/3) hk hk1 (by positivity),upper_paid kappa (eta/3) (by positivity),
    eventually_ge_atTop (2:ℕ)] with N hmid hlo hhi hN
  intro hev P hPN he ho hell ht
  subst N
  have H := hmid P rfl he ho hell ht
  have hh (d : ℕ) (hd : d∈live P) := live_data P (by omega) he ho hell ht hd
  have hl := hlo (live P) P.rho (fun d hd => (hh d hd).1) (fun d hd => (hh d hd).2.2.2)
  have hr := hhi hev (live P) P.rho (fun d hd => (hh d hd).1) (fun d hd => (hh d hd).2.2.2)
  have replace (T : ℕ) (W : ℕ→ℝ) :
      Part3.primeProductSignedError 1 T P.N (live P) P.rho (P5S1SingletonPP.singletonWeight T W) =
      Part3.primeProductSignedError 1 T P.N P.S P.rho (P5S1SingletonPP.singletonWeight T W) := by
    simp only [P5S1SingletonPP.primeProductSignedError_singleton_eq]
    exact read_live P _
  have heq := original_source_exact_reserves kappa 6 P.N (live P) P.rho
  rw [replace,show Part3.primeProductSignedError 1 (2*P.N) P.N (live P) P.rho (fullSmoothWeight kappa 6 P.N) =
    Part3.primeProductSignedError 1 (2*P.N) P.N P.S P.rho (fullSmoothWeight kappa 6 P.N) from replace _ _] at heq
  obtain ⟨h0,h1⟩ := abs_le.mp H
  obtain ⟨l0,l1⟩ := abs_le.mp hl
  obtain ⟨r0,r1⟩ := abs_le.mp hr
  exact abs_le.mpr ⟨by linarith only [h0,l0,r0,heq],by linarith only [h1,l1,r1,heq]⟩

end
end ImbalancedChen.P1OriginalSingletonMiddleWeight
