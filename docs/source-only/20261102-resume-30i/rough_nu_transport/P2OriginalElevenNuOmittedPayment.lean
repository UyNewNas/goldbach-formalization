import ImbalancedChen.P2OriginalElevenNuDensityEnvelope
import ImbalancedChen.P2OriginalElevenActualOmittedMeanPayment
import ImbalancedChen.ActualSmallRoughAttachment

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Transport H's actual signed omitted-density and exact coprime-mean
payments to D=N^nu, without changing z, commonQ, deltaRho or normalization.
The entire actual AP count remains an explicit unpaid term.
-/
namespace ImbalancedChen.P2OriginalElevenNuOmittedPayment
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open Certificates.P2OriginalSixthElevenLogSemantics
open P5OriginalCommonRefinedConstructor P2OriginalElevenCompactGatedPolicy
open P2OriginalElevenActualDifferenceLocalization P2OriginalElevenLocalizedFullQDifference
open P2OriginalElevenFullModulusOmittedCover P2OriginalElevenAttachedOmittedDensity
open P2OriginalElevenPaidCoverDensity P2OriginalElevenActualOmittedMeanPayment
open P2OriginalElevenNuDensityEnvelope

/-- A genuinely active delta has a small factor below the ACTUAL beta
level and a rough factor on the ORIGINAL union carrier.  Large zero-
weight small divisors in commonQ are not mistaken for active support. -/
theorem actual_delta_nu_ne_zero_factors (d : OriginalData) (n N cap : ℕ)
    (nu epsilon r : ℝ) {q : ℕ}
    (hq : deltaRho d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
      ((N : ℝ)^(nu*epsilon)) q ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap ((N : ℝ)^(nu*epsilon^2)),
      ∃ b ∈ commonRough d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r),
        q = a*b ∧ (a : ℝ) < (N : ℝ)^(nu*epsilon) := by
  let w := (N : ℝ)^(nu*epsilon^2)
  let z := (N : ℝ)^r
  let L := (N : ℝ)^(nu*epsilon)
  by_cases hn : actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L q = 0
  · have ho : rho d N cap w z L q ≠ 0 := by
      intro ho
      exact hq (by change _-_ = 0; rw [hn,ho]; ring)
    change actualSmallRoughRho ((policy8 d (N : ℝ)) false) N cap w z L q ≠ 0 at ho
    obtain ⟨a,ha,b,hb,hq,hL,hc⟩ := actualSmallRoughRho_ne_zero_factors _ N cap w z L ho
    exact ⟨a,ha,b,Finset.mem_union_right _ hb,hq,hL⟩
  · obtain ⟨a,ha,b,hb,hq,hL,hc⟩ := actualSmallRoughRho_ne_zero_factors _ N cap w z L hn
    exact ⟨a,ha,b,Finset.mem_union_left _ hb,hq,hL⟩

/-- H's exact finite owner partition, now with the actual nu schedule.
Only positive reciprocal-totient masses are compared by inclusion. -/
theorem exists_paid_cover_nu_density_payment (nu epsilon r eta : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (her : nu*epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ (ret : List ℕ → Bool) (S : Finset ℕ),
        S ⊆ fixedRoughSupport ret N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) →
        (∀ b ∈ S, PaidDivisorCover n N b) →
        |restrictedDensity ret N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^(nu*epsilon)) S| < eta*(singularSeries N/Real.log (N : ℝ)) := by
  let k : ℝ := allCells.toFinset.card
  have hk : 0 < k+1 := by dsimp [k]; positivity
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_full_attached_nu_density_payment nu epsilon r (eta/(k+1))
    hnu he he8 her (div_pos heta hk)
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap ret S hS hcover
  have hN2 := hN₀.trans hN
  have hnorm : 0 < singularSeries N/Real.log (N : ℝ) :=
    div_pos (singularSeries_pos N) (Real.log_pos (by exact_mod_cast (show 1 < N by omega)))
  rw [restrictedDensity_eq_sum_owned ret n N cap _ _ _ S hS]
  calc
    _ ≤ ∑ c ∈ allCells.toFinset,
        |restrictedDensity ret N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^(nu*epsilon)) (ownedRough n N S c)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _c ∈ allCells.toFinset, (eta/(k+1))*(singularSeries N/Real.log (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro c hc
      exact (h n hn N hN hEven cap hcap ret c _
        (ownedRough_subset_cover ret n N cap _ _ S hS hcover c)).le
    _ = k*((eta/(k+1))*(singularSeries N/Real.log (N : ℝ))) := by simp [k]
    _ < eta*(singularSeries N/Real.log (N : ℝ)) := by
      have hs : k*(eta/(k+1)) < eta := by
        rw [← mul_div_assoc]
        apply (div_lt_iff₀ hk).2
        nlinarith
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right hs hnorm

/-- Same two actual policy restrictions, with each original beta sign
chosen before subtraction.  The original z and full commonQ are retained. -/
theorem exists_actual_delta_nu_density_payment (nu epsilon r eta : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (her : nu*epsilon^2 ≤ r) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
        |physicalDensitySum (commonQ d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r))
          (deltaRho d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
            ((N : ℝ)^(nu*epsilon)))| < eta*(singularSeries N/Real.log (N : ℝ)) := by
  obtain ⟨n₀,N₀,hN₀,h⟩ := exists_paid_cover_nu_density_payment nu epsilon r (eta/2)
    hnu he he8 her (half_pos heta)
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap d
  have hN2 := hN₀.trans hN
  rw [actual_delta_density_eq_paid_sides d n N cap (by omega)]
  have hs (ret : List ℕ → Bool) := h n hn N hN hEven cap hcap ret
    (paidSide ret n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r))
    (Finset.filter_subset _ _) (fun b hb => (Finset.mem_filter.mp hb).2)
  exact (abs_sub _ _).trans_lt (by linarith [
    hs ((compactPolicy8 d n (N : ℝ)) false),hs ((policy8 d (N : ℝ)) false)])

/-- The original source roughness gap is in r, NOT nu*r: the rough
ceiling z=N^r has not been rescaled.  A single threshold pays both the
source mass and its rounded coprimality gate. -/
theorem exists_actual_omitted_nu_mean_payment (nu epsilon r b kappa eta : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (her : nu*epsilon^2 ≤ r) (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hgap : r < (1-kappa)*(b/(1+b))) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
        |actualDeltaMean d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^(nu*epsilon)) b (manuscriptHalfProductCutoff kappa N)| <
          eta*singularNormalization N := by
  let J : ℝ := Real.log (1/b)+1
  have hlogb : 0 < Real.log (1/b) := Real.log_pos ((one_lt_div hb).mpr hb1)
  have hJ : 0 < J := by dsimp [J]; linarith
  obtain ⟨n₀,D,hD,hpay⟩ := exists_actual_delta_nu_density_payment nu epsilon r (eta/J)
    hnu he he8 her (div_pos heta hJ)
  have hr : 0 ≤ r := (mul_nonneg hnu.le (sq_nonneg epsilon)).trans her
  have hmass : ∀ᶠ N : ℕ in atTop,
      ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) /
        ((N : ℝ)/Real.log (N : ℝ)) < J :=
    (tendsto_realHalfProductSource_manuscriptCutoff_mass_of_suppliers hb hb1 hkappa).eventually
      (gt_mem_nhds (by dsimp [J]; linarith))
  obtain ⟨M,hM⟩ := eventually_atTop.mp
    (hmass.and (eventually_manuscript_sieve_gate hb hr hgap))
  refine ⟨n₀,max D M,hD.trans (le_max_left _ _),?_⟩
  intro n hn N hN hEven cap hcap d
  have hND := (le_max_left D M).trans hN
  have hNM := (le_max_right D M).trans hN
  have hN2 := hD.trans hND
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hscale : 0 < (N : ℝ)/Real.log (N : ℝ) :=
    div_pos (zero_lt_one.trans hN1) (Real.log_pos hN1)
  obtain ⟨hm,hT,hgate⟩ := hM N hNM
  have hsource : ((realHalfProductSource b N (manuscriptHalfProductCutoff kappa N)).card : ℝ) ≤
      J*((N : ℝ)/Real.log (N : ℝ)) := (div_le_iff₀ hscale).mp hm.le
  have hdensity := hpay n hn N hND hEven cap hcap d
  have hwz := Real.rpow_le_rpow_of_exponent_le hN1.le her
  rw [actualDeltaMean_eq_mass_mul_density d n N cap _ _ _ b _ hb hT hwz hgate,
    abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ (J*((N : ℝ)/Real.log (N : ℝ))) *
        |physicalDensitySum (commonQ d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r))
          (deltaRho d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
            ((N : ℝ)^(nu*epsilon)))| :=
      mul_le_mul_of_nonneg_right hsource (abs_nonneg _)
    _ < (J*((N : ℝ)/Real.log (N : ℝ))) *
        ((eta/J)*(singularSeries N/Real.log (N : ℝ))) :=
      mul_lt_mul_of_pos_left hdensity (mul_pos hJ hscale)
    _ = eta*singularNormalization N := by
      rw [← sourceMassScale_mul_densityScale N]
      field_simp [hJ.ne'] <;> ring

/-- Both original AP functionals are unchanged.  The true same-Q count
is displayed on the right and is not an analytic premise or a paid term. -/
theorem exists_two_actual_nu_AP_count_reduction (nu epsilon r b kappa eta : ℝ)
    (hnu : 0 < nu) (he : 0 < epsilon) (he8 : epsilon < 1/8)
    (her : nu*epsilon^2 ≤ r) (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hgap : r < (1-kappa)*(b/(1+b))) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
        let w := (N : ℝ)^(nu*epsilon^2)
        let z := (N : ℝ)^r
        let L := (N : ℝ)^(nu*epsilon)
        let T := manuscriptHalfProductCutoff kappa N
        |realPhysicalDistributionError b N T
            (actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
            (actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L) -
          realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L)| <
          |actualDeltaCount d n N cap w z L b T|+eta*singularNormalization N := by
  obtain ⟨n₀,N₀,hN₀,hpay⟩ := exists_actual_omitted_nu_mean_payment nu epsilon r b kappa eta
    hnu he he8 her hb hb1 hkappa hgap heta
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap d
  dsimp only
  have hid := delta_test_eq_two_original_sources d n N cap
    ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^(nu*epsilon))
    (fun q => realHalfProductCongruenceMass b N (manuscriptHalfProductCutoff kappa N) q -
      realHalfProductCoprimeMass b N (manuscriptHalfProductCutoff kappa N) q/(Nat.totient q : ℝ))
  change |(_ : ℝ)-_| < _
  rw [← show realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
      (commonQ d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r))
      (deltaRho d n N cap ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^r)
        ((N : ℝ)^(nu*epsilon))) = _ from hid,
    actual_AP_eq_count_sub_mean]
  exact (abs_sub _ _).trans_lt (add_lt_add_left (hpay n hn N hN hEven cap hcap d) _)

end
end ImbalancedChen.P2OriginalElevenNuOmittedPayment
