import ImbalancedChen.P2OriginalElevenPaidCoverDensity
import ImbalancedChen.ActualUpperCountingInputs

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

A genuine analytic payment of the EXACT COPRIME-MEAN COMPONENT of G's
same-Q omitted-source AP difference, on singularNormalization N.  The
literal source mass is supplied by PNT/Mertens and the coprime mask is
removed by the proved source roughness gate.  The congruence-count term
is left visible.  This is not an AP discrepancy bound or a fine compiler.
-/
namespace ImbalancedChen.P2OriginalElevenActualOmittedMeanPayment
noncomputable section
open Classical Filter
open scoped BigOperators Topology
open P5OriginalCommonRefinedConstructor P2OriginalElevenCompactGatedPolicy
open P2OriginalElevenLocalizedFullQDifference P2OriginalElevenPaidCoverDensity

def actualDeltaMean (d : OriginalData) (n N cap : ℕ) (w z L b T : ℝ) : ℝ :=
  ∑ q ∈ commonQ d n N cap w z, deltaRho d n N cap w z L q *
    (realHalfProductCoprimeMass b N T q / (Nat.totient q : ℝ))

def actualDeltaCount (d : OriginalData) (n N cap : ℕ) (w z L b T : ℝ) : ℝ :=
  ∑ q ∈ commonQ d n N cap w z, deltaRho d n N cap w z L q *
    realHalfProductCongruenceMass b N T q

theorem commonQ_dvd_sieveProduct (d : OriginalData) (n N cap : ℕ) (w z : ℝ)
    (hwz : w ≤ z) {q : ℕ} (hq : q ∈ commonQ d n N cap w z) :
    q ∣ sieveProduct N (Nat.ceil z) := by
  obtain ⟨⟨e,r⟩,her,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨he,hr⟩ := Finset.mem_product.mp her
  rcases Finset.mem_union.mp hr with hr | hr
  · exact actualSmallRoughModuli_dvd_sieveProduct_ceil
      ((compactPolicy8 d n (N : ℝ)) false) N cap w z hwz
      (Finset.mem_image.mpr ⟨(e,r),Finset.mem_product.mpr ⟨he,hr⟩,rfl⟩)
  · exact actualSmallRoughModuli_dvd_sieveProduct_ceil
      ((policy8 d (N : ℝ)) false) N cap w z hwz
      (Finset.mem_image.mpr ⟨(e,r),Finset.mem_product.mpr ⟨he,hr⟩,rfl⟩)

/-- This is the exact original mean, not a replacement by an unproved
reference centre. Every displayed full q is covered by the roughness gate. -/
theorem actualDeltaMean_eq_mass_mul_density (d : OriginalData) (n N cap : ℕ)
    (w z L b T : ℝ) (hb : 0 < b) (hT : 0 < T) (hwz : w ≤ z)
    (hgate : (Nat.ceil z : ℝ) ≤ T^(b/(1+b))) :
    actualDeltaMean d n N cap w z L b T =
      ((realHalfProductSource b N T).card : ℝ) *
        physicalDensitySum (commonQ d n N cap w z) (deltaRho d n N cap w z L) := by
  unfold actualDeltaMean physicalDensitySum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [realHalfProductCoprimeMass_eq_card_of_gate hb hT hgate
    (commonQ_dvd_sieveProduct d n N cap w z hwz hq)]
  ring

theorem actual_AP_eq_count_sub_mean (d : OriginalData) (n N cap : ℕ)
    (w z L b T : ℝ) :
    realPhysicalDistributionError b N T (commonQ d n N cap w z)
        (deltaRho d n N cap w z L) =
      actualDeltaCount d n N cap w z L b T - actualDeltaMean d n N cap w z L b T := by
  simp only [realPhysicalDistributionError,actualDeltaCount,actualDeltaMean,
    mul_sub,Finset.sum_sub_distrib]

/-- Fix beta/rough parameters and the original source exponent first.
One finite omission choice works for all larger n, all sufficiently large
even N, every cap and every original common policy datum.  No AP estimate,
final density estimate or source-mass estimate is an input hypothesis. -/
theorem exists_actual_omitted_mean_payment (epsilon r b kappa eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r)
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hgap : r < (1-kappa)*(b/(1+b))) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
        |actualDeltaMean d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r)
          ((N : ℝ)^epsilon) b (manuscriptHalfProductCutoff kappa N)| <
          eta * singularNormalization N := by
  let J : ℝ := Real.log (1/b)+1
  have hlogb : 0 < Real.log (1/b) := Real.log_pos ((one_lt_div hb).mpr hb1)
  have hJ : 0 < J := by dsimp [J]; linarith
  obtain ⟨n₀,D,hD,hpay⟩ := exists_actual_delta_density_payment epsilon r (eta/J)
    he he8 her (div_pos heta hJ)
  have hr : 0 ≤ r := (sq_nonneg epsilon).trans her
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
        |physicalDensitySum (commonQ d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r))
          (deltaRho d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon))| :=
      mul_le_mul_of_nonneg_right hsource (abs_nonneg _)
    _ < (J*((N : ℝ)/Real.log (N : ℝ))) *
        ((eta/J)*(singularSeries N/Real.log (N : ℝ))) :=
      mul_lt_mul_of_pos_left hdensity (mul_pos hJ hscale)
    _ = eta*singularNormalization N := by
      rw [← sourceMassScale_mul_densityScale N]
      field_simp [hJ.ne']
      <;> ring

/-- Same two actual AP sources as G, now with their mean term paid.
The remaining actual count sum is explicit on the right.  In particular
this conclusion does NOT bound that count by the displayed reserve. -/
theorem exists_two_actual_AP_count_reduction (epsilon r b kappa eta : ℝ)
    (he : 0 < epsilon) (he8 : epsilon < 1/8) (her : epsilon^2 ≤ r)
    (hb : 0 < b) (hb1 : b < 1) (hkappa : 0 < kappa)
    (hgap : r < (1-kappa)*(b/(1+b))) (heta : 0 < eta) :
    ∃ n₀ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ n, n₀ ≤ n → ∀ N, N₀ ≤ N → Even N →
      ∀ cap, (N : ℝ)^r ≤ (cap : ℝ) → ∀ d : OriginalData,
        let w := (N : ℝ)^(epsilon^2)
        let z := (N : ℝ)^r
        let L := (N : ℝ)^epsilon
        let T := manuscriptHalfProductCutoff kappa N
        |realPhysicalDistributionError b N T
            (actualSmallRoughModuli ((compactPolicy8 d n (N : ℝ)) false) N cap w z)
            (actualSmallRoughRho ((compactPolicy8 d n (N : ℝ)) false) N cap w z L) -
          realPhysicalDistributionError b N T (moduli d N cap w z) (rho d N cap w z L)| <
          |actualDeltaCount d n N cap w z L b T| + eta*singularNormalization N := by
  obtain ⟨n₀,N₀,hN₀,hpay⟩ := exists_actual_omitted_mean_payment epsilon r b kappa eta
    he he8 her hb hb1 hkappa hgap heta
  refine ⟨n₀,N₀,hN₀,?_⟩
  intro n hn N hN hEven cap hcap d
  dsimp only
  have hid := delta_test_eq_two_original_sources d n N cap
    ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)
    (fun q => realHalfProductCongruenceMass b N (manuscriptHalfProductCutoff kappa N) q -
      realHalfProductCoprimeMass b N (manuscriptHalfProductCutoff kappa N) q/(Nat.totient q : ℝ))
  change |(_ : ℝ) - _| < _
  rw [← show realPhysicalDistributionError b N (manuscriptHalfProductCutoff kappa N)
      (commonQ d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r))
      (deltaRho d n N cap ((N : ℝ)^(epsilon^2)) ((N : ℝ)^r) ((N : ℝ)^epsilon)) = _ from hid,
    actual_AP_eq_count_sub_mean]
  exact (abs_sub _ _).trans_lt (add_lt_add_left (hpay n hn N hN hEven cap hcap d) _)

end
end ImbalancedChen.P2OriginalElevenActualOmittedMeanPayment
