import ImbalancedChen.P2GammaJointMotherLogSaving
import ImbalancedChen.P2GammaActualUpperLowRankReduction

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
The original joint LOW-RANK source now has arbitrary absolute logarithmic
accuracy after subtracting only its explicitly retained empty-word lane.
There is no selectorMass or head-overlap factor. The actual physical
modulus carrier is restored, and the full compact coefficient is split
using its EXISTING high-rank remainder. Neither high-rank PP nor the empty
lane nor common causal physical-Q/positive-Theta is claimed solved.
-/
namespace ImbalancedChen.P2GammaActualJointLowRankLogSaving
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaJointMotherLogSaving P2GammaActualUpperLowRankReduction
open P2GammaRetainedSameRhoRows P2GammaRetainedSameRhoMother
open P2GammaJointRetainedReduction P2GammaJointDiscardedPayment
open P2GammaJointUpperPayment P2GammaOrderingStripPayment
open P2GammaCompleteProductTrimPayment P2GammaChosenLogGridBudget
open P5OriginalU5CausalFinite (pairSupport)

/-- Both true suppliers are invoked on precisely the SAME width and grid.
The height is fixed before N; all later bounded nonnegative selectors are
covered without a lower mass assumption or normalization by their mass. -/
theorem eventually_original_joint_low_rank_logAccuracy
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      |originalJointGammaError N (Finset.Icc 1 N)
          (upperRho N nu epsilon retain cap) sigma-
        emptyJointError N (Finset.Icc 1 N)
          (upperRho N nu epsilon retain cap) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let B := orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A
  have hB : 0 < B := by dsimp [B,orderMeshExponent]; omega
  have hk1 : kappa < 1 := by linarith
  filter_upwards [eventually_joint_head_logAccuracy A B hB kappa hk0.le hk height
      hheight.le (eta/2) (half_pos heta),
    eventually_originalJointGamma_retained_reduction height hheight A kappa hk0 hk1
      (eta/2) (half_pos heta)] with N hhead hdiscard
  intro nu epsilon hnu hnu1 heps heps1 retain cap sigma hs
  let rho := upperRho N nu epsilon retain cap
  let Q := Finset.Icc 1 N
  let T := (N : ℝ)^(1-kappa)
  let H := 2*T
  let δ := chosenWidth A N
  let K := chosenGrid A N
  have hsig : ∀ t ∈ pairSupport N,|sigma t| ≤ height := by
    intro t ht
    rw [abs_of_nonneg (hs t ht).1]
    exact (hs t ht).2
  have hh := hhead nu epsilon hnu hnu1 heps heps1 retain cap Q sigma hsig
  have hh' : |headJointError N Q rho sigma H δ K| ≤
      (eta/2)*(N : ℝ)/(Real.log (N : ℝ))^A := by
    simpa only [rho,H,T,δ,K,chosenWidth,chosenGrid,gridLength,B] using hh
  have hd := hdiscard Q rho sigma (by intro q hq; exact hq)
    (fun q hq => upperRho_abs_le_one N nu epsilon retain cap q) hs
  have heq : originalJointGammaError N Q rho sigma-emptyJointError N Q rho sigma T =
      headJointError N Q rho sigma H δ K+
        (originalJointGammaError N Q rho sigma-
          originalJointRetainedError N Q rho sigma T H δ K) := by
    rw [jointRetained_eq_head_add_empty]
    ring
  change |originalJointGammaError N Q rho sigma-emptyJointError N Q rho sigma T| ≤ _
  rw [heq]
  exact (abs_add _ _).trans ((add_le_add hh' hd).trans_eq (by ring))

/-- The low coefficient on the original actualSmallRoughModuli carrier,
not a replacement statement on an auxiliary analytic level. -/
theorem eventually_physical_joint_low_rank_logAccuracy
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (upperRho N nu epsilon retain cap) sigma-
        emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
          (upperRho N nu epsilon retain cap) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_original_joint_low_rank_logAccuracy height hheight A
    kappa hk0 hk eta heta,eventually_ge_atTop (2 : ℕ)] with N hN hN2
  intro nu epsilon hnu hnu1 heps heps1 retain cap sigma hs
  rw [originalJointGamma_upperRho_actual_moduli hN2 hnu hnu1 heps heps1,
    emptyJointError_upperRho_actual_moduli hN2 hnu hnu1 heps heps1]
  exact hN nu epsilon hnu hnu1 heps heps1 retain cap sigma hs

/-- Actual compact-policy instance. The high coefficient is the original
remainingRho, not an error-defined surrogate. All three functionals retain
the ORIGINAL physical carrier. This strengthens the prior terminal by
removing its selectorMass term, but leaves the two displayed lanes unpaid. -/
theorem eventually_actualCompact_joint_logAccuracy
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (e h : ℝ) (m cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (fullUpperRho N nu epsilon retain cap) sigma-
        originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (highUpperRho N nu epsilon retain cap) sigma-
        emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
          (upperRho N nu epsilon retain cap) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_physical_joint_low_rank_logAccuracy height hheight A
    kappa hk0 hk eta heta] with N hN
  intro nu epsilon hnu hnu1 heps heps1 e h m cap sigma hs
  dsimp only
  rw [originalJointGamma_fullUpper_split,add_sub_cancel_right]
  exact hN nu epsilon hnu hnu1 heps heps1
    (actualExtendedThirdCompactUpperPolicy e h m N false) cap sigma hs

end
end ImbalancedChen.P2GammaActualJointLowRankLogSaving
