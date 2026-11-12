import ImbalancedChen.P2GammaActualEmptyMotherSource
import ImbalancedChen.P2GammaActualJointLowRankLogSaving
import ImbalancedChen.P2GammaSelectedPhysicalTheta

/-! Insert the occurrence-level equality at the original physical upper
moduli and on selected old-pair families. The analytic bounds are the
previous log-saving theorems, with their original quantifier order.
-/

namespace ImbalancedChen.P2GammaActualEmptyMotherPhysical
noncomputable section

open scoped Classical BigOperators Topology
open Filter
open P2GammaActualEmptyMotherSource
open P2GammaRetainedSameRhoMother (emptyJointError)
open P2GammaRetainedSameRhoRows (upperRho)
open P2GammaActualUpperLowRankReduction (physicalUpperModuli fullUpperRho)
open P2GammaRankScaledUpperSource (rankUpperRho rankRemainder)
open P2GammaJointRetainedReduction (originalJointGammaError)
open P2GammaSelectedPhysicalTheta (Pair selectedEmpty selectedGamma selectedResidual)
open P5OriginalU5CausalFinite (pairSupport)

/-- All three signed integer coefficients are tested on the same actual
small/rough physical carrier, with their full beta attachment. -/
theorem physical_full_rank_remainder_empty_zero (N : ℕ) (nu epsilon : ℝ)
    (retain : List ℕ → Bool) (cap k : ℕ) (sigma : Pair → ℝ) (T : ℝ) :
    let Q := physicalUpperModuli N nu epsilon retain cap
    emptyJointError N Q (fullUpperRho N nu epsilon retain cap) sigma T = 0 ∧
    emptyJointError N Q (rankUpperRho N nu epsilon retain cap k) sigma T = 0 ∧
    emptyJointError N Q (rankRemainder N nu epsilon retain cap k) sigma T = 0 := by
  exact ⟨original_empty_joint_zero _ _ _ _ _,
         original_empty_joint_zero _ _ _ _ _,
         original_empty_joint_zero _ _ _ _ _⟩

/-- Applies also to a root-Q fibre or its full set-theoretic complement,
for the very same signed rho and arbitrary outer weights. -/
theorem selected_empty_zero (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (S : Finset Pair) (sigma : Pair → ℝ) :
    selectedEmpty N Q rho T S sigma = 0 := by
  simp only [selectedEmpty, original_empty_pair_zero, mul_zero, Finset.sum_const_zero]

theorem selected_residual_eq_gamma (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ)
    (T : ℝ) (S : Finset Pair) (sigma : Pair → ℝ) :
    selectedResidual N Q rho T S sigma = selectedGamma N Q rho S sigma := by
  rw [selectedResidual, selected_empty_zero, sub_zero]

/-- Actual upper rough rank at most two on the full physical carrier. -/
theorem eventually_physical_rank_two_original_gamma
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (sigma : Pair → ℝ),
      (∀ t ∈ pairSupport N, 0 ≤ sigma t ∧ sigma t ≤ height) →
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (upperRho N nu epsilon retain cap) sigma| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  simpa only [original_empty_joint_zero, sub_zero] using
    P2GammaActualJointLowRankLogSaving.eventually_physical_joint_low_rank_logAccuracy
      height hheight A kappa hk0 hk eta heta

/-- Higher ranks within the inherited complete-level range. The threshold
precedes k, the later coefficient, its physical moduli and the selector. -/
theorem eventually_physical_admitted_rank_original_gamma
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ nu epsilon : ℝ, 0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (sigma : Pair → ℝ),
      (∀ t ∈ pairSupport N, 0 ≤ sigma t ∧ sigma t ≤ height) →
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (rankUpperRho N nu epsilon retain cap k) sigma| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  simpa only [original_empty_joint_zero, sub_zero] using
    P2GammaRankScaledUpperLogSaving.eventually_rank_physical_logAccuracy
      height hheight A kappa hk0 hk eta heta

/-- The compact physical source retains the original ranks above k as
the separately identified remainder on exactly the same moduli. -/
theorem eventually_compact_full_sub_rank_remainder
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, ∀ nu epsilon : ℝ, 0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (e h : ℝ) (m cap : ℕ) (sigma : Pair → ℝ),
      (∀ t ∈ pairSupport N, 0 ≤ sigma t ∧ sigma t ≤ height) →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (fullUpperRho N nu epsilon retain cap) sigma -
        originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (rankRemainder N nu epsilon retain cap k) sigma| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  simpa only [original_empty_joint_zero, sub_zero] using
    P2GammaRankScaledUpperLogSaving.eventually_actualCompact_rank_logAccuracy
      height hheight A kappa hk0 hk eta heta

end
end ImbalancedChen.P2GammaActualEmptyMotherPhysical
