import ImbalancedChen.P2GammaRankScaledUpperSource

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual rank-k original physical-source endpoint, uniform in k AFTER one
threshold whenever the full exponent fits the explicit complete-level
range. Concrete k=3 and k=4 corollaries discharge that range numerically.
The empty lane and the existing ranks above k remain explicit. Neither
positive-Theta nor an unrestricted enhanced/high-level estimate is claimed.
-/
namespace ImbalancedChen.P2GammaRankScaledUpperLogSaving
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaRankScaledUpperSource P2GammaCompleteLevelMother
open P2GammaActualUpperLowRankReduction P2GammaRetainedSameRhoMother
open P2GammaJointRetainedReduction
open P5OriginalU5CausalFinite (pairSupport)

theorem rankGamma_carrier {N : ℕ} (hN : 1 ≤ N) {kappa nu epsilon : ℝ}
    (hk0 : 0 ≤ kappa) (hnu : 0 ≤ nu) (retain : List ℕ → Bool) (cap k : ℕ)
    (hgap : nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ))
    (sigma : (ℕ × ℕ) → ℝ) :
    originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
      (rankUpperRho N nu epsilon retain cap k) sigma =
    originalJointGammaError N (Finset.Icc 1 N)
      (rankUpperRho N nu epsilon retain cap k) sigma := by
  unfold originalJointGammaError
  apply Finset.sum_congr rfl
  intro t ht
  rw [rankUpper_test_carrier hN hk0 hnu retain cap k hgap]

theorem rankEmpty_carrier {N : ℕ} (hN : 1 ≤ N) {kappa nu epsilon : ℝ}
    (hk0 : 0 ≤ kappa) (hnu : 0 ≤ nu) (retain : List ℕ → Bool) (cap k : ℕ)
    (hgap : nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ))
    (sigma : (ℕ × ℕ) → ℝ) (T : ℝ) :
    emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
      (rankUpperRho N nu epsilon retain cap k) sigma T =
    emptyJointError N (Finset.Icc 1 N)
      (rankUpperRho N nu epsilon retain cap k) sigma T := by
  unfold emptyJointError
  apply Finset.sum_congr rfl
  intro t ht
  apply congrArg (fun z : ℝ => sigma t*z)
  unfold emptyPairError
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs hcs
  by_cases hn : cs=[]
  · simp only [emptyWordError,if_pos hn]
    exact rankUpper_test_carrier hN hk0 hnu retain cap k hgap _
  · simp only [emptyWordError,if_neg hn]

/-- k and nu are chosen AFTER the threshold. All primitive level conditions
are supplied from the original rankRho source; no coefficient norm, support,
conductor or PP estimate is an input to this actual endpoint. -/
theorem eventually_rank_physical_logAccuracy
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (rankUpperRho N nu epsilon retain cap k) sigma-
        emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
          (rankUpperRho N nu epsilon retain cap k) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_complete_original_logAccuracy height hheight A kappa hk0 hk
    eta heta,eventually_ge_atTop (1 : ℕ)] with N hN hN1
  intro k nu epsilon hnu hgap retain cap sigma hs
  rw [rankGamma_carrier hN1 hk0.le hnu retain cap k hgap,
    rankEmpty_carrier hN1 hk0.le hnu retain cap k hgap]
  exact hN (rankUpperRho N nu epsilon retain cap k)
    (rankUpper_completeLevel hN1 hnu retain cap k hgap) sigma hs

/-- Actual compact full coefficient on its original physical carrier.
The complementary term is the pre-existing remainingRho at rank k. -/
theorem eventually_actualCompact_rank_logAccuracy
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa < 1)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ k : ℕ,∀ nu epsilon : ℝ,0 ≤ nu →
      nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) →
      ∀ (e h : ℝ) (m cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (fullUpperRho N nu epsilon retain cap) sigma-
        originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (rankRemainder N nu epsilon retain cap k) sigma-
        emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
          (rankUpperRho N nu epsilon retain cap k) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_rank_physical_logAccuracy height hheight A kappa hk0 hk eta heta]
    with N hN
  intro k nu epsilon hnu hgap e h m cap sigma hs
  dsimp only
  rw [originalJointGamma_rank_split,add_sub_cancel_right]
  exact hN k nu epsilon hnu hgap
    (actualExtendedThirdCompactUpperPolicy e h m N false) cap sigma hs

/-- A concrete rank-three branch beyond k=2. The explicit scalar level
inequality is no longer a caller premise in this corollary. -/
theorem eventually_actualCompact_rank_three
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 37/50 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (e h : ℝ) (m cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (fullUpperRho N nu epsilon retain cap) sigma-
        originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (rankRemainder N nu epsilon retain cap 3) sigma-
        emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
          (rankUpperRho N nu epsilon retain cap 3) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_actualCompact_rank_logAccuracy height hheight A kappa hk0
    (by linarith : kappa < 1) eta heta] with N hN
  intro nu epsilon hnu hcap heps0 heps1 e h m cap sigma hs
  exact hN 3 nu epsilon hnu (by simpa using rank_three_gap hnu hcap heps1 hk)
    e h m cap sigma hs

/-- A concrete rank-four branch. It does not assert the same conclusion
for nu=1 or for the out-of-level enhanced remainder. -/
theorem eventually_actualCompact_rank_four
    (height : ℝ) (hheight : 0 < height) (A : ℕ)
    (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 14/25 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (e h : ℝ) (m cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      let retain := actualExtendedThirdCompactUpperPolicy e h m N false
      |originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (fullUpperRho N nu epsilon retain cap) sigma-
        originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
          (rankRemainder N nu epsilon retain cap 4) sigma-
        emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
          (rankUpperRho N nu epsilon retain cap 4) sigma ((N : ℝ)^(1-kappa))| ≤
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := by
  filter_upwards [eventually_actualCompact_rank_logAccuracy height hheight A kappa hk0
    (by linarith : kappa < 1) eta heta] with N hN
  intro nu epsilon hnu hcap heps0 heps1 e h m cap sigma hs
  exact hN 4 nu epsilon hnu (by simpa using rank_four_gap hnu hcap heps1 hk)
    e h m cap sigma hs

end
end ImbalancedChen.P2GammaRankScaledUpperLogSaving
