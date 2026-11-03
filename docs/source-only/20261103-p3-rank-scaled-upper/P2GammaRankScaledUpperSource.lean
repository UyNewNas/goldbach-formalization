import ImbalancedChen.P2GammaCompleteLevelMother

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Supply the primitive complete level for the EXISTING rankRho at every
rough modulus rank k, retaining the full small beta attachment. The
explicit scalar gap is a proved source admissibility range, not an
estimate for the out-of-range enhanced/high-level branch.
-/
namespace ImbalancedChen.P2GammaRankScaledUpperSource
noncomputable section
open scoped Classical BigOperators
open P4BPositiveUpperLowRankClass
open P2GammaCompleteLevelJointRows P2GammaCompleteLevelMother
open P2GammaActualUpperLowRankReduction P2GammaRetainedSameRhoRows
open P2GammaRetainedSameRhoMother P2GammaJointRetainedReduction

/-- Exactly the existing actual coefficient; only the rank parameter varies. -/
def rankUpperRho (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap k q : ℕ) : ℝ :=
  rankRho retain N cap ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) k q

/-- The old complementary coefficient, not a desired-error subtraction. -/
def rankRemainder (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap k q : ℕ) : ℝ :=
  remainingRho retain N cap ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) k q

theorem rank_two_eq (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) :
    rankUpperRho N nu epsilon retain cap 2 = upperRho N nu epsilon retain cap := rfl

theorem remainder_two_eq (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) :
    rankRemainder N nu epsilon retain cap 2 = highUpperRho N nu epsilon retain cap := rfl

/-- The source's active support includes the FULL beta factor before its
exponent is compared with the analytic complete-scale cap. -/
theorem rankUpper_active_support {N : ℕ} (hN : 1 ≤ N) {nu : ℝ} (hnu : 0 ≤ nu)
    (epsilon : ℝ) (retain : List ℕ → Bool) (cap k : ℕ) {q : ℕ}
    (hq : rankUpperRho N nu epsilon retain cap k q ≠ 0) :
    0 < q ∧ Squarefree q ∧ N.Coprime q ∧
      (q : ℝ) < (N : ℝ)^(nu*((k : ℝ)*(19/96 : ℝ)+epsilon)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨hp,hsq,hcop,hlevel⟩ := rankRho_complete_support retain N cap
    ((N : ℝ)^(nu*epsilon^2)) ((N : ℝ)^(nu*(19/96 : ℝ)))
    ((N : ℝ)^(nu*epsilon)) k
    (Real.one_le_rpow hN1 (mul_nonneg hnu (by norm_num))) hq
  refine ⟨hp,hsq,hcop.symm,?_⟩
  simpa only [attachment_rank_power (by omega : 0 < N) nu (19/96) epsilon k] using hlevel

/-- The complete-level supplier is proved for the actual integer rho.
The rank k is not an energy/mother moment order. No PP bound is a premise. -/
theorem rankUpper_completeLevel {N : ℕ} (hN : 1 ≤ N) {nu epsilon kappa : ℝ}
    (hnu : 0 ≤ nu) (retain : List ℕ → Bool) (cap k : ℕ)
    (hgap : nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ)) :
    CompleteLevel N kappa (rankUpperRho N nu epsilon retain cap k) := by
  refine ⟨fun q => rankRho_abs_le_one _ _ _ _ _ _ _ _,?_⟩
  intro q hq
  obtain ⟨hp,hsq,hcop,hbound⟩ := rankUpper_active_support hN hnu epsilon retain cap k hq
  exact ⟨hp,hcop,hbound.le.trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hgap)⟩

/-- A simple uniform sufficient domain, useful even when k varies with N. -/
theorem scaled_rank_gap {nu epsilon kappa : ℝ} {k : ℕ}
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (heps : epsilon ≤ 1/1000)
    (hk : kappa ≤ 1/100) (hscaled : nu*(k : ℝ) ≤ 2) :
    nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) := by
  have he := mul_le_mul_of_nonneg_left heps hnu
  nlinarith

/-- Concrete extensions beyond the old k=2 range; the beta margin is paid. -/
theorem rank_three_gap {nu epsilon kappa : ℝ}
    (hnu : 0 ≤ nu) (hcap : nu ≤ 37/50)
    (heps : epsilon ≤ 1/1000) (hk : kappa ≤ 1/100) :
    nu*((3 : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) := by
  have he := mul_le_mul_of_nonneg_left heps hnu
  nlinarith

theorem rank_four_gap {nu epsilon kappa : ℝ}
    (hnu : 0 ≤ nu) (hcap : nu ≤ 14/25)
    (heps : epsilon ≤ 1/1000) (hk : kappa ≤ 1/100) :
    nu*((4 : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ) := by
  have he := mul_le_mul_of_nonneg_left heps hnu
  nlinarith

theorem rankUpper_active_mem_physical (N : ℕ) (nu epsilon : ℝ)
    (retain : List ℕ → Bool) (cap k : ℕ) {q : ℕ}
    (hq : rankUpperRho N nu epsilon retain cap k q ≠ 0) :
    q ∈ physicalUpperModuli N nu epsilon retain cap := by
  have hm : q ∈ rankModuli retain N cap ((N : ℝ)^(nu*epsilon^2))
      ((N : ℝ)^(nu*(19/96 : ℝ))) k := by
    by_contra hn
    exact hq (by simp only [rankUpperRho,rankRho,if_neg hn])
  exact rankModuli_subset retain N cap _ _ k hm

/-- [1,N] is only an enumeration carrier for this active part. The full
physical carrier and the remaining higher part are not changed. -/
theorem completeLevel_active_mem_target {N : ℕ} (hN : 1 ≤ N) {kappa : ℝ}
    (hk0 : 0 ≤ kappa) {rho : ℕ → ℝ} (hrho : CompleteLevel N kappa rho)
    {q : ℕ} (hq : rho q ≠ 0) : q ∈ Finset.Icc 1 N := by
  obtain ⟨hp,hcop,hbound⟩ := hrho.2 q hq
  have hlast : (N : ℝ)^((1-kappa)*(9/20 : ℝ)) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hN) (show (1-kappa)*(9/20 : ℝ) ≤ 1 by linarith)
  exact Finset.mem_Icc.mpr ⟨hp,by exact_mod_cast hbound.trans hlast⟩

theorem rankUpper_test_carrier {N : ℕ} (hN : 1 ≤ N) {kappa nu epsilon : ℝ}
    (hk0 : 0 ≤ kappa) (hnu : 0 ≤ nu) (retain : List ℕ → Bool) (cap k : ℕ)
    (hgap : nu*((k : ℝ)*(19/96 : ℝ)+epsilon) ≤ (1-kappa)*(9/20 : ℝ))
    (F : ℕ → ℝ) :
    (∑ q ∈ physicalUpperModuli N nu epsilon retain cap,
      rankUpperRho N nu epsilon retain cap k q*F q) =
      ∑ q ∈ Finset.Icc 1 N,rankUpperRho N nu epsilon retain cap k q*F q := by
  let S := physicalUpperModuli N nu epsilon retain cap
  let I := Finset.Icc 1 N
  let rho := rankUpperRho N nu epsilon retain cap k
  let f := fun q => rho q*F q
  have hlevel := rankUpper_completeLevel hN hnu retain cap k hgap
  have hS : (∑ q ∈ S,f q) = ∑ q ∈ S ∩ I,f q := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hq hn
    have hz : rho q = 0 := by
      by_contra hr
      exact hn (Finset.mem_inter.mpr ⟨hq,completeLevel_active_mem_target hN hk0 hlevel hr⟩)
    simp only [f,hz,zero_mul]
  have hI : (∑ q ∈ I,f q) = ∑ q ∈ S ∩ I,f q := by
    symm
    apply Finset.sum_subset Finset.inter_subset_right
    intro q hq hn
    have hz : rho q = 0 := by
      by_contra hr
      exact hn (Finset.mem_inter.mpr ⟨rankUpper_active_mem_physical N nu epsilon retain cap k hr,hq⟩)
    simp only [f,hz,zero_mul]
  exact hS.trans hI.symm

/-- The existing full coefficient is split exactly at the chosen rank k. -/
theorem originalJointGamma_rank_split (N : ℕ) (nu epsilon : ℝ)
    (retain : List ℕ → Bool) (cap k : ℕ) (Q : Finset ℕ) (sigma : (ℕ × ℕ) → ℝ) :
    originalJointGammaError N Q (fullUpperRho N nu epsilon retain cap) sigma =
      originalJointGammaError N Q (rankUpperRho N nu epsilon retain cap k) sigma+
      originalJointGammaError N Q (rankRemainder N nu epsilon retain cap k) sigma := by
  have h (q : ℕ) : fullUpperRho N nu epsilon retain cap q =
      rankUpperRho N nu epsilon retain cap k q+rankRemainder N nu epsilon retain cap k q :=
    rho_eq_rank_add_remaining retain N cap _ _ _ k q
  simp only [originalJointGammaError,h,add_mul,Finset.sum_add_distrib,mul_add]

end
end ImbalancedChen.P2GammaRankScaledUpperSource
