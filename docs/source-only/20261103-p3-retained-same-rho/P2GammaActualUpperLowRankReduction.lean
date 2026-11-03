import ImbalancedChen.P2GammaRetainedSameRhoMother

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Compose the actual original upper low-rank coefficient, the complete
retained mother/grid sum and the previous complete joint discarded payment.
The resulting full-source bound displays both remaining costs explicitly:
the unchanged empty-word lane and the actual outside selector L1 mass.
Neither is renamed Theta or asserted small. Full P3.6 remains open.
-/

namespace ImbalancedChen.P2GammaActualUpperLowRankReduction
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P4BPositiveUpperLowRankClass
open P2GammaRetainedSameRhoRows P2GammaRetainedSameRhoMother
open P2GammaJointRetainedReduction P2GammaJointDiscardedPayment
open P2GammaOrderingStripPayment P2GammaJointLabels
open P2GammaCompleteProductTrimPayment P2GammaChosenLogGridBudget
open P5OriginalU5CausalFinite (pairSupport)

/-- Full beta is included: this is not a rough-only coefficient bound. -/
theorem upperRho_abs_le_one (N : ℕ) (nu epsilon : ℝ)
    (retain : List ℕ → Bool) (cap q : ℕ) :
    |upperRho N nu epsilon retain cap q| ≤ 1 :=
  rankRho_abs_le_one _ _ _ _ _ _ _ _

/-- The fixed positive-modulus carrier [1,N] contains the ENTIRE nonzero
low-rank physical coefficient. It is an enumeration carrier, not a common causal
rootQ and not a replacement of the coefficient's physical level. -/
theorem upperRho_active_mem_target {N : ℕ} (hN : 2 ≤ N) {nu epsilon : ℝ}
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (heps : 0 ≤ epsilon)
    (heps1 : epsilon ≤ 1/1000) (retain : List ℕ → Bool) (cap : ℕ)
    {q : ℕ} (hr : upperRho N nu epsilon retain cap q ≠ 0) :
    q ∈ Finset.Icc 1 N := by
  have hs := attached_rank_two_support (fun _ => retain) (fun _ => cap)
    (mul_nonneg hnu (by norm_num : (0 : ℝ) ≤ 19/96)) (by omega : 1 ≤ N) hr
  have hq := (original_upper_rank_two_below_half (fun _ => retain) (fun _ => cap)
    hnu hnu1 heps (by linarith : epsilon < 5/48) (by omega : 1 < N) hr).1
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ)^(19/48+epsilon) ≤ (N : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hN1
      (show 19/48+epsilon ≤ (1 : ℝ) by linarith)
  have hqN : q ≤ N := by exact_mod_cast (hq.trans_le hpow).le
  exact Finset.mem_Icc.mpr ⟨by have hp := hs.1; omega,hqN⟩

/-- The original full physical carrier, not its analytic enumeration cap. -/
def physicalUpperModuli (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap : ℕ) : Finset ℕ :=
  actualSmallRoughModuli retain N cap ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*(19/96 : ℝ)))

/-- Every active low coefficient belongs to the original full carrier. -/
theorem upperRho_active_mem_physical (N : ℕ) (nu epsilon : ℝ)
    (retain : List ℕ → Bool) (cap : ℕ) {q : ℕ}
    (hr : upperRho N nu epsilon retain cap q ≠ 0) :
    q ∈ physicalUpperModuli N nu epsilon retain cap := by
  have hmem : q ∈ rankModuli retain N cap ((N : ℝ)^(nu*epsilon^2))
      ((N : ℝ)^(nu*(19/96 : ℝ))) 2 := by
    by_contra hn
    exact hr (by simp only [upperRho,rankRho,if_neg hn])
  exact rankModuli_subset retain N cap _ _ 2 hmem

/-- An exact test identity moves ONLY the active low branch between the
actual physical carrier and [1,N]. No high-branch support is assumed. -/
theorem upperRho_test_actual_moduli {N : ℕ} (hN : 2 ≤ N) {nu epsilon : ℝ}
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (heps : 0 ≤ epsilon)
    (heps1 : epsilon ≤ 1/1000) (retain : List ℕ → Bool) (cap : ℕ) (F : ℕ → ℝ) :
    (∑ q ∈ physicalUpperModuli N nu epsilon retain cap,
      upperRho N nu epsilon retain cap q*F q) =
      ∑ q ∈ Finset.Icc 1 N,upperRho N nu epsilon retain cap q*F q := by
  let S := physicalUpperModuli N nu epsilon retain cap
  let I := Finset.Icc 1 N
  let f := fun q => upperRho N nu epsilon retain cap q*F q
  have hS : (∑ q ∈ S,f q) = ∑ q ∈ S ∩ I,f q := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro q hq hn
    have hz : upperRho N nu epsilon retain cap q = 0 := by
      by_contra hr
      exact hn (Finset.mem_inter.mpr ⟨hq,
        upperRho_active_mem_target hN hnu hnu1 heps heps1 retain cap hr⟩)
    simp only [f,hz,zero_mul]
  have hI : (∑ q ∈ I,f q) = ∑ q ∈ S ∩ I,f q := by
    symm
    apply Finset.sum_subset Finset.inter_subset_right
    intro q hq hn
    have hz : upperRho N nu epsilon retain cap q = 0 := by
      by_contra hr
      exact hn (Finset.mem_inter.mpr
        ⟨upperRho_active_mem_physical N nu epsilon retain cap hr,hq⟩)
    simp only [f,hz,zero_mul]
  exact hS.trans hI.symm

theorem originalJointGamma_upperRho_actual_moduli {N : ℕ} (hN : 2 ≤ N)
    {nu epsilon : ℝ} (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (heps : 0 ≤ epsilon)
    (heps1 : epsilon ≤ 1/1000) (retain : List ℕ → Bool) (cap : ℕ)
    (sigma : (ℕ × ℕ) → ℝ) :
    originalJointGammaError N (physicalUpperModuli N nu epsilon retain cap)
      (upperRho N nu epsilon retain cap) sigma =
    originalJointGammaError N (Finset.Icc 1 N)
      (upperRho N nu epsilon retain cap) sigma := by
  unfold originalJointGammaError
  apply Finset.sum_congr rfl
  intro t ht
  rw [upperRho_test_actual_moduli hN hnu hnu1 heps heps1 retain cap]

theorem emptyJointError_upperRho_actual_moduli {N : ℕ} (hN : 2 ≤ N)
    {nu epsilon : ℝ} (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (heps : 0 ≤ epsilon)
    (heps1 : epsilon ≤ 1/1000) (retain : List ℕ → Bool) (cap : ℕ)
    (sigma : (ℕ × ℕ) → ℝ) (T : ℝ) :
    emptyJointError N (physicalUpperModuli N nu epsilon retain cap)
      (upperRho N nu epsilon retain cap) sigma T =
    emptyJointError N (Finset.Icc 1 N)
      (upperRho N nu epsilon retain cap) sigma T := by
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
    exact upperRho_test_actual_moduli hN hnu hnu1 heps heps1 retain cap _
  · simp only [emptyWordError,if_neg hn]

/-- Exact source equality, with no analytical assumptions and no deleted
nil occurrence. The same rho occurs in every term. -/
theorem originalJointGamma_eq_three_lanes (N : ℕ) (Q : Finset ℕ)
    (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℝ) {T H δ : ℝ}
    (hT : 0 < T) (hH : 2*T ≤ H) (hδ : 0 < δ) {K : ℕ}
    (hK : Real.log (N : ℝ)/δ+1 ≤ K) :
    originalJointGammaError N Q rho sigma =
      headJointError N Q rho sigma H δ K+
      emptyJointError N Q rho sigma T+
      originalJointDiscardedError N Q rho sigma T H δ K := by
  rw [originalJointGammaError_eq_retained_add_discarded N Q rho sigma hT hH hδ hK,
    jointRetained_eq_head_add_empty]

/-- The terminal source estimate actually consumes both supplier chains.
No PP/energy/conductor/profile/cutoff estimate is an argument. The result
is NOT a uniform relative-Theta estimate: the genuine selector mass and
the untouched empty-word lane remain visible. All constants precede N
and every later allowed physical policy, coefficient and selector. -/
theorem exists_original_upper_low_rank_reduction (height : ℝ) (hheight : 0 < height)
    (A : ℕ) (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
      0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (sigma : (ℕ × ℕ) → ℝ),
      (∀ t ∈ pairSupport N,0 ≤ sigma t ∧ sigma t ≤ height) →
      |originalJointGammaError N (Finset.Icc 1 N)
          (upperRho N nu epsilon retain cap) sigma-
        emptyJointError N (Finset.Icc 1 N)
          (upperRho N nu epsilon retain cap) sigma ((N : ℝ)^(1-kappa))| ≤
        (C*selectorMass N sigma+eta)*(N : ℝ)/(Real.log (N : ℝ))^A := by
  let B := orderMeshExponent (jointListMomentOrder originalMotherOccurrences) A
  have hB : 0 < B := by dsimp [B,orderMeshExponent]; omega
  have hk1 : kappa < 1 := by linarith
  obtain ⟨C,hC,hheads⟩ := exists_chosen_headJoint_same_rho A B hB kappa hk0.le hk
  refine ⟨C,hC,?_⟩
  filter_upwards [hheads,
    eventually_originalJointGamma_retained_reduction height hheight A kappa hk0 hk1 eta heta]
    with N hh hd
  intro nu epsilon hnu hnu1 heps heps1 retain cap sigma hsigma
  let rho := upperRho N nu epsilon retain cap
  let Q := Finset.Icc 1 N
  let T := (N : ℝ)^(1-kappa)
  let H := 2*T
  let δ := chosenWidth A N
  let K := chosenGrid A N
  have hrho : ∀ q ∈ Q,|rho q| ≤ 1 := fun q _ => upperRho_abs_le_one _ _ _ _ _ q
  have hdiscard := hd Q rho sigma (by intro q hq; exact hq) hrho hsigma
  have hhead := hh nu epsilon hnu hnu1 heps heps1 retain cap Q sigma
  have hhead' : |headJointError N Q rho sigma H δ K| ≤
      (C*(N : ℝ)/(Real.log (N : ℝ))^A)*selectorMass N sigma := by
    simpa only [rho,H,T,δ,K,chosenWidth,chosenGrid,gridLength,B] using hhead
  have hid : originalJointGammaError N Q rho sigma-emptyJointError N Q rho sigma T =
      headJointError N Q rho sigma H δ K+
        (originalJointGammaError N Q rho sigma-
          originalJointRetainedError N Q rho sigma T H δ K) := by
    rw [jointRetained_eq_head_add_empty]
    ring
  change |originalJointGammaError N Q rho sigma-emptyJointError N Q rho sigma T| ≤ _
  rw [hid]
  calc
    _ ≤ |headJointError N Q rho sigma H δ K|+
        |originalJointGammaError N Q rho sigma-
          originalJointRetainedError N Q rho sigma T H δ K| := abs_add _ _
    _ ≤ (C*(N : ℝ)/(Real.log (N : ℝ))^A)*selectorMass N sigma+
        eta*(N : ℝ)/(Real.log (N : ℝ))^A := add_le_add hhead' hdiscard
    _ = _ := by ring


/-- The full original attachment and its existing complementary rank branch.
The latter is defined by the original remainingRho, not a desired error. -/
def fullUpperRho (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap q : ℕ) : ℝ :=
  actualSmallRoughRho retain N cap ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) q

def highUpperRho (N : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap q : ℕ) : ℝ :=
  remainingRho retain N cap ((N : ℝ)^(nu*epsilon^2))
    ((N : ℝ)^(nu*(19/96 : ℝ))) ((N : ℝ)^(nu*epsilon)) 2 q

/-- This identity prevents the low-rank theorem being mistaken for a
bound on the entire unsplit coefficient. It holds before any estimate. -/
theorem originalJointGamma_fullUpper_split (N : ℕ) (nu epsilon : ℝ)
    (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ) (sigma : (ℕ × ℕ) → ℝ) :
    originalJointGammaError N Q (fullUpperRho N nu epsilon retain cap) sigma =
      originalJointGammaError N Q (upperRho N nu epsilon retain cap) sigma+
      originalJointGammaError N Q (highUpperRho N nu epsilon retain cap) sigma := by
  have h (q : ℕ) : fullUpperRho N nu epsilon retain cap q =
      upperRho N nu epsilon retain cap q+highUpperRho N nu epsilon retain cap q :=
    rho_eq_rank_add_remaining retain N cap _ _ _ 2 q
  simp only [originalJointGammaError,h,add_mul,Finset.sum_add_distrib,mul_add]

/-- Actual compact extended-third policy instance. This identifies a real
existing coefficient, not the still-unidentified final full87 policy.
The HIGH branch, empty LOW lane, and outside mass all stay explicit. -/
theorem exists_actualCompact_fullUpper_reduction (height : ℝ) (hheight : 0 < height)
    (A : ℕ) (kappa : ℝ) (hk0 : 0 < kappa) (hk : kappa ≤ 1/100)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ nu epsilon : ℝ,
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
        (C*selectorMass N sigma+eta)*(N : ℝ)/(Real.log (N : ℝ))^A := by
  obtain ⟨C,hC,hbound⟩ := exists_original_upper_low_rank_reduction
    height hheight A kappa hk0 hk eta heta
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (2 : ℕ)] with N hN hN2
  intro nu epsilon hnu hnu1 heps heps1 e h m cap sigma hsigma
  dsimp only
  rw [originalJointGamma_fullUpper_split,add_sub_cancel_right,
    originalJointGamma_upperRho_actual_moduli hN2 hnu hnu1 heps heps1,
    emptyJointError_upperRho_actual_moduli hN2 hnu hnu1 heps heps1]
  exact hN nu epsilon hnu hnu1 heps heps1
    (actualExtendedThirdCompactUpperPolicy e h m N false) cap sigma hsigma

end
end ImbalancedChen.P2GammaActualUpperLowRankReduction
