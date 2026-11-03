import ImbalancedChen.P2GammaDyadicSmallConductorFamily

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Actual signed joint retained row -> dyadic character family -> supplied
small AND complete high conductor budgets. Neither an outside selector
mass nor a head-key overlap/count appears in the final explicit bound.
This is not yet the arbitrary-log full mother/grid PP endpoint: all
remaining scalar cutoff/logarithm costs are displayed.
-/

namespace ImbalancedChen.P2GammaDyadicJointRowEstimate
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaDyadicHeadIntervals P2GammaDyadicHeadSource P2GammaDyadicFamilyEnergy
open P2GammaDyadicSmallConductorFamily P2GammaRetainedSameRhoRows
open P2GammaRetainedCompleteScale P2GammaRetainedLowRankLevel
open P2GammaSmallConductorIntervalBridge P2GammaConductorScaleThreshold
open P2GammaChosenLogGridBudget P2GammaSmoothLogGrid
open P5OriginalU5CausalFinite (pairSupport)

def JointOccupied (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ) : Prop :=
  ∃ t ∈ pairSupport N,Occupied N t c cs H δ j l

def jointSignedRow (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (nu epsilon : ℝ) (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℂ) : ℂ :=
  ∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ)*
    ∑ t ∈ pairSupport N,sigma t*cartesianRow N t c cs H δ j l q

/-- Inactive charts are zero in the ORIGINAL source; no comparison of
artificial prefix pieces is used to assert this. -/
theorem jointSignedRow_zero_of_unoccupied (N c : ℕ) (cs : List ℕ)
    (H δ : ℝ) (j l : ℕ) (nu epsilon : ℝ) (retain : List ℕ → Bool)
    (cap : ℕ) (Q : Finset ℕ) (sigma : (ℕ × ℕ) → ℂ)
    (hn : ¬ JointOccupied N c cs H δ j l) :
    jointSignedRow N c cs H δ j l nu epsilon retain cap Q sigma = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have htzero : (∑ t ∈ pairSupport N,sigma t*cartesianRow N t c cs H δ j l q) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have ho : ¬ Occupied N t c cs H δ j l := fun h => hn ⟨t,ht,h⟩
    rw [cartesianRow_eq_zero ho q,mul_zero]
  rw [htzero,mul_zero]

/-- Finite same-rho modulus attachment and whole outside source. The
post-loss modulus cap is supplied by the actual upper rank-two coefficient,
not by a premise about a newly chosen analytic coefficient. -/
theorem jointSignedRow_le_ledgers {N c : ℕ} {cs : List ℕ}
    (hN : 2 ≤ N) {kappa δ nu epsilon : ℝ}
    (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100)
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2)
    (hnu : 0 ≤ nu) (hnu1 : nu ≤ 1) (heps : 0 ≤ epsilon) (heps1 : epsilon ≤ 1/1000)
    (j l : ℕ) (hM : 1 ≤ lower δ j)
    (hocc : JointOccupied N c cs (2*(N : ℝ)^(1-kappa)) δ j l)
    (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
    (sigma : (ℕ × ℕ) → ℂ) (b0 : ℕ) :
    let H := 2*(N : ℝ)^(1-kappa)
    let Q0 := localModulusCap (lower δ j*lower δ l)
    ‖jointSignedRow N c cs H δ j l nu epsilon retain cap Q sigma‖ ≤
      (∑ d ∈ Finset.range (depth (ambientHi δ j)),
        (levelLow N c cs H δ j l d (endpointHi N c cs H δ j l) sigma Q0 b0+
         levelLow N c cs H δ j l d (endpointLo N c cs H δ j l) sigma Q0 b0))+
      (∑ d ∈ Finset.range (depth (ambientHi δ j)),
        (levelHigh N c cs H δ j l d (endpointHi N c cs H δ j l) sigma Q0 b0+
         levelHigh N c cs H δ j l d (endpointLo N c cs H δ j l) sigma Q0 b0)) := by
  dsimp only
  let H := 2*(N : ℝ)^(1-kappa)
  let Q0 := localModulusCap (lower δ j*lower δ l)
  let I := Finset.Icc 1 Q0
  let D := Finset.range (depth (ambientHi δ j))
  let Fhi := fun d q => levelCharacterSource N c cs H δ j l d
    (endpointHi N c cs H δ j l) sigma q
  let Flo := fun d q => levelCharacterSource N c cs H δ j l d
    (endpointLo N c cs H δ j l) sigma q
  let F := fun q => ∑ d ∈ D,(Fhi d q-Flo d q)
  obtain ⟨t,ht,ho⟩ := hocc
  have heq : jointSignedRow N c cs H δ j l nu epsilon retain cap Q sigma =
      ∑ q ∈ Q,(upperRho N nu epsilon retain cap q : ℂ)*F q :=
    same_rho_dyadic_source (by omega : 1 ≤ N) c cs H hδ hwidth hnu epsilon j l
      (fun _ _ _ => hM) retain cap Q sigma
  have hmod : ‖jointSignedRow N c cs H δ j l nu epsilon retain cap Q sigma‖ ≤
      ∑ q ∈ I,‖F q‖ := by
    rw [heq]
    calc
      _ ≤ ∑ q ∈ Q,‖(upperRho N nu epsilon retain cap q : ℂ)*F q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Q,if q ∈ I then ‖F q‖ else 0 := by
        apply Finset.sum_le_sum
        intro q hqQ
        by_cases hr : upperRho N nu epsilon retain cap q = 0
        · simp only [hr,Complex.ofReal_zero,zero_mul,norm_zero]
          split_ifs <;> positivity
        · obtain ⟨hq,hsq,hcop,hrho,hqlt,hqcap⟩ :=
            occupied_actual_rank_two_postloss hN ht hk0 hk hδ hwidth
              hnu hnu1 heps heps1 ho retain cap hr
          have hqI : q ∈ I := Finset.mem_Icc.mpr ⟨by omega,hqcap⟩
          have hnorm : ‖(upperRho N nu epsilon retain cap q : ℂ)‖ ≤ 1 := by
            simpa only [upperRho,Complex.norm_real,Real.norm_eq_abs] using hrho
          rw [if_pos hqI,norm_mul]
          exact (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans_eq (one_mul _)
      _ = ∑ q ∈ Q.filter (fun q => q ∈ I),‖F q‖ := by rw [Finset.sum_filter]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
        (fun q hq => (Finset.mem_filter.mp hq).2) (fun q _ _ => norm_nonneg _)
  calc
    _ ≤ ∑ q ∈ I,‖F q‖ := hmod
    _ ≤ ∑ q ∈ I,∑ d ∈ D,(‖Fhi d q‖+‖Flo d q‖) := by
      apply Finset.sum_le_sum
      intro q hq
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun d hd => norm_sub_le _ _))
    _ = ∑ d ∈ D,((∑ q ∈ I,‖Fhi d q‖)+(∑ q ∈ I,‖Flo d q‖)) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib]
    _ ≤ ∑ d ∈ D,
        ((levelLow N c cs H δ j l d (endpointHi N c cs H δ j l) sigma Q0 b0+
          levelHigh N c cs H δ j l d (endpointHi N c cs H δ j l) sigma Q0 b0)+
         (levelLow N c cs H δ j l d (endpointLo N c cs H δ j l) sigma Q0 b0+
          levelHigh N c cs H δ j l d (endpointLo N c cs H δ j l) sigma Q0 b0)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact add_le_add (level_character_norm_le N c cs H δ j l d _ sigma Q0 b0)
        (level_character_norm_le N c cs H δ j l d _ sigma Q0 b0)
    _ = _ := by simp only [Finset.sum_add_distrib]; ring

/-- The first complete explicit joint retained-row estimate with NO old
pair mass/count or headMultiplicity factor. Both analytic ledgers are
supplied, not assumed. What remains visible is cutoff/logarithm balancing
and the later complete mother/grid/Theta/high-rank assembly. -/
theorem exists_chosen_joint_row_estimate (A : ℝ) (B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ c : ℕ,∀ cs : List ℕ,∀ j l : ℕ,
      (JointOccupied N c cs (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) j l) →
      ∀ nu epsilon : ℝ,0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
        (sigma : (ℕ × ℕ) → ℂ) (height : ℝ),0 ≤ height →
      (∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) → ∀ b0 : ℕ,
      let δ := boundaryLogMesh B N
      let H := 2*(N : ℝ)^(1-kappa)
      let M := lower δ j
      let V := lower δ l
      let Q0 := localModulusCap (M*V)
      ‖jointSignedRow N c cs H δ j l nu epsilon retain cap Q sigma‖ ≤
        (2*(depth (ambientHi δ j) : ℝ))*
          (lowCost C height M V (M*V) cs A Q0 b0+
           (Real.sqrt (ambientHi δ j)*Real.sqrt (betaBound cs height V))*
             highFactor (ambientHi δ j) (ambientHi δ l) Q0 b0 (logGauge Q0)) := by
  have hk1 : kappa < 1 := by linarith
  obtain ⟨C,hC,hlow⟩ := exists_chosen_all_scales_low A B hB kappa hk1
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk1
  refine ⟨C,hC,?_⟩
  filter_upwards [hlow,eventually_ge_atTop (Nat.ceil Ts),eventually_ge_atTop (2 : ℕ),
    eventually_chosen_mesh_factor_two hB] with N hlowN hNT hN hm
  intro c cs j l hocc nu epsilon hnu hnu1 heps heps1 retain cap Q sigma height hh hs b0
  dsimp only
  let δ := boundaryLogMesh B N
  let H := 2*(N : ℝ)^(1-kappa)
  let Q0 := localModulusCap (lower δ j*lower δ l)
  obtain ⟨t,ht,ho⟩ := hocc
  have hTsN : Ts ≤ (N : ℝ) := (Nat.le_ceil Ts).trans (by exact_mod_cast hNT)
  have hscaleN := hscale N hTsN t ht c cs δ hm.2.1 hm.2.2 j l ho
  have hM : 1 ≤ lower δ j := hscaleN.2.1
  have hV : 1 ≤ lower δ l := hscaleN.2.2.1
  have hfinite := jointSignedRow_le_ledgers hN hk0 hk hm.2.1 hm.2.2
    hnu hnu1 heps heps1 j l hM ⟨t,ht,ho⟩ retain cap Q sigma b0
  have hlow' := hlowN c cs j l ⟨t,ht,ho⟩ sigma height hh hs Q0 b0
  have hhigh := actual_all_scales_high_le N c cs H hm.2.1 hm.2.2 j l hV sigma hh hs Q0 b0
  exact hfinite.trans ((add_le_add hlow' hhigh).trans_eq (by ring))

end
end ImbalancedChen.P2GammaDyadicJointRowEstimate
