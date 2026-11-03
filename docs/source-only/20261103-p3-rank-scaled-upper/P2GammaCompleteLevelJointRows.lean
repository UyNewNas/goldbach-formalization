import ImbalancedChen.P2GammaDyadicJointLogSaving

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Generalize the actual joint-source attachment from the fixed rank-two rho
only to a primitive COMPLETE coefficient level. All analytic suppliers,
source labels, dyadic costs and scalar balances are reused unchanged.
The actual rank-k supplier is in P2GammaRankScaledUpperSource; the level
predicate below is not a PP/distribution/energy premise.
-/
namespace ImbalancedChen.P2GammaCompleteLevelJointRows
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaDyadicHeadIntervals P2GammaDyadicHeadSource P2GammaDyadicFamilyEnergy
open P2GammaDyadicSmallConductorFamily P2GammaDyadicJointRowEstimate
open P2GammaRetainedSameRhoRows P2GammaRetainedCompleteScale
open P2GammaRetainedLowRankLevel P2GammaSmallConductorIntervalBridge
open P2GammaConductorScaleThreshold P2GammaChosenLogGridBudget P2GammaSmoothLogGrid
open P2GammaJointLogBudget P2GammaOriginalScaleTransport
open P5OriginalU5CausalFinite (pairSupport)

/-- Primitive scalar and active-support conditions at the ORIGINAL N.
No analytic conclusion or source-error bound is included. -/
def CompleteLevel (N : ℕ) (kappa : ℝ) (rho : ℕ → ℝ) : Prop :=
  (∀ q : ℕ, |rho q| ≤ 1) ∧
    ∀ q : ℕ, rho q ≠ 0 →
      0 < q ∧ N.Coprime q ∧ (q : ℝ) ≤ (N : ℝ)^((1-kappa)*(9/20 : ℝ))

/-- The same explicit original joint Cartesian source at a supplied rho. -/
def boundedRow (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℂ) : ℂ :=
  ∑ q ∈ Q,(rho q : ℂ)*
    ∑ t ∈ pairSupport N,sigma t*cartesianRow N t c cs H δ j l q

theorem boundedRow_zero (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (sigma : (ℕ × ℕ) → ℂ)
    (hn : ¬ JointOccupied N c cs H δ j l) :
    boundedRow N c cs H δ j l Q rho sigma = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hz : (∑ t ∈ pairSupport N,sigma t*cartesianRow N t c cs H δ j l q) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [cartesianRow_eq_zero (fun ho => hn ⟨t,ht,ho⟩) q,mul_zero]
  rw [hz,mul_zero]

/-- Transfer the complete N-level to the occupied COMPLETE two-factor x.
This is the only level comparison needed by the inherited conductor ledger. -/
theorem completeLevel_local_cap {N : ℕ} {kappa x : ℝ} {rho : ℕ → ℝ}
    (hrho : CompleteLevel N kappa rho)
    (hlower : (N : ℝ)^(1-kappa) ≤ x) {q : ℕ} (hq : rho q ≠ 0) :
    0 < q ∧ N.Coprime q ∧ |rho q| ≤ 1 ∧ q ≤ localModulusCap x := by
  obtain ⟨hpos,hcop,hlevel⟩ := hrho.2 q hq
  have hp : (q : ℝ) ≤ x^(9/20 : ℝ) := by
    calc
      _ ≤ (N : ℝ)^((1-kappa)*(9/20 : ℝ)) := hlevel
      _ = ((N : ℝ)^(1-kappa))^(9/20 : ℝ) :=
        Real.rpow_mul (Nat.cast_nonneg N) _ _
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg N) _)
        hlower (by norm_num)
  exact ⟨hpos,hcop,hrho.1 q,Nat.le_floor hp⟩

/-- No new character argument: exact dyadic source and exact principal
cancellation are reused on active q before the norm is taken. -/
theorem boundedRow_le_ledgers {N c : ℕ} {cs : List ℕ}
    (hN : 2 ≤ N) {kappa δ : ℝ} (hk : kappa < 1)
    (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ)
    (hM : 1 ≤ lower δ j)
    (hocc : JointOccupied N c cs (2*(N : ℝ)^(1-kappa)) δ j l)
    (Q : Finset ℕ) (rho : ℕ → ℝ) (hrho : CompleteLevel N kappa rho)
    (sigma : (ℕ × ℕ) → ℂ) (b0 : ℕ) :
    let H := 2*(N : ℝ)^(1-kappa)
    let Q0 := localModulusCap (lower δ j*lower δ l)
    ‖boundedRow N c cs H δ j l Q rho sigma‖ ≤
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
  have hlower := (occupied_trim_complete_scale hN ht hk hδ hwidth ho).1
  have heq : boundedRow N c cs H δ j l Q rho sigma = ∑ q ∈ Q,(rho q : ℂ)*F q := by
    apply Finset.sum_congr rfl
    intro q hqQ
    by_cases hq : rho q = 0
    · simp only [hq,Complex.ofReal_zero,zero_mul]
    · obtain ⟨hpos,hcop,_⟩ := hrho.2 q hq
      rw [original_joint_eq_dyadic N c cs H hδ hwidth j l (fun _ _ _ => hM) sigma q]
      have hchar (d : ℕ) (e : (ℕ × ℕ) → ℕ) :=
        levelSource_eq_character N c cs H hδ hwidth j l d e sigma hpos hcop
      simpa only [hchar]
  have hmod : ‖boundedRow N c cs H δ j l Q rho sigma‖ ≤ ∑ q ∈ I,‖F q‖ := by
    rw [heq]
    calc
      _ ≤ ∑ q ∈ Q,‖(rho q : ℂ)*F q‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ Q,if q ∈ I then ‖F q‖ else 0 := by
        apply Finset.sum_le_sum
        intro q hqQ
        by_cases hq : rho q = 0
        · simp only [hq,Complex.ofReal_zero,zero_mul,norm_zero]
          split_ifs <;> positivity
        · obtain ⟨hpos,hcop,hnorm,hcap⟩ := completeLevel_local_cap hrho hlower hq
          have hqI : q ∈ I := Finset.mem_Icc.mpr ⟨hpos,hcap⟩
          have hnorm' : ‖(rho q : ℂ)‖ ≤ 1 := by
            simpa only [Complex.norm_real,Real.norm_eq_abs] using hnorm
          rw [if_pos hqI,norm_mul]
          exact (mul_le_mul_of_nonneg_right hnorm' (norm_nonneg _)).trans_eq (one_mul _)
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

/-- Invoke both actual small/high suppliers with the same original rows.
Their constants do not depend on the later rho. -/
theorem exists_complete_row_estimate (A : ℝ) (B : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk : kappa < 1) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,∀ c : ℕ,∀ cs : List ℕ,∀ j l : ℕ,
      JointOccupied N c cs (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N) j l →
      ∀ (Q : Finset ℕ) (rho : ℕ → ℝ),CompleteLevel N kappa rho →
      ∀ (sigma : (ℕ × ℕ) → ℂ) (height : ℝ),0 ≤ height →
      (∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) → ∀ b0 : ℕ,
      let δ := boundaryLogMesh B N
      let H := 2*(N : ℝ)^(1-kappa)
      let M := lower δ j
      let V := lower δ l
      let Q0 := localModulusCap (M*V)
      ‖boundedRow N c cs H δ j l Q rho sigma‖ ≤
        (2*(depth (ambientHi δ j) : ℝ))*
          (lowCost C height M V (M*V) cs A Q0 b0+
           (Real.sqrt (ambientHi δ j)*Real.sqrt (betaBound cs height V))*
             highFactor (ambientHi δ j) (ambientHi δ l) Q0 b0 (logGauge Q0)) := by
  obtain ⟨C,hC,hlow⟩ := exists_chosen_all_scales_low A B hB kappa hk
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk
  refine ⟨C,hC,?_⟩
  filter_upwards [hlow,eventually_ge_atTop (Nat.ceil Ts),eventually_ge_atTop (2 : ℕ),
    eventually_chosen_mesh_factor_two hB] with N hlowN hNT hN hm
  intro c cs j l hocc Q rho hrho sigma height hh hs b0
  dsimp only
  let δ := boundaryLogMesh B N
  let H := 2*(N : ℝ)^(1-kappa)
  let Q0 := localModulusCap (lower δ j*lower δ l)
  obtain ⟨t,ht,ho⟩ := hocc
  have hTsN : Ts ≤ (N : ℝ) := (Nat.le_ceil Ts).trans (by exact_mod_cast hNT)
  have hscaleN := hscale N hTsN t ht c cs δ hm.2.1 hm.2.2 j l ho
  have hM : 1 ≤ lower δ j := hscaleN.2.1
  have hV : 1 ≤ lower δ l := hscaleN.2.2.1
  have hfinite := boundedRow_le_ledgers hN hk hm.2.1 hm.2.2 j l hM
    ⟨t,ht,ho⟩ Q rho hrho sigma b0
  have hlow' := hlowN c cs j l ⟨t,ht,ho⟩ sigma height hh hs Q0 b0
  have hhigh := actual_all_scales_high_le N c cs H hm.2.1 hm.2.2 j l hV sigma hh hs Q0 b0
  exact hfinite.trans ((add_le_add hlow' hhigh).trans_eq (by ring))

/-- All scalar cutoff and log costs are discharged using the unchanged
153bb09 balance. The primitive coefficient support is the only new
parameter; the analytic bound and the original source are supplied. -/
theorem exists_complete_row_log_saving (A B J : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk : kappa < 1) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ c : ℕ,∀ cs : List ℕ,cs.length+2 ≤ J → (cs.length+3)^2-1 ≤ J →
      ∀ j l : ℕ,∀ (Q : Finset ℕ) (rho : ℕ → ℝ),CompleteLevel N kappa rho →
      ∀ (sigma : (ℕ × ℕ) → ℂ) (height : ℝ),0 ≤ height →
      (∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) →
      ‖boundedRow N c cs (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N)
        j l Q rho sigma‖ ≤ C*height*(N : ℝ)/(Real.log (N : ℝ))^A := by
  have hk1 : kappa < 1 := hk
  have hbeta : 0 < 1-kappa := by linarith
  obtain ⟨C0,hC0,hraw⟩ := exists_complete_row_estimate
    (primeOrder A J : ℝ) B hB kappa hk
  obtain ⟨x0,hx0,hbalance⟩ := exists_joint_scalar_threshold A J
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk1
  obtain ⟨Tl,hTl,hlarge⟩ := exists_original_scale_common_threshold x0 (1-kappa) hbeta
  let D := totalConstant C0 A J
  have hD : 0 < D := totalConstant_pos hC0 A J
  refine ⟨D/(1-kappa)^A,by positivity,?_⟩
  filter_upwards [hraw,eventually_ge_atTop (Nat.ceil Ts),
    eventually_ge_atTop (Nat.ceil Tl),eventually_ge_atTop (2 : ℕ),
    eventually_chosen_mesh_factor_two hB] with N hrow hTsN hTlN hN hm
  intro c cs hJ1 hJ2 j l Q rho hrho sigma height hh hs
  let δ := boundaryLogMesh B N
  let H := 2*(N : ℝ)^(1-kappa)
  let M := lower δ j
  let V := lower δ l
  let x := M*V
  by_cases ho : JointOccupied N c cs H δ j l
  · obtain ⟨t,ht,hot⟩ := ho
    have hTsN' : Ts ≤ (N : ℝ) := (Nat.le_ceil Ts).trans (by exact_mod_cast hTsN)
    have hTlN' : Tl ≤ (N : ℝ) := (Nat.le_ceil Tl).trans (by exact_mod_cast hTlN)
    obtain ⟨hlogx,hM,hV,hMp,hVp,hlower,hupper,htarget⟩ :=
      hscale N hTsN' t ht c cs δ hm.2.1 hm.2.2 j l hot
    have hxx : x0 ≤ x := hlarge (N : ℝ) hTlN' x hlower
    have hP : (ambientHi δ j : ℝ) ≤ 2*M := Nat.floor_le (by dsimp [M]; positivity)
    have hR : (ambientHi δ l : ℝ) ≤ 2*V := Nat.floor_le (by dsimp [V]; positivity)
    have hQ0 : (localModulusCap x : ℝ) ≤ x^(9/20 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by dsimp [x,M,V]; positivity) _)
    let b0 := cutoffExponent (Real.log x) (cutOrder A J)
    have hfinite := hrow c cs j l ⟨t,ht,hot⟩ Q rho hrho sigma height hh hs b0
    have hbalanced := hbalance x hxx M V hM hV rfl hMp hVp
      (ambientHi δ j) (ambientHi δ l) (localModulusCap x) hP hR hQ0
      cs hJ1 hJ2 C0 height hC0.le hh
    have hlocal : ‖boundedRow N c cs H δ j l Q rho sigma‖ ≤
        D*height*x/(Real.log x)^A := hfinite.trans hbalanced
    have hu := local_log_unit_le_original (A : ℝ) (1-kappa) 1 (N : ℝ) x
      (by positivity) hbeta (by norm_num)
      (by exact_mod_cast (show 1 < N by omega)) hlower (by simpa only [one_mul] using hupper)
    simp only [Real.rpow_natCast] at hu
    have htransport := mul_le_mul_of_nonneg_left hu (mul_nonneg hD.le hh)
    exact hlocal.trans (by convert htransport using 1 <;> ring)
  · rw [boundedRow_zero N c cs H δ j l Q rho sigma ho,norm_zero]
    have hlog : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hm.1
    positivity


end
end ImbalancedChen.P2GammaCompleteLevelJointRows
