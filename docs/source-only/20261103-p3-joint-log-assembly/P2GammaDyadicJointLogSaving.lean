import ImbalancedChen.P2GammaJointLogBudget

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.
Consume the previously supplied JOINT dyadic row estimate, discharge its
cutoff/logarithm balance from actual complete scales, and return to N.
No selectorMass, head overlap, row estimate, energy, cutoff-growth or
post-loss licence is an input to the terminal theorem. The coefficient
class is the original upper rough-modulus rank <= 2, not all of P3.6.
-/
namespace ImbalancedChen.P2GammaDyadicJointLogSaving
noncomputable section
open scoped Classical BigOperators Topology
open Filter
open P2GammaJointLogBudget P2GammaDyadicJointRowEstimate
open P2GammaDyadicHeadSource P2GammaDyadicFamilyEnergy
open P2GammaDyadicSmallConductorFamily P2GammaRetainedCompleteScale
open P2GammaRetainedLowRankLevel P2GammaChosenLogGridBudget
open P2GammaOriginalScaleTransport P2GammaConductorScaleThreshold
open P2GammaSmoothLogGrid P2GammaRetainedSameRhoRows
open P5OriginalU5CausalFinite (pairSupport)

/-- J and B are fixed BEFORE prime accuracy and all thresholds. The later
height h is paid linearly, including h=0. Both occupied and empty charts
are covered in the same statement. -/
theorem exists_joint_row_log_saving (A B J : ℕ) (hB : 0 < B)
    (kappa : ℝ) (hk0 : 0 ≤ kappa) (hk : kappa ≤ 1/100) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ c : ℕ,∀ cs : List ℕ,cs.length+2 ≤ J → (cs.length+3)^2-1 ≤ J →
      ∀ j l : ℕ,∀ nu epsilon : ℝ,0 ≤ nu → nu ≤ 1 → 0 ≤ epsilon → epsilon ≤ 1/1000 →
      ∀ (retain : List ℕ → Bool) (cap : ℕ) (Q : Finset ℕ)
        (sigma : (ℕ × ℕ) → ℂ) (height : ℝ),0 ≤ height →
      (∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) →
      ‖jointSignedRow N c cs (2*(N : ℝ)^(1-kappa)) (boundaryLogMesh B N)
        j l nu epsilon retain cap Q sigma‖ ≤ C*height*(N : ℝ)/(Real.log (N : ℝ))^A := by
  have hk1 : kappa < 1 := by linarith
  have hbeta : 0 < 1-kappa := by linarith
  obtain ⟨C0,hC0,hraw⟩ := exists_chosen_joint_row_estimate
    (primeOrder A J : ℝ) B hB kappa hk0 hk
  obtain ⟨x0,hx0,hbalance⟩ := exists_joint_scalar_threshold A J
  obtain ⟨Ts,hTs,hscale⟩ := exists_trim_occupied_scale_threshold kappa hk1
  obtain ⟨Tl,hTl,hlarge⟩ := exists_original_scale_common_threshold x0 (1-kappa) hbeta
  let D := totalConstant C0 A J
  have hD : 0 < D := totalConstant_pos hC0 A J
  refine ⟨D/(1-kappa)^A,by positivity,?_⟩
  filter_upwards [hraw,eventually_ge_atTop (Nat.ceil Ts),
    eventually_ge_atTop (Nat.ceil Tl),eventually_ge_atTop (2 : ℕ),
    eventually_chosen_mesh_factor_two hB] with N hrow hTsN hTlN hN hm
  intro c cs hJ1 hJ2 j l nu epsilon hnu hnu1 heps heps1 retain cap Q sigma height hh hs
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
    have hfinite := hrow c cs j l ⟨t,ht,hot⟩ nu epsilon hnu hnu1 heps heps1
      retain cap Q sigma height hh hs b0
    have hbalanced := hbalance x hxx M V hM hV rfl hMp hVp
      (ambientHi δ j) (ambientHi δ l) (localModulusCap x) hP hR hQ0
      cs hJ1 hJ2 C0 height hC0.le hh
    have hlocal : ‖jointSignedRow N c cs H δ j l nu epsilon retain cap Q sigma‖ ≤
        D*height*x/(Real.log x)^A := hfinite.trans hbalanced
    have hu := local_log_unit_le_original (A : ℝ) (1-kappa) 1 (N : ℝ) x
      (by positivity) hbeta (by norm_num)
      (by exact_mod_cast (show 1 < N by omega)) hlower (by simpa only [one_mul] using hupper)
    simp only [Real.rpow_natCast] at hu
    have htransport := mul_le_mul_of_nonneg_left hu (mul_nonneg hD.le hh)
    exact hlocal.trans (by convert htransport using 1 <;> ring)
  · rw [jointSignedRow_zero_of_unoccupied N c cs H δ j l nu epsilon retain cap Q sigma ho,norm_zero]
    have hlog : 0 ≤ Real.log (N : ℝ) := zero_le_one.trans hm.1
    positivity

end
end ImbalancedChen.P2GammaDyadicJointLogSaving
