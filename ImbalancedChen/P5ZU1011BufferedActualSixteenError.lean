import ImbalancedChen.P5ZU1011BufferedUniformStrip
import ImbalancedChen.P5ZU1011OriginalSixteenKnotPayment

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
Actual ORIGINAL16 one-sided physical ordinary errors. Every eligible
policy has the genuine residual floor; the nonlinear guarded minimum
pays ONE common error, without exchanging minimum and mean.
-/

namespace ImbalancedChen.P5Z.BufferedActualSixteenError

noncomputable section

open Set
open Classical
open U11Integral U11Canonical U11H248
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenKnotPayment U1011AdaptivePrimeError
open BufferedOrdinaryClamp BufferedUniformStrip
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary

def cubeFloor : ℝ := 417 / 5000
def badCostBound : ℝ := 8 / cubeFloor

theorem cubeFloor_pos : 0 < cubeFloor := by norm_num [cubeFloor]
theorem badCostBound_pos : 0 < badCostBound := by unfold badCostBound; positivity

def scale (δ e : ℝ) : ℝ := eta cubeFloor cubeFloor δ e / 2

theorem scale_pos {δ e : ℝ} (hd : 0 < δ) (he : 0 < e) : 0 < scale δ e :=
  div_pos (eta_pos cubeFloor_pos cubeFloor_pos hd he) (by norm_num)

def Small (δ e : ℝ) (τ ξ ρ : Policy → ℝ) : Prop := ∀ p : Policy,
  0 ≤ τ p ∧ τ p ≤ scale δ e ∧ 0 ≤ ξ p ∧ ξ p ≤ scale δ e ∧ 0 ≤ ρ p ∧ ρ p ≤ scale δ e

theorem small_strict {δ e : ℝ} (hd : 0 < δ) (he : 0 < e)
    {τ ξ ρ : Policy → ℝ} (h : Small δ e τ ξ ρ) (p : Policy) :
    0 ≤ τ p ∧ τ p < eta cubeFloor cubeFloor δ e ∧
      0 ≤ ξ p ∧ ξ p < eta cubeFloor cubeFloor δ e ∧
      0 ≤ ρ p ∧ ρ p < eta cubeFloor cubeFloor δ e := by
  have hp := h p
  have hs : scale δ e < eta cubeFloor cubeFloor δ e := by
    have hh := eta_pos cubeFloor_pos cubeFloor_pos hd he
    dsimp only [scale]
    linarith only [hh]
  exact ⟨hp.1, hp.2.1.trans_lt hs, hp.2.2.1, hp.2.2.2.1.trans_lt hs,
    hp.2.2.2.2.1, hp.2.2.2.2.2.trans_lt hs⟩

theorem eligible_scalar_parameters (mask : Set (ℝ × ℝ)) (p : Policy) {v : LogFour}
    (hv : v ∈ originalDomain mask) (he : TypedEligible p v) :
    cubeFloor ≤ typedResidual p v ∧ typedResidual p v ≤ 1 ∧
      cubeFloor ≤ v 3 ∧ v 3 ≤ 1 := by
  have hb := originalDomain_subset_compactBox mask hv
  have hcoord : ∀ i : Fin 4, 0 ≤ v i := fun i =>
    (show (0 : ℝ) ≤ 417 / 5000 by norm_num).trans (hb.1 i)
  have hsel : 0 ≤ selectedMass p v := by
    unfold selectedMass
    apply Finset.sum_nonneg
    intro i _
    by_cases hs : Selected p i <;> simp only [hs, if_true, if_false]
    · exact hcoord i
    · exact le_rfl
  have hcap : cap p v ≤ 1 := by
    by_cases hp : p.val < 15
    · simp only [cap, if_pos hp]
      exact (min_le_right _ _).trans (by linarith only [hsel])
    · simp only [cap, if_neg hp]
      linarith only [hcoord 2]
  have hresU : typedResidual p v ≤ 1 := by
    dsimp only [typedResidual, U11SelectedLargest.prefixSum]
    linarith only [hcap, hcoord 0, hcoord 1, hcoord 2, hcoord 3]
  have hresL := typedEligible_residual_gt_smallest p v he
  exact ⟨(hb.1 3).trans hresL.le, hresU, hb.1 3, (hb.2 3).trans (by norm_num)⟩

theorem target_cost_eq (p : Policy) (v : LogFour) :
    originalCost (typedResidual p v) (v 3) = ordinaryKernel H248 residual p.val v := by
  simp only [originalCost, ordinaryKernel, residual, dif_pos p.isLt]

theorem physicalCost_bounds {R w τ ξ ρ : ℝ}
    (hR : cubeFloor ≤ R) (hτ : 0 ≤ τ) (hτsmall : τ ≤ cubeFloor / 2) :
    0 ≤ physicalCost R w τ ξ ρ ∧ physicalCost R w τ ξ ρ ≤ badCostBound := by
  have hd : cubeFloor / 2 ≤ R - τ := by linarith only [hR, hτsmall]
  have hd0 : 0 < R - τ := (half_pos cubeFloor_pos).trans_le hd
  have hH := H248_bounds (physicalQuery R w τ ξ ρ)
  have hNum0 : 0 ≤ 4 * (1 - H248 (physicalQuery R w τ ξ ρ)) := by linarith only [hH.2]
  have hNum4 : 4 * (1 - H248 (physicalQuery R w τ ξ ρ)) ≤ 4 := by linarith only [hH.1]
  refine ⟨div_nonneg hNum0 hd0.le, ?_⟩
  have hh := (div_le_div_of_nonneg_right hNum4 hd0.le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4) (half_pos cubeFloor_pos) hd)
  have hConst : (4 : ℝ) / (cubeFloor / 2) = badCostBound := by norm_num [cubeFloor, badCostBound]
  simpa only [physicalCost, hConst] using hh

def pointError (δ e : ℝ) (v : LogFour) : ℝ := if v ∈ knotStrip δ then badCostBound else e

theorem pointError_nonneg {δ e : ℝ} (he : 0 ≤ e) (v : LogFour) : 0 ≤ pointError δ e v := by
  by_cases h : v ∈ knotStrip δ <;> simp only [pointError, h, if_true, if_false]
  · exact badCostBound_pos.le
  · exact he

theorem ordinary_upper (mask : Set (ℝ × ℝ)) (p : Policy) {v : LogFour}
    (hv : v ∈ originalDomain mask) (hel : TypedEligible p v)
    {δ e : ℝ} (hd : 0 < δ) (he : 0 < e)
    {τ ξ ρ : Policy → ℝ} (hsmall : Small δ e τ ξ ρ) :
    physicalCost (typedResidual p v) (v 3) (τ p) (ξ p) (ρ p) ≤
      originalCost (typedResidual p v) (v 3) + pointError δ e v := by
  have hp := eligible_scalar_parameters mask p hv hel
  have hb := small_strict hd he hsmall p
  by_cases hbad : v ∈ knotStrip δ
  · have hτc : τ p ≤ cubeFloor / 2 := hb.2.1.le.trans (eta_bounds cubeFloor cubeFloor δ e).2.2.1
    have hCost := (physicalCost_bounds hp.1 hb.1 hτc).2
    have hOrig0 : 0 ≤ originalCost (typedResidual p v) (v 3) := by
      have hH := H248_bounds (max 2 (typedResidual p v / v 3))
      exact div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hH.2))
        ((cubeFloor_pos.trans_le hp.1).le)
    simp only [pointError, if_pos hbad]
    linarith only [hCost, hOrig0]
  · have hGood : Good (typedResidual p v) (v 3) δ := by
      by_cases hClamp : typedResidual p v ≤ 2 * v 3
      · exact Or.inl hClamp
      · refine Or.inr ⟨lt_of_not_ge hClamp, ?_⟩
        intro j
        have hh := actual_gap_separated_of_not_strip p v j δ hbad
        simpa only [policyGap, tableKnot, Nat.add_comm] using hh.le
    have hCost := physical_cost_upper_uniform cubeFloor_pos cubeFloor_pos hd he
      (typedResidual p v) (v 3) (τ p) (ξ p) (ρ p) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hGood
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
    simpa only [pointError, if_neg hbad] using hCost

def bufferedOrdinary (τ ξ ρ : Policy → ℝ) (j : ℕ) (v : LogFour) : ℝ :=
  if hj : j < 16 then physicalCost (typedResidual ⟨j,hj⟩ v) (v 3)
    (τ ⟨j,hj⟩) (ξ ⟨j,hj⟩) (ρ ⟨j,hj⟩) else 0

def targetEnvelope (v : LogFour) : ℝ := envelope bank
  (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab) (ordinaryKernel H248 residual)) v

def bufferedEnvelope (τ ξ ρ : Policy → ℝ) (v : LogFour) : ℝ := envelope bank
  (guarded eligible (switchedKernel currentK LiLiuPrereqBuchstab.buchstab) (bufferedOrdinary τ ξ ρ)) v

/-- A one-sided error passes through the ACTUAL guarded sixteen minimum
once. The original switched fallback and actual eligibility stay fixed. -/
theorem envelope_upper (mask : Set (ℝ × ℝ)) {v : LogFour}
    (hv : v ∈ originalDomain mask) {δ e : ℝ} (hd : 0 < δ) (he : 0 < e)
    {τ ξ ρ : Policy → ℝ} (hsmall : Small δ e τ ξ ρ) :
    bufferedEnvelope τ ξ ρ v ≤ targetEnvelope v + pointError δ e v := by
  apply envelope_le_add
  intro tag htag
  rcases Finset.mem_insert.mp htag with rfl | htag
  · simp only [guarded, if_pos rfl]
    linarith only [pointError_nonneg he.le v]
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp htag
    have hj16 : j < 16 := Finset.mem_range.mp hj
    by_cases hel : eligible j v
    · have hel' : TypedEligible ⟨j,hj16⟩ v := by simpa only [eligible, dif_pos hj16] using hel
      have hh := ordinary_upper mask ⟨j,hj16⟩ hv hel' hd he hsmall
      rw [target_cost_eq] at hh
      simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_pos hel,
        bufferedOrdinary, dif_pos hj16] using hh
    · simp only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_neg hel]
      linarith only [pointError_nonneg he.le v]

end

end ImbalancedChen.P5Z.BufferedActualSixteenError
