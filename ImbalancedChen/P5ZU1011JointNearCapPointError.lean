import ImbalancedChen.P5ZU1011JointNearCapOwnerBinding

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
True full-cube pointwise native-profile errors for the JOINT source.
Both minima below use EXACTLY the same whole-box-certified bank. No lost
candidate is silently discarded and no low-band tuple is placed in D11.
-/

namespace ImbalancedChen.P5Z.JointNearCapPointError

noncomputable section

open Set
open Classical
open U11Integral U11H248 U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenKnotPayment U1011AdaptivePrimeError
open BufferedOrdinaryClamp BufferedUniformStrip BufferedActualSixteenError
open JointNearCapOwnerBinding
open Part5UpperTables Part5OriginalUpsilon5CausalDictionary

theorem cube_scalar_parameters (p : Policy) {v : LogFour} (hv : v ∈ cube)
    (hel : TypedEligible p v) :
    cubeFloor ≤ typedResidual p v ∧ typedResidual p v ≤ 1 ∧ cubeFloor ≤ v 3 ∧ v 3 ≤ 1 := by
  have hb := mem_logPrimeBox.mp hv
  have hcoord : ∀ i : Fin 4, 0 ≤ v i := fun i =>
    (show (0 : ℝ) ≤ (lower : ℝ) by norm_num [lower]).trans (hb i).1
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
  have hresL := typedEligible_residual_gt_smallest p v hel
  have hwL : cubeFloor ≤ v 3 := by simpa only [cubeFloor, lower] using (hb 3).1
  have hwU : v 3 ≤ 1 := (hb 3).2.le.trans (by norm_num [upper])
  exact ⟨hwL.trans hresL.le, hresU, hwL, hwU⟩

theorem actual_buffers_small (m : ℕ) {δ e : ℝ} (hstep : 12 * step m ≤ scale δ e) (v : LogFour) :
    Small δ e (fun p => tauMap m p v) (fun p => xiMap m p v) (fun p => rhoMap m p v) := by
  intro p
  have hb := buffer_bounds m p v
  exact ⟨hb.1, hb.2.1.trans hstep, hb.2.2.1, hb.2.2.2.1.trans hstep,
    hb.2.2.2.2.1, hb.2.2.2.2.2.trans hstep⟩

theorem certified_native_upper (m : ℕ) (p : Policy) {v : LogFour} (hv : v ∈ cube)
    (ht : Certified m p v) {δ e : ℝ} (hd : 0 < δ) (he : 0 < e)
    (hstep : 12 * step m ≤ scale δ e) :
    nativeCost m p v ≤ ordinaryKernel H248 residual p.val v + pointError δ e v := by
  have hel := certified_eligible m p hv ht
  have hp := cube_scalar_parameters p hv hel
  have hb := small_strict hd he (actual_buffers_small m hstep v) p
  rw [nativeCost_eq_physical m p hv ht, ← target_cost_eq p v]
  by_cases hbad : v ∈ knotStrip δ
  · have hτc : tauMap m p v ≤ cubeFloor / 2 := hb.2.1.le.trans
      (eta_bounds cubeFloor cubeFloor δ e).2.2.1
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
      (typedResidual p v) (v 3) (tauMap m p v) (xiMap m p v) (rhoMap m p v)
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hGood
      hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1 hb.2.2.2.2.2
    simpa only [pointError, if_neg hbad] using hCost

def policyExcess (m : ℕ) (p : Policy) (v : LogFour) : ℝ :=
  if Certified m p v then max 0 (nativeCost m p v - ordinaryKernel H248 residual p.val v) else 0

def certifiedNat (m : ℕ) (j : ℕ) (v : LogFour) : Prop :=
  if hj : j < 16 then Certified m ⟨j,hj⟩ v else False
def nativeOrdinary (m : ℕ) (j : ℕ) (v : LogFour) : ℝ :=
  if hj : j < 16 then nativeCost m ⟨j,hj⟩ v else 0
def nativeMinimum (m : ℕ) (v : LogFour) : ℝ := envelope bank
  (guarded (certifiedNat m) (switchedKernel currentK LiLiuPrereqBuchstab.buchstab) (nativeOrdinary m)) v
def targetMinimum (m : ℕ) (v : LogFour) : ℝ := envelope bank
  (guarded (certifiedNat m) (switchedKernel currentK LiLiuPrereqBuchstab.buchstab) (ordinaryKernel H248 residual)) v
def minimumExcess (m : ℕ) (v : LogFour) : ℝ := max 0 (nativeMinimum m v - targetMinimum m v)

theorem policyExcess_nonneg (m : ℕ) (p : Policy) (v : LogFour) : 0 ≤ policyExcess m p v := by
  unfold policyExcess
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

theorem policyExcess_le (m : ℕ) (p : Policy) {v : LogFour} (hv : v ∈ cube)
    {δ e : ℝ} (hd : 0 < δ) (he : 0 < e) (hstep : 12 * step m ≤ scale δ e) :
    policyExcess m p v ≤ pointError δ e v := by
  by_cases ht : Certified m p v
  · rw [policyExcess, if_pos ht]
    apply max_le (pointError_nonneg he.le v)
    have hh := certified_native_upper m p hv ht hd he hstep
    linarith only [hh]
  · rw [policyExcess, if_neg ht]
    exact pointError_nonneg he.le v

theorem minimumExcess_le (m : ℕ) {v : LogFour} (hv : v ∈ cube)
    {δ e : ℝ} (hd : 0 < δ) (he : 0 < e) (hstep : 12 * step m ≤ scale δ e) :
    minimumExcess m v ≤ pointError δ e v := by
  have hUpper : nativeMinimum m v ≤ targetMinimum m v + pointError δ e v := by
    apply envelope_le_add
    intro tag htag
    rcases Finset.mem_insert.mp htag with rfl | htag
    · simp only [guarded, if_pos rfl]
      linarith only [pointError_nonneg he.le v]
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp htag
      have hj16 : j < 16 := Finset.mem_range.mp hj
      by_cases ht : Certified m ⟨j,hj16⟩ v
      · have hh := certified_native_upper m ⟨j,hj16⟩ hv ht hd he hstep
        simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ,
          certifiedNat, nativeOrdinary, dif_pos hj16, if_pos ht] using hh
      · simp only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ,
          certifiedNat, dif_pos hj16, if_neg ht]
        linarith only [pointError_nonneg he.le v]
  exact max_le (pointError_nonneg he.le v) (by linarith only [hUpper])

end

end ImbalancedChen.P5Z.JointNearCapPointError
