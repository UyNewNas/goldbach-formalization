import ImbalancedChen.Part3OriginalSwitchedInitialProjection

/-! Restrict the public full-block mask estimates to the two common
endpoints occurring in the recursion, preserving their exact values. -/
namespace ImbalancedChen.Part3.OriginalSwitchedProjectionMask20261113
noncomputable section
open Finset Complex
open scoped BigOperators Classical
open MediumGlobalDyadicOwnership20261028 (dyadicWindow)
open private mark from ImbalancedChen.Part3OriginalSwitchedNativeBilinearTrace
open OriginalSwitchedTraceProjection20261113 (pair H R C)
open OriginalSwitchedHolTraceError20261113 (test component trace_dyadic)
open OriginalSwitchedRegularBlockExchange20261113 (principalBlock incomingBlock)
open OriginalSwitchedRegularMarkExchange20261113 (principal incoming)
open OriginalSwitchedRegularRows20261113 (amplitude)
open OriginalSameInfinityWeightedHol20261113 (holSum)
open OriginalClassicalSpectralSupports20261102 (classicalMScale classicalMScale_bounds)
open OriginalExceptionalJNativeCompletion20261110 (classicalLevels)
open OriginalRegularPacketTest20261113 (energy)
open ActualIntervalGeometricSumSourceOnly (phaseAt)

def mask (a b m : ℕ) : ℂ := if m∈Ico a b then 1 else 0

private theorem one_sum {α : Type*} [AddCommMonoid α] {S U : Finset ℕ} (sub : S⊆U) (f : ℕ→α) :
    (∑ n∈U,if n∈S then f n else 0)=∑ n∈S,f n := by
  classical
  rw [←Finset.sum_filter]
  congr 1
  ext n
  exact Finset.mem_filter.trans ⟨And.right,fun hn => ⟨sub hn,hn⟩⟩

private theorem masked (j a b : ℕ) (lo : 2^j≤a) (hi : b≤2^(j+1)) (ω : ℝ) (f : ℕ+→ℕ+→ℂ) :
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    (∑ m : ↥(dyadicWindow j),∑ n : ↥(dyadicWindow j),amplitude (mask a b) ω m.val n.val*f (mark m) (mark n))=
    pair ap b ω f := by
  let S := Ico a b
  let U := dyadicWindow j
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  let lift (m : ℕ) : ℕ+ := ⟨max 1 m,(by decide : (0:ℕ)<1).trans_le (le_max_left 1 m)⟩
  have sub : S⊆U := fun _ hn => Finset.mem_Ico.mpr ⟨lo.trans (Finset.mem_Ico.mp hn).1,
    lt_of_lt_of_le (Finset.mem_Ico.mp hn).2 hi⟩
  have ful (m : ↥U) : mark (j:=j) m=lift m.val := by
    apply Subtype.ext
    exact (max_eq_right (show 1≤m.val from (mark (j:=j) m).property)).symm
  have short (m : ↥S) : OriginalSwitchedInitialTraceGeometry20261113.mark a ap m=lift m.val := by
    apply Subtype.ext
    exact (max_eq_right (show 1≤m.val from (OriginalSwitchedInitialTraceGeometry20261113.mark a ap m).property)).symm
  let Z (m n : ℕ) := star (phaseAt ω m)*phaseAt ω n*f (lift m) (lift n)
  have eq (m n : ℕ) : amplitude (mask a b) ω m n*f (lift m) (lift n)=
      if m∈S then (if n∈S then Z m n else 0) else 0 := by
    change (star (phaseAt ω m*(if m∈S then 1 else 0))*(phaseAt ω n*(if n∈S then 1 else 0)))*
      f (lift m) (lift n)=_
    by_cases hm : m∈S <;> by_cases hn : n∈S <;> simp [hm,hn,Z]
  have inner (m : ℕ) : (∑ n∈U,if m∈S then (if n∈S then Z m n else 0) else 0)=
      if m∈S then ∑ n∈S,Z m n else 0 := by
    by_cases hm : m∈S
    · simpa only [if_pos hm] using one_sum sub (Z m)
    · simp only [if_neg hm,Finset.sum_const_zero]
  change (∑ m : ↥U,∑ n : ↥U,amplitude (mask a b) ω m.val n.val*f (mark (j:=j) m) (mark (j:=j) n))=
    ∑ m : ↥S,∑ n : ↥S,star (phaseAt ω m.val)*phaseAt ω n.val*
      f (OriginalSwitchedInitialTraceGeometry20261113.mark a ap m) (OriginalSwitchedInitialTraceGeometry20261113.mark a ap n)
  simp_rw [ful,short,eq]
  simp only [Finset.univ_eq_attach,Finset.sum_attach]
  simp_rw [inner]
  exact one_sum sub (fun m => ∑ n∈S,Z m n)

private theorem short_mass (j a b : ℕ) :
    energy (dyadicWindow j) (mask a b)≤2*classicalMScale j := by
  have z (m : ℕ) : ‖mask a b m‖^2≤1 := by unfold mask;split <;> norm_num
  have h := sum_le_sum (s:=dyadicWindow j) (fun m _ => z m)
  have card : (dyadicWindow j).card=2^j := by
    change (Ico (2^j) (2^(j+1))).card=2^j
    rw [Nat.card_Ico,pow_succ];omega
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,card] at h
  exact h.trans (by linarith only [(classicalMScale_bounds j).2.1])

theorem hol_price {ε : ℝ} (ep : 0<ε) :
    ∃ D : ℝ,0≤D ∧ ∀ (s : Bool) (j a b : ℕ) (lo : 2^j≤a),b≤2^(j+1) → ∀ (Y Q B ω : ℝ),
    1≤Y → 0<Q → 0<B →
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    let M := classicalMScale j
    (∑ d∈classicalLevels B,‖H s d ap b Y Q ω‖)≤D*(B+M^(1+ε))*M := by
  obtain ⟨D,dp,p⟩ := trace_dyadic ep
  refine ⟨2*D,by positivity,fun s j a b lo hi Y Q B ω y1 qp bp => ?_⟩
  let M := classicalMScale j
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  have mp : 0<M := (by norm_num : (0:ℝ)<1/2).trans_le (classicalMScale_bounds j).1
  have z (d : ℕ+) : component s d j Y Q ω (mask a b)=H s d ap b Y Q ω :=
    masked j a b lo hi ω (fun m n => holSum d m n (test s d Y Q m.val n.val))
  have src : (∑ d∈classicalLevels B,‖component s d j Y Q ω (mask a b)‖)≤
      D*(B+M^(1+ε))*energy (dyadicWindow j) (mask a b) := by
    cases s
    · exact (p j Y Q B ω y1 qp bp _).1
    · exact (p j Y Q B ω y1 qp bp _).2
  simp_rw [z] at src
  exact src.trans ((mul_le_mul_of_nonneg_left (short_mass j a b) (mul_nonneg dp
    (add_nonneg bp.le (Real.rpow_nonneg mp.le _)))).trans_eq (by dsimp only [M];ring))

theorem regular_mask (d : ℕ+) (j a b : ℕ) (lo : 2^j≤a) (hi : b≤2^(j+1)) (Y Q ω : ℝ) :
    let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
    principalBlock d j Y Q ω (mask a b)=R true d ap b Y Q ω ∧
    incomingBlock d j Y Q ω (mask a b)=C true d ap b Y Q ω :=
  ⟨masked j a b lo hi ω (fun m n => principal d m n (test true d Y Q m.val n.val)),
   masked j a b lo hi ω (fun m n => incoming d m n (test true d Y Q m.val n.val))⟩

end
end ImbalancedChen.Part3.OriginalSwitchedProjectionMask20261113
