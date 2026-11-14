import ImbalancedChen.Part3OriginalPositiveMarkOrder
import ImbalancedChen.Part3OriginalSwitchedPaidReturn

/-! Eliminate the true high-order remainder on the positive-frequency row.
These estimates take the complete exceptional sum on both sides of the
level switch. -/
namespace ImbalancedChen.Part3.OriginalFullPositiveLevelSwitch20261113
noncomputable section
open Finset Complex
open scoped Classical BigOperators MatrixGroups
open OriginalPositiveMarkOrder20261113 (high_positive_zero)
open ActualCuspBasisWhittakerCoefficients20261102 (basisRhoK basisR_eq_half_native)
open OriginalSameInfinityTensorSpectrum20261113 (disc)
open OriginalSwitchedIntervalTraceSlots20261113 (slot input output)
open OriginalSwitchedInitialTraceGeometry20261113 (mark)
open OriginalSwitchedInitialProjection20261113 (bandEnergy outsideSlot)
open OriginalSwitchedFiniteSectorBalance20261113 (high)
open OriginalSwitchedIntervalReturn20261113 (retained)
open OriginalSwitchedNativePrefixEnergy20261113 (intervalEnergy)
open OriginalSwitchedMellinRows20261113 (twistedRow nativeRow)
open OriginalSwitchedReturnedWindow20261113 (prefixMax)
open OriginalSwitchedActiveLevels20261113 (inScale outScale)
open OriginalSwitchedPaidReturn20261113 (allowance)
open OriginalExceptionalJNativeCompletion20261110 (exceptional tau classicalLevels)
open OriginalClassicalSpectralSupports20261102 (classicalMScale)

local instance (q : ℕ+) : NeZero q.val := ⟨q.property.ne'⟩

theorem rho_zero (q m : ℕ+) (i : ↥(exceptional q)) (hi : 3/4<tau q i.val) :
    basisRhoK q.val q.property i.val 1 (m.val:ℤ)=0 := by
  have h := high_positive_zero q m i hi
  rw [basisR_eq_half_native q.val q.property i.val 1 (by exact_mod_cast m.property.ne')] at h
  exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)

private theorem row_zero (q : ℕ+) (i : ↥(exceptional q)) (hi : 3/4<tau q i.val)
    {a : ℕ} (ap : 0<a) (b : ℕ) (ω t : ℝ) : twistedRow (Ico a b) (nativeRow q i.val ω) t=0 := by
  apply sum_eq_zero
  intro m hm
  have mpos : 0<m := ap.trans_le (mem_Ico.mp hm).1
  simp only [nativeRow,rho_zero q ⟨m,mpos⟩ i hi,mul_zero,zero_mul]

private theorem all_weights (L : Finset ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y ω : ℝ) :
    bandEnergy L (3/4) Y ω a b=intervalEnergy L Y ω a b 0 := by
  apply sum_congr rfl
  intro q _
  change (∑ i∈retained (3/4) q,_)=∑ i : ↥(exceptional q),_
  unfold retained
  rw [sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hi : tau q i.val≤3/4
  · rw [if_pos hi]
  · simp only [if_neg hi,row_zero q i (lt_of_not_ge hi) ap b ω 0,norm_zero,zero_pow (by decide : (2:ℕ)≠0),mul_zero]

private theorem zero_slot (q : ℕ+) (i : ↥(exceptional q)) (hi : 3/4<tau q i.val) {a : ℕ}
    (ap : 0<a) (b : ℕ) (ω : ℝ) (W : ℕ→ℕ→ℂ) : slot q i ap b ω W=0 := by
  apply sum_eq_zero
  intro m _
  apply sum_eq_zero
  intro n _
  have z := high_positive_zero q (mark a ap m) i hi
  simp only [disc,z,star_zero,zero_mul,mul_zero]

private theorem outside_zero (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y ω : ℝ) :
    outsideSlot q ap b (3/4) Y ω=0 := by
  apply sum_eq_zero
  intro i _
  by_cases h : 3/4<tau q i.val
  · rw [if_pos h];exact zero_slot q i h ap b ω _
  · rw [if_neg h]

private theorem high_zero (s : Bool) (q : ℕ+) {a : ℕ} (ap : 0<a) (b : ℕ) (Y Q ω : ℝ) :
    high s q ap b (3/4) Y Q ω=0 := by
  apply sum_eq_zero
  intro i _
  by_cases h : 3/4<tau q i.val
  · rw [if_pos h]
    cases s <;> exact zero_slot q i h ap b ω _
  · rw [if_neg h]

theorem initial {ε : ℝ} (ep : 0<ε) :
    ∃ c K Y₀ : ℝ,0<c ∧ 0<K ∧ 1≤Y₀ ∧
    ∀ (j a b : ℕ) (lo : 2^j≤a),a≤b → b≤2^(j+1) → ∀ (Y Q ω : ℝ),Y₀≤Y → 0<Q →
    let M := classicalMScale j
    c*intervalEnergy (classicalLevels Q) Y ω a b 0≤
      K*(((1+M)*(1+Y))^ε*(M+Y)*M+allowance Y*(Q+M^(1+ε))*M) := by
  obtain ⟨c,K,Z,cp,kp,z1,F⟩ := OriginalSwitchedPaidReturn20261113.initial
    (by norm_num : (0:ℝ)≤3/4) (by norm_num) ep
  refine ⟨c,K,Z,cp,kp,z1,fun j a b lo ab hi Y Q ω hy qp => ?_⟩
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  simpa only [all_weights _ ap,outside_zero,norm_zero,Finset.sum_const_zero,mul_zero,add_zero] using F j a b lo ab hi Y Q ω hy qp

theorem recurrence {ε : ℝ} (ep : 0<ε) :
    ∃ c K D Y₀ : ℝ,0<c ∧ 0<K ∧ 0≤D ∧ 1≤Y₀ ∧
    ∀ Y≥Y₀,∀ (Q ω : ℝ),0<Q → ∀ (j a b : ℕ) (lo : 2^j≤a) (ab : a≤b),b≤2^(j+1) →
    let M := classicalMScale j
    c*intervalEnergy (classicalLevels Q) Y ω a b 0≤
      K*(∑ l∈range 6,prefixMax (classicalLevels (outScale j Y Q l)) Y ω a b ab+
        Y^ε*(outScale j Y Q l+M)*M)+
      4*(D*allowance Y*((∑ l∈range 6,(outScale j Y Q l+M^(1+ε))*M)+
         (∑ l∈range 4,(inScale Q l+M^(1+ε))*M))) := by
  obtain ⟨c,K,D,Z,cp,kp,dp,z1,F⟩ := OriginalSwitchedPaidReturn20261113.recurrence
    (by norm_num : (0:ℝ)≤3/4) (by norm_num) ep
  refine ⟨c,K,D,Z,cp,kp,dp,z1,fun Y hy Q ω qp j a b lo ab hi => ?_⟩
  let ap := (pow_pos (by norm_num : (0:ℕ)<2) j).trans_le lo
  simpa only [all_weights _ ap,high_zero,norm_zero,sum_const_zero,zero_add] using F Y hy Q ω qp j a b lo ab hi

end
end ImbalancedChen.Part3.OriginalFullPositiveLevelSwitch20261113
