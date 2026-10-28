import ImbalancedChen.P2UpperActualFiniteKnotMass
import ImbalancedChen.P5ZU1011JointNearCapPrimeReserve

/-! SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The same actual static selected row is attached to the proved all-policy
joint native reserve. This pays its full clamp cost with the genuine
prime-box/Mertens supplier already used by that reserve. No H248 count
or native-density identification is inferred from the cost comparison. -/

namespace ImbalancedChen.P2UpperActualSelectedClampReserve

noncomputable section
open scoped Classical BigOperators
open P5Z U11Integral U1011OriginalSixteenPolicyBank
open U1011OriginalSixteenArithmeticProducts U1011OriginalFifteenNativeGridCells
open U1011OriginalSixteenStaticNativeCompiler (selectedPolicy ownerBox tupleTag)
open P5U1011JointOverlap JointNearCapPrimeReserve JointNearCapPointError

def clampKeep (n N : ℕ) (t : Four) : Prop :=
  tupleTag n N t ≠ 0 ∧ typedResidual (selectedPolicy n N t) (coordinates N t) ≤
    2 * coordinates N t 3

def selectedNativeCost (n N : ℕ) (t : Four) : ℝ :=
  U1011OriginalSixteenNearCapBoxProfiles.nativeCost
    (selectedPolicy n N t) (ownerBox n N t) (JointNearCapOwnerBinding.precision n)

def selectedOriginalCost (n N : ℕ) (t : Four) : ℝ :=
  ordinaryKernel Part5UpperTables.H248 residual (selectedPolicy n N t).val (coordinates N t)

def clampExcess (n N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ jointSelector N E,
    if clampKeep n N t then
      max 0 (selectedNativeCost n N t - selectedOriginalCost n N t) /
        (Nat.totient (fullPrefix t) : ℝ) else 0

def nativeClampCost (n N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ jointSelector N E,
    if clampKeep n N t then selectedNativeCost n N t /
      (Nat.totient (fullPrefix t) : ℝ) else 0

def originalClampCost (n N : ℕ) (E : ℕ × ℕ → Prop) : ℝ :=
  ∑ t ∈ jointSelector N E,
    if clampKeep n N t then selectedOriginalCost n N t /
      (Nat.totient (fullPrefix t) : ℝ) else 0

/-- The actual static selection is certified on its genuine owner box;
this identifies its positive excess with the existing actual policy map. -/
theorem selected_excess_eq_policyExcess (n N : ℕ) (t : Four)
    (ht : tupleTag n N t ≠ 0) :
    max 0 (selectedNativeCost n N t - selectedOriginalCost n N t) =
      policyExcess n (selectedPolicy n N t) (coordinates N t) := by
  have hc := (U1011OriginalSixteenStaticNativeCompiler.boxPolicy_certificate
    (ownerBox n N t) ht).2
  have hcert : JointNearCapOwnerBinding.Certified n (selectedPolicy n N t)
      (coordinates N t) := hc
  simp only [policyExcess, if_pos hcert, selectedNativeCost, selectedOriginalCost,
    JointNearCapOwnerBinding.nativeCost, JointNearCapOwnerBinding.ownerBox, ownerBox]

theorem jointMinimumError_nonneg (N n : ℕ) (E : ℕ × ℕ → Prop) (keep : Four → Prop) :
    0 ≤ jointMinimumError N n E keep := by
  unfold jointMinimumError jointMass
  apply Finset.sum_nonneg
  intro t ht
  split_ifs
  · exact div_nonneg (le_max_left _ _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem clampExcess_le_jointTotal (n N : ℕ) (E : ℕ × ℕ → Prop) :
    clampExcess n N E ≤ jointTotalError N n E (clampKeep n N) := by
  have hsum : clampExcess n N E ≤
      ∑ p : Policy, jointPolicyError N n E (clampKeep n N) p := by
    unfold clampExcess jointPolicyError jointMass
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro t ht
    by_cases hk : clampKeep n N t
    · simp only [if_pos hk]
      rw [selected_excess_eq_policyExcess n N t hk.1]
      have hh := Finset.single_le_sum
        (fun p (_ : p ∈ (Finset.univ : Finset Policy)) =>
          div_nonneg (policyExcess_nonneg n p (coordinates N t)) (Nat.cast_nonneg _))
        (Finset.mem_univ (selectedPolicy n N t))
      exact hh
    · simp only [if_neg hk, Finset.sum_const_zero, le_refl]
  unfold jointTotalError
  exact hsum.trans (le_add_of_nonneg_right (jointMinimumError_nonneg _ _ _ _))

theorem nativeClampCost_le_original_add_excess (n N : ℕ) (E : ℕ × ℕ → Prop) :
    nativeClampCost n N E ≤ originalClampCost n N E + clampExcess n N E := by
  unfold nativeClampCost originalClampCost clampExcess
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  by_cases hk : clampKeep n N t
  · simp only [if_pos hk]
    have hh : selectedNativeCost n N t ≤ selectedOriginalCost n N t +
        max 0 (selectedNativeCost n N t - selectedOriginalCost n N t) := by
      have h := le_max_right 0 (selectedNativeCost n N t - selectedOriginalCost n N t)
      linarith
    have hdiv := div_le_div_of_nonneg_right hh (Nat.cast_nonneg (Nat.totient (fullPrefix t)))
    simpa only [add_div] using hdiv
  · simp only [if_neg hk, zero_add, le_refl]

/-- Genuine reserve with m before N, the unchanged original moving E,
and no assumed wall/mass/mean estimate. The imported theorem internally
pays its actual prime-box mass by the pinned Mertens/PNT supplier. -/
theorem exists_actual_selected_clamp_reserve (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ m N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N → ∀ E : ℕ × ℕ → Prop,
      clampExcess m N E < epsilon ∧
        nativeClampCost m N E ≤ originalClampCost m N E + epsilon := by
  obtain ⟨delta, hd, m, N0, hN0, hpaid⟩ :=
    exists_uniform_joint_native_reserve epsilon hepsilon
  refine ⟨m, N0, hN0, ?_⟩
  intro N hN E
  have he := (clampExcess_le_jointTotal m N E).trans_lt
    (hpaid N hN E (clampKeep m N)).1
  exact ⟨he, (nativeClampCost_le_original_add_excess m N E).trans
    (add_le_add_left he.le _)⟩

end
end ImbalancedChen.P2UpperActualSelectedClampReserve
