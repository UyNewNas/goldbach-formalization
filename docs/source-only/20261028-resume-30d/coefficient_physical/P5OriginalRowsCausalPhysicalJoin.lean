import ImbalancedChen.P5OriginalPhysicalFullPolicyFibre
import ImbalancedChen.P4AOriginalVariableFifthPhysicalLedger
import ImbalancedChen.P1Pair12RetainedSignedSource

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The earlier physicalPolicy used finalPolicy (the corrected second/third
fallback parent) directly below its sixth/eighth splices. Its through-sixth
identity therefore did NOT contain the original fourth/fifth row maxima.
This file constructs a DIFFERENT explicit joined policy whose base is the
actual original policy5, with the unchanged original fourth licence and
literal fourth/fifth row banks. It proves the original fifth decisions and
frontiers survive through rank six, and derives one same-rho pointwise
majorant plus an exact attached-density telescope at the ACTUAL 4/5/6/8
frontiers. Fifth changes act after rank FOUR, before fifth admission.

There is no assertion that this joined policy equals the earlier fallback
physicalPolicy or is the complete adopted all22 policy. The common causal
refinement with the second/third fallback actions, the selected full sixth
cap instance, all87 eighth ownership, support inflation and K remain open.
All cap/licence/row inputs below are original data, not density conclusions.
-/

namespace ImbalancedChen.P5OriginalRowsCausalPhysicalJoin

noncomputable section
open scoped Classical BigOperators
open P2OriginalFourthCapProducerInterface
open P5OriginalAdoptedEighthPhysicalMasks
open P1Pair12RetainedSignedSource

/-- Original finite inputs only. In particular licensed4 is NOT replaced
by a checker flag or an assumed equality of licences. -/
structure Inputs where
  e : ℚ
  chi : ℝ
  m : ℕ
  omega : ℝ
  rows4 : Finset ProducerRow
  licensed4 : ProducerRow → Prop
  J5 : Finset (P1OriginalVariableFifthContinuation.Label5 m)
  rows5 : Finset (P1OriginalVariableFifthContinuation.FifthRow m)
  lambda3 : List ℕ → ℝ
  lambda6 : List ℕ → ℝ

inductive Stage where
  | third | fourth | fifth | sixth | eighth

inductive Action where
  | fourth | fifth | sixth | eighth

def parentStage : Action → Stage
  | .fourth => .third
  | .fifth => .fourth
  | .sixth => .fifth
  | .eighth => .sixth

def nextStage : Action → Stage
  | .fourth => .fourth
  | .fifth => .fifth
  | .sixth => .sixth
  | .eighth => .eighth

def rank : Action → ℕ
  | .fourth => 4
  | .fifth => 4
  | .sixth => 6
  | .eighth => 8

/-- Each stage names a real existing source policy, not an arbitrary
caller policy with an imposed source/density identity. -/
def policy (d : Inputs) (s : Stage) (N : ℝ) : Bool → List ℕ → Bool :=
  match s with
  | .third => HistoricalThirdCoarse.policy (d.e : ℝ) d.chi d.m d.omega N
  | .fourth => P1OriginalVariableFourthContinuation.producerPolicy4
      (d.e : ℝ) d.chi d.m d.omega N d.rows4 d.licensed4
  | .fifth => P1OriginalVariableFifthContinuation.policy5
      d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5
  | .sixth => P5OriginalAdoptedEighthPhysicalMasks.parentPolicy N d.lambda6
      (P1OriginalVariableFifthContinuation.policy5
        d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5)
  | .eighth => familyPolicy N d.lambda3 d.lambda6
      (P1OriginalVariableFifthContinuation.policy5
        d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5)

def replacement (d : Inputs) (a : Action) (N : ℝ) : Bool → List ℕ → Bool :=
  match a with
  | .fourth => frozenParityRosserPolicy false 4
      (P1OriginalVariableFourthContinuation.producerLevel4
        (d.e : ℝ) d.chi d.m d.omega N d.rows4 d.licensed4)
  | .fifth => frozenParityRosserPolicy false 5
      (P1OriginalVariableFifthContinuation.level5
        d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5)
  | .sixth => frozenParityRosserPolicy false 6 (fun pre => N ^ d.lambda6 pre)
  | .eighth => frozenParityRosserPolicy false 8
      (fun pre => N ^ raisedExponent N d.lambda3 d.lambda6 pre)

/-- The fifth continuation is the replacement of the CURRENT fourth
continuation at their shared rank-four frontier, not a rank-five splice. -/
theorem next_policy_eq_actual_splice (d : Inputs) (a : Action) (N : ℝ) :
    policy d (nextStage a) N =
      firstExitDepthSplicePolicy (rank a) (policy d (parentStage a) N)
        (replacement d a N) := by
  cases a with
  | fourth => rfl
  | fifth =>
      change firstExitDepthSplicePolicy 4 _ _ =
        firstExitDepthSplicePolicy 4 (firstExitDepthSplicePolicy 4 _ _) _
      exact (firstExitDepthSplicePolicy_absorb 4 _ _ _).symm
  | sixth => rfl
  | eighth => rfl

theorem policy_even (d : Inputs) (s : Stage) (N : ℝ) (pre : List ℕ) :
    policy d s N true pre = true := by
  cases s with
  | third => exact HistoricalThirdCoarse.policy_even (d.e : ℝ) d.chi d.m d.omega N pre
  | fourth => exact P4AOriginalVariableFifthPhysicalLedger.fourth_even
      d.e d.chi d.m d.omega d.rows4 d.licensed4 N pre
  | fifth => exact P4AOriginalVariableFifthPhysicalLedger.fifth_even
      d.e d.chi d.m d.omega d.rows4 d.licensed4 d.J5 d.rows5 N pre
  | sixth => exact P4AOriginalEighthParentPhysicalLedger.parent_even
      N d.lambda6 (policy d .fifth N)
      (P4AOriginalVariableFifthPhysicalLedger.fifth_even
        d.e d.chi d.m d.omega d.rows4 d.licensed4 d.J5 d.rows5 N) pre
  | eighth => exact family_even N d.lambda3 d.lambda6 (policy d .fifth N)
      (P4AOriginalVariableFifthPhysicalLedger.fifth_even
        d.e d.chi d.m d.omega d.rows4 d.licensed4 d.J5 d.rows5 N) pre

/-- The full original fifth policy, including its original row licence,
remains unchanged at EVERY query through the selected sixth rank. -/
theorem eighth_through_sixth_eq_original_fifth
    (d : Inputs) (N : ℝ) (positive : Bool) (pre : List ℕ)
    (hlen : pre.length ≤ 6) :
    policy d .eighth N positive pre = policy d .fifth N positive pre := by
  have h8 : pre.length ≤ 8 := hlen.trans (by decide)
  simp [policy, familyPolicy, P5OriginalAdoptedEighthPhysicalMasks.parentPolicy,
    P4AOriginalEighthParentPhysicalLedger.parentPolicy,
    P4AActualSixthFrozenEighthAdmission.sixthPolicy,
    firstExitDepthSplicePolicy, hlen, h8]

/-- A retained prefix's full state is preserved, including mass, sign and
remaining carrier. This does not identify an ideal cap with an old level. -/
theorem action_preserves_parent_frontier
    (d : Inputs) (a : Action) (N : ℝ) (k : ℕ) (hk : k ≤ rank a)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier k (policy d (nextStage a) N) h pre positive mass carrier =
      firstExitDepthFrontier k (policy d (parentStage a) N) h pre positive mass carrier := by
  rw [next_policy_eq_actual_splice d a N]
  exact firstExitDepthFrontier_depthSplice_eq k (rank a) hk _ _ h pre carrier positive mass

/-- At rank five the actual row maximum is used before the odd test.
No old fifth surrogate or constant stored cap replaces exponent5. -/
theorem joined_actual_fifth_test
    (d : Inputs) (N : ℝ) (pre : List ℕ) (hlen : pre.length = 5) :
    policy d .eighth N false pre =
      decide (ordinaryRosserPrefixAdmissible false
        (N ^ P1OriginalVariableFifthContinuation.exponent5
          d.e d.chi d.m d.omega N d.rows4 d.licensed4 d.J5 d.rows5 pre) pre) := by
  rw [eighth_through_sixth_eq_original_fifth d N false pre (by omega)]
  simp [policy, P1OriginalVariableFifthContinuation.policy5, fifthCappedUpperPolicy,
    firstExitDepthSplicePolicy, hlen, frozenParityRosserPolicy, ancestorFrozenPolicy,
    ordinaryParityRosserPolicy, oddFirstExitPolicy, rosserAncestor,
    P1OriginalVariableFifthContinuation.level5]

/-- Same exact final coefficient for all pointwise and density uses. -/
def finalRho (d : Inputs) (N cap : ℕ) (w z L : ℝ) : ℕ → ℝ :=
  actualSmallRoughRho ((policy d .eighth (N : ℝ)) false) N cap w z L

def finalModuli (d : Inputs) (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  actualSmallRoughModuli ((policy d .eighth (N : ℝ)) false) N cap w z

/-- The earlier local H3 fibre now uses this P4/P5-wired final coefficient,
not the previously defined fallback-only physicalRho. -/
theorem joined_h3_local_rho_eq_final_mask
    (d : Inputs) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    P5OriginalH3LocalPhysicalQFibre.localRho
      ((policy d .eighth (N : ℝ)) false) N cap w z L d.lambda3 d.lambda6 q =
      if q ∈ P5OriginalH3LocalPhysicalQFibre.localModuli
        ((policy d .eighth (N : ℝ)) false) N cap w z d.lambda3 d.lambda6 then
        finalRho d N cap w z L q else 0 :=
  P5OriginalH3LocalPhysicalQFibre.localRho_eq_masked_global
    _ N cap w z L d.lambda3 d.lambda6 q

/-- Its H3-local rough leaves are genuine FULL joined-policy root leaves. -/
theorem joined_h3_local_leaves_eq_full
    (d : Inputs) (N cap : ℕ) (w z : ℝ) :
    P5OriginalH3LocalPhysicalQFibre.localLeaves
      ((policy d .eighth (N : ℝ)) false) N cap w z d.lambda3 d.lambda6 =
      ((firstExitRootLeaves (policy d .eighth (N : ℝ)) (fun _ => 1)
        (roughPrimeUniverse N cap w z)).toFinset).filter
          (P5OriginalH3LocalPhysicalQFibre.H3Leaf N d.lambda3 d.lambda6) := by
  have ho := UpperPolicyFiniteBridge.oddFirstExitPolicy_eq_of_even_retained
    (policy d .eighth (N : ℝ)) (policy_even d .eighth (N : ℝ))
  unfold P5OriginalH3LocalPhysicalQFibre.localLeaves
    oddFirstExitRetainedLeaves firstExitRootLeaves
  rw [ho]

/-- Original pointwise rough-indicator majorant for this explicitly
P4/P5-wired coefficient, including every integer n, zero and negatives. -/
theorem joined_same_rho_pointwise_majorant
    (d : Inputs) (N cap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ))
    (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (finalModuli d N cap w z) (finalRho d N cap w z L) n.natAbs :=
  actualSmallRoughRho_majorant ((policy d .eighth (N : ℝ)) false)
    N cap w z L hL hwL hwz hzcap n

def density (d : Inputs) (s : Stage) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  physicalDensitySum (actualSmallRoughModuli ((policy d s (N : ℝ)) false) N cap w z)
    (actualSmallRoughRho ((policy d s (N : ℝ)) false) N cap w z L)

/-- The small beta choice and the entire physical totient stay inside
this SAME terminal test at every stage and every signed frontier. -/
def densityTerminal (N cap : ℕ) (w L : ℝ) : Bool → List ℕ → ℝ :=
  attachedLeafTest N cap 1 w L (fun q => 1 / (Nat.totient q : ℝ))

theorem density_eq_actual_signed_root
    (d : Inputs) (s : Stage) (N cap : ℕ) (w z L : ℝ) :
    density d s N cap w z L =
      signedTest (policy d s (N : ℝ)) (fun _ => 1) (densityTerminal N cap w L)
        [] true 1 (roughPrimeUniverse N cap w z) := by
  have hf := physical_test_eq_signedTest (policy d s (N : ℝ))
    (policy_even d s (N : ℝ)) N cap 1 w z L
    (fun q => 1 / (Nat.totient q : ℝ))
  simpa [density, densityTerminal, physicalDensitySum, div_eq_mul_inv] using hf

/-- A direct full-root-leaf form of each actual stage's physical density. -/
theorem density_eq_actual_root_leaves
    (d : Inputs) (s : Stage) (N cap : ℕ) (w z L : ℝ) :
    density d s N cap w z L =
      ((firstExitRootLeaves (policy d s (N : ℝ)) (fun _ => 1)
        (roughPrimeUniverse N cap w z)).map
          (fun leaf => leaf.value * densityTerminal N cap w L leaf.positive leaf.selected)).sum := by
  rw [density_eq_actual_signed_root]
  exact signedTest_eq_leaves _ _ _ [] _ true 1

/-- NEW minus CURRENT-parent attached density on the exact actual frontier.
No positivity, unordered factorial or individual integral gain is assumed. -/
def densityChange (d : Inputs) (a : Action) (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ((firstExitDepthFrontier (rank a) (policy d (parentStage a) (N : ℝ))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N cap w z)).map
      (fun state =>
        signedTest (replacement d a (N : ℝ)) (fun _ => 1)
          (densityTerminal N cap w L) state.selectedPrefix state.positive state.mass state.remaining -
        signedTest (policy d (parentStage a) (N : ℝ)) (fun _ => 1)
          (densityTerminal N cap w L) state.selectedPrefix state.positive state.mass state.remaining)).sum

theorem actual_density_change_eq_frontier
    (d : Inputs) (a : Action) (N cap : ℕ) (w z L : ℝ) :
    density d (nextStage a) N cap w z L - density d (parentStage a) N cap w z L =
      densityChange d a N cap w z L := by
  rw [density_eq_actual_signed_root, density_eq_actual_signed_root,
    next_policy_eq_actual_splice d a (N : ℝ)]
  exact signedTest_splice_sub_eq_frontier (rank a) _ _ (fun _ => 1)
    (densityTerminal N cap w L) [] (roughPrimeUniverse N cap w z) true 1

/-- Exact finite 3→4→5→6→8 ledger. Each earlier saving is retained once,
and every later change is charged to its real CURRENT parent. -/
theorem joined_same_rho_finite_density_telescope
    (d : Inputs) (N cap : ℕ) (w z L : ℝ) :
    physicalDensitySum (finalModuli d N cap w z) (finalRho d N cap w z L) =
      density d .third N cap w z L + densityChange d .fourth N cap w z L +
        densityChange d .fifth N cap w z L + densityChange d .sixth N cap w z L +
        densityChange d .eighth N cap w z L := by
  have h4 := actual_density_change_eq_frontier d .fourth N cap w z L
  have h5 := actual_density_change_eq_frontier d .fifth N cap w z L
  have h6 := actual_density_change_eq_frontier d .sixth N cap w z L
  have h8 := actual_density_change_eq_frontier d .eighth N cap w z L
  simp only [nextStage, parentStage] at h4 h5 h6 h8
  change density d .eighth N cap w z L = _
  linarith

end
end ImbalancedChen.P5OriginalRowsCausalPhysicalJoin
