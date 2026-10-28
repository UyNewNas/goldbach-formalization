import ImbalancedChen.P5OriginalH3LocalPhysicalQFibre
import ImbalancedChen.P5OriginalAboveMuThirdLowerPhysicalCoefficient
import ImbalancedChen.ActualUpperPolicyFiniteBridge

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The corrected Phase7 third selected-pair action is globally an UPPER
parity policy: thirdReplacement uses ordinaryParityRosserPolicy false.
The term "lower residual" describes the relative continuation after the
odd third prefix; it does not flip the global Bool policy to lower=true.
Its proved final_even is therefore exactly the missing input required
by family_even. This file derives physicalPolicy's global even retention
and identifies its FULL root leaves with the oddified root leaves used
by the actual coefficient. It then upgrades the local H3 q-fibre to the
full corrected physical policy, removing the earlier conditional topology
boundary for this specific source version.

The general identification is stated with its exact necessary and
sufficient even-retained condition. No such equality is asserted for an
arbitrary Bool policy. No global cap supplier, 87-domain geometry,
pointwise majorant, density telescope, PP estimate or K is supplied here.
-/

namespace ImbalancedChen.P5OriginalPhysicalFullPolicyFibre

noncomputable section
open scoped Classical BigOperators
open P5OriginalAdoptedEighthPhysicalMasks
open P5OriginalH3Cell00StrictOldPlanes
open P5OriginalH3LocalPhysicalQFibre
open P5OriginalAboveMuThirdLowerPhysicalCoefficient

/-- This is the exact condition for identifying an arbitrary Bool policy
with its oddification; a one-sided sign heuristic is insufficient. -/
theorem oddification_eq_iff_even_retained {α : Type*}
    (R : Bool → List α → Bool) :
    oddFirstExitPolicy (R false) = R ↔ ∀ pre, R true pre = true := by
  constructor
  · intro h pre
    have hv := congrFun (congrFun h true) pre
    simpa [oddFirstExitPolicy] using hv.symm
  · exact UpperPolicyFiniteBridge.oddFirstExitPolicy_eq_of_even_retained R

/-- The source's actual corrected third parent already proves final_even.
The sixth and eighth splices both preserve it by the existing family API. -/
theorem physical_even_retained
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ) :
    P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
      lambda3 lambda6 true pre = true := by
  exact family_even N lambda3 lambda6 (finalPolicy e chi m omega N)
    (final_even e chi m omega N) pre

theorem physical_oddification_eq
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    oddFirstExitPolicy
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
        lambda3 lambda6) false) =
      P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
        lambda3 lambda6 := by
  exact (oddification_eq_iff_even_retained _).2
    (physical_even_retained e chi m omega N lambda3 lambda6)

/-- Equality is of complete leaf records, including selected word, sign
and local mass, and holds for every local prime weight and carrier. -/
theorem physical_root_leaves_eq
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (h : ℕ → ℝ) (carrier : List ℕ) :
    oddFirstExitRetainedLeaves
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
        lambda3 lambda6) false) h carrier =
      firstExitRootLeaves
        (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
          lambda3 lambda6) h carrier := by
  unfold oddFirstExitRetainedLeaves firstExitRootLeaves
  rw [physical_oddification_eq e chi m omega N lambda3 lambda6]

/-- The physical rough support consists of full corrected-policy leaves. -/
theorem physical_fixed_support_eq_full
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    fixedRoughSupport
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) false) N cap w z =
      firstExitRetainedModuli
        (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
          (N : ℝ) lambda3 lambda6) (roughPrimeUniverse N cap w z) := by
  exact UpperPolicyFiniteBridge.fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    _ (physical_even_retained e chi m omega (N : ℝ) lambda3 lambda6) N cap w z

/-- Mobius lookup is also unchanged, so support equality does not leave
a separately indexed coefficient or sign convention behind. -/
theorem physical_fixed_coefficient_eq_full
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (d : ℕ) :
    fixedRoughCoefficient
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) false) N cap w z d =
      (firstExitRetainedCoefficient
        (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
          (N : ℝ) lambda3 lambda6) (roughPrimeUniverse N cap w z) d : ℝ) := by
  exact UpperPolicyFiniteBridge.fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    _ (physical_even_retained e chi m omega (N : ℝ) lambda3 lambda6) N cap w z d

/-- The exact physical rho is the sign-sensitive small attachment to the
FULL policy's fixed modulus and Mobius coefficient, at the same q. -/
theorem physical_rho_eq_full_attachment
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    P5OriginalPhaseBPhysicalBinding.physicalRho e chi m omega N cap
      w z L lambda3 lambda6 =
    smallRoughRho (actualSmallRosserSupport N cap w)
      (firstExitRetainedModuli
        (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
          (N : ℝ) lambda3 lambda6) (roughPrimeUniverse N cap w z))
      (fun d => (firstExitRetainedCoefficient
        (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
          (N : ℝ) lambda3 lambda6) (roughPrimeUniverse N cap w z) d : ℝ))
      (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  exact UpperPolicyFiniteBridge.actualSmallRoughRho_eq_firstExitAttachment
    _ (physical_even_retained e chi m omega (N : ℝ) lambda3 lambda6) N cap w z L

/-- Earlier H3 local leaves are now identified with the corresponding
filter of the actual full policy's unit-weight root leaves. -/
theorem physical_h3_local_leaves_eq_full
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) :
    localLeaves
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) false) N cap w z lambda3 lambda6 =
      ((firstExitRootLeaves
        (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
          (N : ℝ) lambda3 lambda6) (fun _ => 1)
          (roughPrimeUniverse N cap w z)).toFinset).filter (H3Leaf N lambda3 lambda6) := by
  unfold localLeaves
  rw [physical_root_leaves_eq e chi m omega (N : ℝ) lambda3 lambda6]

/-- This exact membership statement can be used directly by a full-policy
frontier/leaf consumer; the oddification premise has been discharged. -/
theorem physical_h3_mem_local_leaf_iff
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (leaf : FirstExitLeaf ℕ) :
    leaf ∈ localLeaves
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) false) N cap w z lambda3 lambda6 ↔
    leaf ∈ firstExitRootLeaves
      (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) (fun _ => 1)
        (roughPrimeUniverse N cap w z) ∧ H3Leaf N lambda3 lambda6 leaf := by
  rw [physical_h3_local_leaves_eq_full e chi m omega N cap w z lambda3 lambda6]
  simp

/-- An active local physical q has one small-factor/full-policy-leaf
fibre, and its OWN actual eighth ancestor carries the selected mask/cap. -/
theorem physical_h3_active_unique_full_root_fibre
    (e chi : ℝ) (m : ℕ) (omega : ℝ) (N cap : ℕ) (w z L : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (q : ℕ)
    (hq : localRho
      ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
        (N : ℝ) lambda3 lambda6) false) N cap w z L lambda3 lambda6 q ≠ 0) :
    let retainOdd := (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
      (N : ℝ) lambda3 lambda6) false
    ∃! x : Pair,
      (x.1 ∈ actualSmallRosserSupport N cap w ∧
        (x.2 ∈ firstExitRootLeaves
          (P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
            (N : ℝ) lambda3 lambda6) (fun _ => 1)
            (roughPrimeUniverse N cap w z) ∧ H3Leaf N lambda3 lambda6 x.2)) ∧
      pairModulus x = q ∧ (x.1 : ℝ) < L ∧
      P5OriginalPhaseBPhysicalBinding.physicalRho e chi m omega N cap
        w z L lambda3 lambda6 q = atom retainOdd N cap w z L x ∧
      ∃ h : adoptedGuard (N : ℝ) lambda3 lambda6 (eighthAncestor x.2),
        selectedMask (Classical.choose h) = mask138 ∧
        raisedExponent (N : ℝ) lambda3 lambda6 (eighthAncestor x.2) =
          newCap slot (primeHistoryLogCoordinates (N : ℝ) 8 (eighthAncestor x.2)) := by
  dsimp only
  have hf := active_q_unique_local_fibre
    ((P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega
      (N : ℝ) lambda3 lambda6) false) N cap w z L lambda3 lambda6 q hq
  simpa only [localPairs, Finset.mem_product,
    physical_h3_mem_local_leaf_iff e chi m omega N cap w z lambda3 lambda6,
    P5OriginalPhaseBPhysicalBinding.physicalRho] using hf

/-- Exact branch scope before the sixth splice: the selected third
fallback has even global nodes retained and odd global tests at its raised
UPPER admissibility level. "Lower residual" does not change this flag. -/
theorem physical_third_branch_global_upper_tests
    (e chi : ℝ) (m : ℕ) (omega N : ℝ)
    (lambda3 lambda6 : List ℕ → ℝ) (pre : List ℕ)
    (hlo : 3 < pre.length) (hhi : pre.length ≤ 6)
    (hguard : thirdGuard N pre) :
    P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
      lambda3 lambda6 true pre = true ∧
    P5OriginalPhaseBPhysicalBinding.physicalPolicy e chi m omega N
      lambda3 lambda6 false pre =
      decide (ordinaryRosserPrefixAdmissible false
        (thirdQ N (rosserAncestor 3 pre)) pre) := by
  refine ⟨physical_even_retained e chi m omega N lambda3 lambda6 pre, ?_⟩
  rw [P5OriginalPhaseBPhysicalBinding.through_sixth_eq_corrected_parent
    e chi m omega N lambda3 lambda6 false pre hhi]
  exact third_hit_odd_test e chi m omega N pre hlo hguard

end
end ImbalancedChen.P5OriginalPhysicalFullPolicyFibre
