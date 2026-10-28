import ImbalancedChen.P5OriginalCommonRefinedPreservation
import ImbalancedChen.P1Pair12RetainedSignedSource
import ImbalancedChen.P5OriginalH3LocalPhysicalQFibre

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact finite source, majorant and density identities for the independently
constructed common policy and literal eleven-family sixth supplier.
The same full physical q and same sign-sensitive small beta are retained
in counts, exact coprime means and density. No PP/density estimate is a premise.
The identities do not identify this policy with the archived adopted gain. -/
namespace ImbalancedChen.P5OriginalCommonRefinedSource
noncomputable section
open scoped Classical BigOperators
open P5OriginalCommonRefinedConstructor
open P1Pair12RetainedSignedSource

inductive Stage where
  | third | fourth | fifth | sixth | eighth
inductive Action where
  | fourth | fifth | sixth | eighth

def stagePolicy (d : OriginalData) (N : ℝ) : Stage → Bool → List ℕ → Bool
  | .third => common3 d N
  | .fourth => policy4 d N
  | .fifth => policy5 d N
  | .sixth => policy6 d N
  | .eighth => policy8 d N

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

def actionRank : Action → ℕ
  | .fourth => 4
  | .fifth => 4
  | .sixth => 6
  | .eighth => 8

def replacement (d : OriginalData) (N : ℝ) : Action → Bool → List ℕ → Bool
  | .fourth => frozenParityRosserPolicy false 4 (level4 d N)
  | .fifth => frozenParityRosserPolicy false 5 (level5 d N)
  | .sixth => frozenParityRosserPolicy false 6 (level6 d N)
  | .eighth => frozenParityRosserPolicy false 8 (fun pre => N ^
      P5OriginalAdoptedEighthPhysicalMasks.raisedExponent N (lambda3 d N) (lambda6 d N) pre)

theorem next_eq_actual_splice (d : OriginalData) (N : ℝ) (a : Action) :
    stagePolicy d N (nextStage a) = firstExitDepthSplicePolicy (actionRank a)
      (stagePolicy d N (parentStage a)) (replacement d N a) := by
  cases a with
  | fourth => rfl
  | fifth => exact (firstExitDepthSplicePolicy_absorb 4 _ _ _).symm
  | sixth => rfl
  | eighth => rfl

theorem stagePolicy_even (d : OriginalData) (N : ℝ) (s : Stage) (pre : List ℕ) :
    stagePolicy d N s true pre = true := by
  cases s with
  | third => exact common3_even d N pre
  | fourth => exact policy4_even d N pre
  | fifth => exact policy5_even d N pre
  | sixth => exact policy6_even d N pre
  | eighth => exact policy8_even d N pre

def source (d : OriginalData) (s : Stage) (N enumerationCap : ℕ) (w z L : ℝ)
    (G : ℕ → ℝ) : ℝ :=
  ∑ q ∈ actualSmallRoughModuli ((stagePolicy d (N : ℝ) s) false) N enumerationCap w z,
    actualSmallRoughRho ((stagePolicy d (N : ℝ) s) false) N enumerationCap w z L q * G q

def terminal (N enumerationCap : ℕ) (w L : ℝ) (G : ℕ → ℝ) : Bool → List ℕ → ℝ :=
  attachedLeafTest N enumerationCap 1 w L G

/-- Exact full-root source for every original stage, including signed
nonmultiplicative arithmetic tests on the COMPLETE modulus. -/
theorem source_eq_actual_root (d : OriginalData) (s : Stage)
    (N enumerationCap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    source d s N enumerationCap w z L G =
      signedTest (stagePolicy d (N : ℝ) s) (fun _ => 1)
        (terminal N enumerationCap w L G) [] true 1 (roughPrimeUniverse N enumerationCap w z) := by
  simpa [source, terminal] using physical_test_eq_signedTest
    (stagePolicy d (N : ℝ) s) (stagePolicy_even d (N : ℝ) s)
    N enumerationCap 1 w z L G

/-- Same test on NEW minus CURRENT parent, at its original retained
frontier. The fifth action is at rank four, before fifth admission. -/
def sourceChange (d : OriginalData) (a : Action) (N enumerationCap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) : ℝ :=
  ((firstExitDepthFrontier (actionRank a) (stagePolicy d (N : ℝ) (parentStage a))
    (fun _ => 1) [] true 1 (roughPrimeUniverse N enumerationCap w z)).map
      (fun state =>
        signedTest (replacement d (N : ℝ) a) (fun _ => 1)
          (terminal N enumerationCap w L G) state.selectedPrefix state.positive state.mass state.remaining -
        signedTest (stagePolicy d (N : ℝ) (parentStage a)) (fun _ => 1)
          (terminal N enumerationCap w L G) state.selectedPrefix state.positive state.mass state.remaining)).sum

theorem source_next_sub_current (d : OriginalData) (a : Action)
    (N enumerationCap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    source d (nextStage a) N enumerationCap w z L G -
      source d (parentStage a) N enumerationCap w z L G =
      sourceChange d a N enumerationCap w z L G := by
  rw [source_eq_actual_root, source_eq_actual_root, next_eq_actual_splice]
  exact signedTest_splice_sub_eq_frontier (actionRank a) _ _ (fun _ => 1)
    (terminal N enumerationCap w L G) [] (roughPrimeUniverse N enumerationCap w z) true 1

theorem actual_source_telescope (d : OriginalData) (N enumerationCap : ℕ)
    (w z L : ℝ) (G : ℕ → ℝ) :
    (∑ q ∈ moduli d N enumerationCap w z, rho d N enumerationCap w z L q * G q) =
      source d .third N enumerationCap w z L G +
        sourceChange d .fourth N enumerationCap w z L G +
        sourceChange d .fifth N enumerationCap w z L G +
        sourceChange d .sixth N enumerationCap w z L G +
        sourceChange d .eighth N enumerationCap w z L G := by
  have h4 := source_next_sub_current d .fourth N enumerationCap w z L G
  have h5 := source_next_sub_current d .fifth N enumerationCap w z L G
  have h6 := source_next_sub_current d .sixth N enumerationCap w z L G
  have h8 := source_next_sub_current d .eighth N enumerationCap w z L G
  simp only [nextStage, parentStage] at h4 h5 h6 h8
  change source d .eighth N enumerationCap w z L G = _
  linarith

/-- The original pointwise majorant now belongs to this SAME fully
specified finite constructor, with its actual eleven-cell lambda6. -/
theorem actual_same_rho_majorant (d : OriginalData) (N enumerationCap : ℕ) (w z L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (enumerationCap : ℝ))
    (n : ℤ) :
    actualSmallRoughIndicator N z n ≤
      physicalDivisorSum (moduli d N enumerationCap w z) (rho d N enumerationCap w z L) n.natAbs :=
  actualSmallRoughRho_majorant ((policy8 d (N : ℝ)) false)
    N enumerationCap w z L hL hwL hwz hzcap n

/-- Density is an exact specialization, preserving each real small-beta
sign correction; no positive gain or analytic bound is presumed. -/
theorem actual_same_rho_density_telescope (d : OriginalData)
    (N enumerationCap : ℕ) (w z L : ℝ) :
    physicalDensitySum (moduli d N enumerationCap w z) (rho d N enumerationCap w z L) =
      source d .third N enumerationCap w z L (fun q => 1 / (Nat.totient q : ℝ)) +
        sourceChange d .fourth N enumerationCap w z L (fun q => 1 / (Nat.totient q : ℝ)) +
        sourceChange d .fifth N enumerationCap w z L (fun q => 1 / (Nat.totient q : ℝ)) +
        sourceChange d .sixth N enumerationCap w z L (fun q => 1 / (Nat.totient q : ℝ)) +
        sourceChange d .eighth N enumerationCap w z L (fun q => 1 / (Nat.totient q : ℝ)) := by
  simpa [physicalDensitySum, div_eq_mul_inv] using
    actual_source_telescope d N enumerationCap w z L (fun q => 1 / (Nat.totient q : ℝ))

/-- AP count and exact full-q coprime mean use one coefficient, one
root carrier, one small beta and one causal common ancestor. -/
theorem actual_same_rho_count_mean (d : OriginalData) (N enumerationCap : ℕ) (w z L : ℝ) :
    (∑ q ∈ moduli d N enumerationCap w z, rho d N enumerationCap w z L q *
      (chenPrimeAPCount N N q - exactCoprimeMean N q)) =
      signedTest (policy8 d (N : ℝ)) (fun _ => 1)
        (fun positive pre =>
          attachedLeafTest N enumerationCap 1 w L (chenPrimeAPCount N N) positive pre -
          attachedLeafTest N enumerationCap 1 w L (exactCoprimeMean N) positive pre)
        [] true 1 (roughPrimeUniverse N enumerationCap w z) := by
  have hf := source_eq_actual_root d .eighth N enumerationCap w z L
    (fun q => chenPrimeAPCount N N q - exactCoprimeMean N q)
  have ht : terminal N enumerationCap w L
      (fun q => chenPrimeAPCount N N q - exactCoprimeMean N q) =
      (fun positive pre =>
        attachedLeafTest N enumerationCap 1 w L (chenPrimeAPCount N N) positive pre -
        attachedLeafTest N enumerationCap 1 w L (exactCoprimeMean N) positive pre) := by
    funext positive pre
    simp [terminal, attachedLeafTest, mul_sub, Finset.sum_sub_distrib]
  rw [ht] at hf
  exact hf

/-- The H3 local coefficient is now a literal q-mask of this independently
constructed common rho, with its actual eleven-family lambda6. -/
theorem actual_common_h3_local_rho (d : OriginalData) (N enumerationCap : ℕ)
    (w z L : ℝ) (q : ℕ) :
    P5OriginalH3LocalPhysicalQFibre.localRho ((policy8 d (N : ℝ)) false)
      N enumerationCap w z L (lambda3 d (N : ℝ)) (lambda6 d (N : ℝ)) q =
    if q ∈ P5OriginalH3LocalPhysicalQFibre.localModuli ((policy8 d (N : ℝ)) false)
      N enumerationCap w z (lambda3 d (N : ℝ)) (lambda6 d (N : ℝ)) then
      rho d N enumerationCap w z L q else 0 :=
  P5OriginalH3LocalPhysicalQFibre.localRho_eq_masked_global _ N enumerationCap w z L _ _ q

/-- The same local fibre contains FULL common-policy root leaves. -/
theorem actual_common_h3_root_leaves (d : OriginalData) (N enumerationCap : ℕ) (w z : ℝ) :
    P5OriginalH3LocalPhysicalQFibre.localLeaves ((policy8 d (N : ℝ)) false)
      N enumerationCap w z (lambda3 d (N : ℝ)) (lambda6 d (N : ℝ)) =
    ((firstExitRootLeaves (policy8 d (N : ℝ)) (fun _ => 1)
      (roughPrimeUniverse N enumerationCap w z)).toFinset).filter
        (P5OriginalH3LocalPhysicalQFibre.H3Leaf N (lambda3 d (N : ℝ)) (lambda6 d (N : ℝ))) := by
  have ho := UpperPolicyFiniteBridge.oddFirstExitPolicy_eq_of_even_retained
    (policy8 d (N : ℝ)) (policy8_even d (N : ℝ))
  unfold P5OriginalH3LocalPhysicalQFibre.localLeaves oddFirstExitRetainedLeaves firstExitRootLeaves
  rw [ho]

end
end ImbalancedChen.P5OriginalCommonRefinedSource
