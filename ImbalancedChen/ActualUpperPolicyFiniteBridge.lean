import ImbalancedChen.FiniteUpperCarrierCore
import ImbalancedChen.ActualPrimePresieveSplit
import ImbalancedChen.FirstExitGenericModuli
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Finite identification of an even-retaining physical policy

These seven structural identities retain the literal policy, modulus
carrier, signed coefficient and reciprocal-totient density. The generic
proofs are reproduced from ActualUpperPolicyDensity in this separate
namespace so this finite consumer does not import historical integral
suppliers. No density limit, distribution or coefficient bound is assumed.
-/

namespace ImbalancedChen.UpperPolicyFiniteBridge

noncomputable section

theorem oddFirstExitPolicy_eq_of_even_retained {α : Type*}
    (retained : Bool → List α → Bool)
    (heven : ∀ pre, retained true pre = true) :
    oddFirstExitPolicy (retained false) = retained := by
  funext positive pre
  cases positive <;> simp [oddFirstExitPolicy, heven]

theorem fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    fixedRoughSupport (retained false) N cap w z =
      firstExitRetainedModuli retained (roughPrimeUniverse N cap w z) := by
  unfold fixedRoughSupport oddFirstExitRetainedModuli firstExitRetainedModuli
    oddFirstExitRetainedLeaves firstExitRootLeaves
  rw [oddFirstExitPolicy_eq_of_even_retained retained heven]

theorem fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) (d : ℕ) :
    fixedRoughCoefficient (retained false) N cap w z d =
      (firstExitRetainedCoefficient retained (roughPrimeUniverse N cap w z) d : ℝ) := by
  change ((if d ∈ fixedRoughSupport (retained false) N cap w z then
    ArithmeticFunction.moebius d else 0 : ℤ) : ℝ) = _
  rw [fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    retained heven N cap w z]
  rfl

theorem actualSmallRoughRho_eq_firstExitAttachment
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z L : ℝ) :
    actualSmallRoughRho (retained false) N cap w z L =
      smallRoughRho (actualSmallRosserSupport N cap w)
        (firstExitRetainedModuli retained (roughPrimeUniverse N cap w z))
        (fun d => (firstExitRetainedCoefficient retained
          (roughPrimeUniverse N cap w z) d : ℝ))
        (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) := by
  unfold actualSmallRoughRho
  rw [fixedRoughSupport_eq_firstExitRetainedModuli_of_even_retained
    retained heven N cap w z]
  rw [funext (fixedRoughCoefficient_eq_firstExitRetainedCoefficient_of_even_retained
    retained heven N cap w z)]

theorem firstExitRetainedPolynomial_eq_fixedRoughDensity_of_even_retained
    (retained : Bool → List ℕ → Bool)
    (heven : ∀ pre, retained true pre = true)
    (N cap : ℕ) (w z : ℝ) :
    firstExitRetainedPolynomial retained
        (fun p : ℕ => 1 / ((p : ℝ) - 1)) [] true 1
        (roughPrimeUniverse N cap w z) =
      reciprocalTotientDensity (fixedRoughSupport (retained false) N cap w z)
        (fixedRoughCoefficient (retained false) N cap w z) := by
  simpa only [oddFirstExitRetainedPolynomial,
    oddFirstExitPolicy_eq_of_even_retained retained heven] using
      oddFirstExitRetainedPolynomial_eq_fixedRoughDensity
        (retained false) N cap w z

theorem firstExitDepthSplicePolicy_even_retained {α : Type*} (k : ℕ)
    (parent replacement : Bool → List α → Bool)
    (hparent : ∀ pre, parent true pre = true)
    (hreplacement : ∀ pre, replacement true pre = true) (pre : List α) :
    firstExitDepthSplicePolicy k parent replacement true pre = true := by
  simp [firstExitDepthSplicePolicy, hparent, hreplacement]

theorem thirdCappedUpperPolicy_even_retained
    (base : Bool → List ℕ → Bool) (Q3 : List ℕ → ℝ)
    (hbase : ∀ pre, base true pre = true) (pre : List ℕ) :
    thirdCappedUpperPolicy base Q3 true pre = true := by
  unfold thirdCappedUpperPolicy
  exact firstExitDepthSplicePolicy_even_retained 2 _ _ hbase
    (fun history => by
      simp [frozenParityRosserPolicy, ancestorFrozenPolicy,
        ordinaryParityRosserPolicy, oddFirstExitPolicy]) pre

end

end ImbalancedChen.UpperPolicyFiniteBridge
