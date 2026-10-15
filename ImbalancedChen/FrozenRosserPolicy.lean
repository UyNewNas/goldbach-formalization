import ImbalancedChen.OrdinaryRosserContinuation
import ImbalancedChen.FinitePrimeGeometryCore

/-!
# Ordinary Rosser policies with an ancestor-frozen level

The tree stores selected primes in reverse processing order. Thus its
rank-`k` ancestor is the last `k` entries of the history. Once that rank
has been reached, prepending further selected labels leaves the ancestor
and its chosen level unchanged. The continuation identity below is proved
from the actual tree recursion, not supplied as a hypothesis.

The level-selection function is arbitrary finite policy data. No claim is
made that an arbitrary such function implements the manuscript's certified
cap selection. Its inherited admissibility obligations remain explicit.
-/

namespace ImbalancedChen

noncomputable section

@[simp] theorem rosserAncestor_length {α : Type*} (k : ℕ) (history : List α) :
    (rosserAncestor k history).length = min k history.length := by
  simp only [rosserAncestor, List.length_drop]
  omega

theorem rosserAncestor_self_of_length_le {α : Type*} (k : ℕ) (history : List α)
    (hlen : history.length ≤ k) : rosserAncestor k history = history := by
  simp only [rosserAncestor, Nat.sub_eq_zero_of_le hlen, List.drop_zero]

theorem rosserAncestor_self_of_length {α : Type*} (k : ℕ) (history : List α)
    (hlen : history.length = k) : rosserAncestor k history = history :=
  rosserAncestor_self_of_length_le k history hlen.le

@[simp] theorem rosserAncestor_zero {α : Type*} (history : List α) :
    rosserAncestor 0 history = [] := by
  simp [rosserAncestor]

/-- Reaching rank `k` freezes the actual ancestor under the next selection. -/
theorem rosserAncestor_cons {α : Type*} (k : ℕ) (q : α) (history : List α)
    (hk : k ≤ history.length) :
    rosserAncestor k (q :: history) = rosserAncestor k history := by
  unfold rosserAncestor
  have hidx : (q :: history).length - k = (history.length - k) + 1 := by
    simp only [List.length_cons]
    omega
  rw [hidx, List.drop_succ_cons]

/-- Arbitrarily many later selections preserve the same ancestor. -/
theorem rosserAncestor_append {α : Type*} (k : ℕ) (later history : List α)
    (hk : k ≤ history.length) :
    rosserAncestor k (later ++ history) = rosserAncestor k history := by
  induction later with
  | nil => rfl
  | cons q later ih =>
      rw [List.cons_append, rosserAncestor_cons]
      · exact ih
      · simp only [List.length_append]
        omega

/-- Taking a smaller ancestor of an ancestor recovers the original smaller
ancestor, even when the actual history has not reached either rank. -/
theorem rosserAncestor_nested {α : Type*} (k m : ℕ) (hkm : k ≤ m)
    (history : List α) :
    rosserAncestor k (rosserAncestor m history) = rosserAncestor k history := by
  simp only [rosserAncestor, List.length_drop, List.drop_drop]
  congr 1
  omega

theorem rosserAncestor_four_five {α : Type*} (history : List α) :
    rosserAncestor 4 (rosserAncestor 5 history) = rosserAncestor 4 history :=
  rosserAncestor_nested 4 5 (by omega) history

theorem rosserAncestor_level_append {α : Type*} (k : ℕ)
    (Q : List α → ℝ) (later history : List α) (hk : k ≤ history.length) :
    Q (rosserAncestor k (later ++ history)) = Q (rosserAncestor k history) := by
  rw [rosserAncestor_append k later history hk]

def frozenOrdinaryRosserPolicy (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) :
    Bool → List ℕ → Bool :=
  ancestorFrozenPolicy k Q (ordinaryRosserRetainedPolicy lower)

/-- Exact recursive freezing. The future policy reads the same ancestor
after every actual selection; skipped labels do not alter the history. -/
theorem firstExitRetainedPolynomial_ancestorFrozenPolicy
    {α : Type*} (k : ℕ) (Q : List α → ℝ)
    (policy : ℝ → Bool → List α → Bool) (h : α → ℝ)
    (carrier pre : List α) (positive : Bool) (mass : ℝ) (hk : k ≤ pre.length) :
    firstExitRetainedPolynomial (ancestorFrozenPolicy k Q policy)
        h pre positive mass carrier =
      firstExitRetainedPolynomial (policy (Q (rosserAncestor k pre)))
        h pre positive mass carrier := by
  induction carrier generalizing pre positive mass with
  | nil => rfl
  | cons q qs ih =>
      have hk' : k ≤ (q :: pre).length := by simp only [List.length_cons]; omega
      have hanc := rosserAncestor_cons k q pre hk
      simp only [firstExitRetainedPolynomial, ancestorFrozenPolicy, hanc]
      rw [ih pre positive mass hk]
      by_cases ht : policy (Q (rosserAncestor k pre)) (!positive) (q :: pre) = true
      · simp only [if_pos ht]
        rw [ih (q :: pre) (!positive) (mass * h q) hk', hanc]
      · simp only [if_neg ht]

theorem firstExitRetainedPolynomial_frozenOrdinaryRosser_eq
    (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) (hlen : pre.length = k) :
    firstExitRetainedPolynomial (frozenOrdinaryRosserPolicy lower k Q)
        h pre positive mass carrier =
      firstExitRetainedPolynomial (ordinaryRosserRetainedPolicy lower (Q pre))
        h pre positive mass carrier := by
  rw [frozenOrdinaryRosserPolicy, firstExitRetainedPolynomial_ancestorFrozenPolicy
    k Q _ h carrier pre positive mass hlen.ge, rosserAncestor_self_of_length k pre hlen]

theorem firstExitRetainedPolynomial_frozenParityRosser_eq
    (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) (h : ℕ → ℝ)
    (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) (hlen : pre.length = k) :
    firstExitRetainedPolynomial (frozenParityRosserPolicy lower k Q)
        h pre positive mass carrier =
      firstExitRetainedPolynomial (ordinaryParityRosserPolicy lower (Q pre))
        h pre positive mass carrier := by
  rw [frozenParityRosserPolicy, firstExitRetainedPolynomial_ancestorFrozenPolicy
    k Q _ h carrier pre positive mass hlen.ge, rosserAncestor_self_of_length k pre hlen]

/-- A rank-`m` frozen selection inherited from its rank-`k` ancestor is
literally the rank-`k` frozen policy, for `k ≤ m`. -/
theorem ancestorFrozenPolicy_nested {α : Type*} (k m : ℕ) (hkm : k ≤ m)
    (Q : List α → ℝ) (policy : ℝ → Bool → List α → Bool) :
    ancestorFrozenPolicy m (fun pre => Q (rosserAncestor k pre)) policy =
      ancestorFrozenPolicy k Q policy := by
  funext positive history
  simp only [ancestorFrozenPolicy, rosserAncestor_nested k m hkm]

theorem frozenOrdinaryRosserPolicy_nested (lower : Bool) (k m : ℕ) (hkm : k ≤ m)
    (Q : List ℕ → ℝ) :
    frozenOrdinaryRosserPolicy lower m (fun pre => Q (rosserAncestor k pre)) =
      frozenOrdinaryRosserPolicy lower k Q :=
  ancestorFrozenPolicy_nested k m hkm Q _

theorem frozenParityRosserPolicy_nested (lower : Bool) (k m : ℕ) (hkm : k ≤ m)
    (Q : List ℕ → ℝ) :
    frozenParityRosserPolicy lower m (fun pre => Q (rosserAncestor k pre)) =
      frozenParityRosserPolicy lower k Q :=
  ancestorFrozenPolicy_nested k m hkm Q _

@[simp] theorem frozenParityRosserPolicy_upper_even (k : ℕ) (Q : List ℕ → ℝ)
    (pre : List ℕ) : frozenParityRosserPolicy false k Q true pre = true := by
  simp [frozenParityRosserPolicy, ancestorFrozenPolicy]

@[simp] theorem frozenParityRosserPolicy_lower_odd (k : ℕ) (Q : List ℕ → ℝ)
    (pre : List ℕ) : frozenParityRosserPolicy true k Q false pre = true := by
  simp [frozenParityRosserPolicy, ancestorFrozenPolicy]

/-- Beyond the freezing rank, the literal residual level is the level
selected by the unchanged ancestor divided by the entire selected product.
Admissibility of that entire history at the frozen level remains explicit. -/
theorem firstExitRetainedPolynomial_frozenOrdinaryRosser_actualDensity_of_le
    (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) (N cap : ℕ) (y : ℝ) (pre : List ℕ)
    (hk : k ≤ pre.length)
    (hpre : ordinaryRosserPrefixAdmissible lower (Q (rosserAncestor k pre)) pre)
    (hnd : pre.Nodup) (hP : (0 : ℝ) < pre.prod)
    (hcut : ∀ p ∈ pre, y ≤ (p : ℝ)) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (frozenOrdinaryRosserPolicy lower k Q)
        (fun p => 1 / ((p : ℝ) - 1)) pre positive mass
        (roughPrimeUniverse N cap 0 y) =
      signedTreeCoefficient positive mass *
        (if ordinaryRosserResidualLower lower pre.length then
          actualSmallRosserMinusDensity N cap y
            (Q (rosserAncestor k pre) / (pre.prod : ℝ))
        else actualSmallRosserPlusDensity N cap y
            (Q (rosserAncestor k pre) / (pre.prod : ℝ))) := by
  rw [frozenOrdinaryRosserPolicy, firstExitRetainedPolynomial_ancestorFrozenPolicy
    k Q _ _ _ pre positive mass hk]
  exact firstExitRetainedPolynomial_ordinaryRosser_continuation_actualDensity
    lower N cap y (Q (rosserAncestor k pre)) pre hpre hnd hP hcut positive mass

/-- The rank-`k` frontier reads its own level value `Q pre`. -/
theorem firstExitRetainedPolynomial_frozenOrdinaryRosser_actualDensity
    (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) (N cap : ℕ) (y : ℝ) (pre : List ℕ)
    (hlen : pre.length = k)
    (hpre : ordinaryRosserPrefixAdmissible lower (Q pre) pre)
    (hnd : pre.Nodup) (hP : (0 : ℝ) < pre.prod)
    (hcut : ∀ p ∈ pre, y ≤ (p : ℝ)) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial (frozenOrdinaryRosserPolicy lower k Q)
        (fun p => 1 / ((p : ℝ) - 1)) pre positive mass
        (roughPrimeUniverse N cap 0 y) =
      signedTreeCoefficient positive mass *
        (if ordinaryRosserResidualLower lower k then
          actualSmallRosserMinusDensity N cap y (Q pre / (pre.prod : ℝ))
        else actualSmallRosserPlusDensity N cap y (Q pre / (pre.prod : ℝ))) := by
  rw [firstExitRetainedPolynomial_frozenOrdinaryRosser_eq lower k Q _ pre _
    positive mass hlen]
  simpa only [hlen] using
    firstExitRetainedPolynomial_ordinaryRosser_continuation_actualDensity
      lower N cap y (Q pre) pre hpre hnd hP hcut positive mass

/-- The parity-safe frozen policy has the same literal residual density
on sorted, nonempty admissible histories with their actual incoming sign. -/
theorem firstExitRetainedPolynomial_frozenParityRosser_actualDensity_of_le
    (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) (N cap : ℕ) (y : ℝ) (pre : List ℕ)
    (hk : k ≤ pre.length)
    (hpre : ordinaryRosserPrefixAdmissible lower (Q (rosserAncestor k pre)) pre)
    (hsort : pre.Pairwise (· < ·)) (hP : (0 : ℝ) < pre.prod) (hne : pre ≠ [])
    (hcut : ∀ p ∈ pre, y ≤ (p : ℝ)) (positive : Bool) (mass : ℝ)
    (hsign : positive = evenListLength pre) :
    firstExitRetainedPolynomial (frozenParityRosserPolicy lower k Q)
        (fun p => 1 / ((p : ℝ) - 1)) pre positive mass
        (roughPrimeUniverse N cap 0 y) =
      signedTreeCoefficient positive mass *
        (if ordinaryRosserResidualLower lower pre.length then
          actualSmallRosserMinusDensity N cap y
            (Q (rosserAncestor k pre) / (pre.prod : ℝ))
        else actualSmallRosserPlusDensity N cap y
            (Q (rosserAncestor k pre) / (pre.prod : ℝ))) := by
  rw [frozenParityRosserPolicy, firstExitRetainedPolynomial_ancestorFrozenPolicy
    k Q _ _ _ pre positive mass hk]
  exact firstExitRetainedPolynomial_ordinaryParityRosser_continuation_actualDensity
    lower N cap y (Q (rosserAncestor k pre)) pre hpre hsort hP hne hcut
    positive mass hsign

/-- At a positive frontier rank, admissibility pays the first-prime total
level condition; no additional level hypothesis is supplied by the caller. -/
theorem firstExitRetainedPolynomial_frozenParityRosser_actualDensity
    (lower : Bool) (k : ℕ) (Q : List ℕ → ℝ) (N cap : ℕ) (y : ℝ) (pre : List ℕ)
    (hlen : pre.length = k) (hk : 0 < k)
    (hpre : ordinaryRosserPrefixAdmissible lower (Q pre) pre)
    (hsort : pre.Pairwise (· < ·)) (hP : (0 : ℝ) < pre.prod)
    (hcut : ∀ p ∈ pre, y ≤ (p : ℝ)) (positive : Bool) (mass : ℝ)
    (hsign : positive = evenListLength pre) :
    firstExitRetainedPolynomial (frozenParityRosserPolicy lower k Q)
        (fun p => 1 / ((p : ℝ) - 1)) pre positive mass
        (roughPrimeUniverse N cap 0 y) =
      signedTreeCoefficient positive mass *
        (if ordinaryRosserResidualLower lower k then
          actualSmallRosserMinusDensity N cap y (Q pre / (pre.prod : ℝ))
        else actualSmallRosserPlusDensity N cap y (Q pre / (pre.prod : ℝ))) := by
  have hne : pre ≠ [] := by
    intro he
    simp only [he, List.length_nil] at hlen
    omega
  rw [firstExitRetainedPolynomial_frozenParityRosser_eq lower k Q _ pre _
    positive mass hlen]
  simpa only [hlen] using
    firstExitRetainedPolynomial_ordinaryParityRosser_continuation_actualDensity
      lower N cap y (Q pre) pre hpre hsort hP hne hcut positive mass hsign

end

end ImbalancedChen
