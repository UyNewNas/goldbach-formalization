import ImbalancedChen.P4AOriginalFull87ActiveLevelHighProduct
import ImbalancedChen.P4AOriginalFull87RankFourStoppedLocalization
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An H_N estimate cannot be inferred from an active-level cutoff. The actual
stopped producer must first be regrouped at its literal FULL physical modulus
q = a * selected.prod, retaining every terminal occurrence, actual beta sign,
original policy and original post-candidate carrier. This file performs that
finite pushforward without making the original stopped rho a new analytic
input, and compares raw/licensed producers at the SAME modulus q.

The resulting stopped-rho fibre is only a COMPONENT of each full physical
rho. It must not be fed into the manuscript's discrepancy statement as if
the full signed coefficient hypothesis automatically transferred to it.
-/

namespace ImbalancedChen.P4AOriginalFull87StoppedModulusFibres
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87StoppedTerminalPopulation
  (StoppedTerminal stoppedTerminals stoppedPhysicalTerm
   actual_stopped_eq_physical_terminal_sum)
open P4AOriginalFull87EarlyStopPhysicalGap (rawStopped licensedStopped)

/-- The finite list of ORIGINAL (terminal, small Rosser factor) occurrences.
Unlike a set of terminals, flatMap preserves repeated source occurrences. -/
def stoppedFactorOccurrences (N cap : ℕ) (w : ℝ)
    (ts : List (StoppedTerminal ℕ)) : List (StoppedTerminal ℕ × ℕ) :=
  ts.flatMap (fun t =>
    (actualSmallRosserSupport N cap w).toList.map (fun a => (t, a)))

/-- The FULL physical modulus, never just the rough selected product. -/
def factorModulus (o : StoppedTerminal ℕ × ℕ) : ℕ :=
  o.2 * o.1.selected.prod

/-- Exact signed coefficient at one original physical factor occurrence. -/
def factorSignedWeight (N cap : ℕ) (w L : ℝ)
    (o : StoppedTerminal ℕ × ℕ) : ℝ :=
  signedTreeCoefficient o.1.positive o.1.mass *
    (if o.1.positive then actualSmallRosserPlus N cap w L o.2
     else actualSmallRosserMinus N cap w L o.2)

/-- A Finset is used ONLY for distinct full modulus labels. The fibre sum
below still ranges over the whole List, so equal q values do not erase
terminal multiplicity or cancel the opposite signs prematurely. -/
def stoppedModulusSupport (N cap : ℕ) (w : ℝ)
    (ts : List (StoppedTerminal ℕ)) : Finset ℕ :=
  ((stoppedFactorOccurrences N cap w ts).map factorModulus).toFinset

/-- Signed coefficient of a fixed full modulus, with original multiplicity. -/
def stoppedModulusFibre (N cap : ℕ) (w L : ℝ)
    (ts : List (StoppedTerminal ℕ)) (q : ℕ) : ℝ :=
  ((stoppedFactorOccurrences N cap w ts).map (fun o =>
    if factorModulus o = q then factorSignedWeight N cap w L o else 0)).sum

private theorem physical_terminal_eq_factor_occurrence_sum
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (t : StoppedTerminal ℕ) :
    stoppedPhysicalTerm N cap w L X F t =
      (((actualSmallRosserSupport N cap w).toList.map (fun a =>
        factorSignedWeight N cap w L (t, a) *
          highQTest X F (factorModulus (t, a)))).sum) := by
  unfold stoppedPhysicalTerm factorSignedWeight factorModulus
  simp only [attachedLeafTest, one_mul]
  rw [Finset.mul_sum]
  rw [Finset.sum_toList]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- Fubini along the exact original stopped List; no Finset coercion of
terminal occurrences is used at any point. -/
private theorem physical_terminal_list_eq_factor_occurrence_sum
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (ts : List (StoppedTerminal ℕ)) :
    (ts.map (stoppedPhysicalTerm N cap w L X F)).sum =
      ((stoppedFactorOccurrences N cap w ts).map (fun o =>
        factorSignedWeight N cap w L o *
          highQTest X F (factorModulus o))).sum := by
  induction ts with
  | nil =>
      simp [stoppedFactorOccurrences]
  | cons t ts ih =>
      change stoppedPhysicalTerm N cap w L X F t +
        (ts.map (stoppedPhysicalTerm N cap w L X F)).sum =
        (((actualSmallRosserSupport N cap w).toList.map
            (fun a => (t, a)) ++ stoppedFactorOccurrences N cap w ts).map
          (fun o => factorSignedWeight N cap w L o *
            highQTest X F (factorModulus o))).sum
      simp only [List.map_append, List.sum_append, List.map_map]
      rw [physical_terminal_eq_factor_occurrence_sum, ih]

private theorem factor_modulus_mem_support
    (N cap : ℕ) (w : ℝ) (ts : List (StoppedTerminal ℕ))
    (o : StoppedTerminal ℕ × ℕ)
    (ho : o ∈ stoppedFactorOccurrences N cap w ts) :
    factorModulus o ∈ stoppedModulusSupport N cap w ts := by
  unfold stoppedModulusSupport
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨o, ho, rfl⟩)

/-- A finite pushforward identity with explicit support. This is a REAL
signed identity, not a triangle-inequality invoice. -/
private theorem list_weighted_pushforward {α : Type*}
    (xs : List α) (Q : Finset ℕ) (modulus : α → ℕ)
    (weight : α → ℝ) (G : ℕ → ℝ)
    (hQ : ∀ o ∈ xs, modulus o ∈ Q) :
    (xs.map (fun o => weight o * G (modulus o))).sum =
      ∑ q ∈ Q,
        ((xs.map (fun o => if modulus o = q then weight o else 0)).sum) *
          G q := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : modulus x ∈ Q := hQ x (by simp)
      have htail : ∀ y ∈ xs, modulus y ∈ Q := by
        intro y hy
        exact hQ y (by simp [hy])
      have hsingle :
          (∑ q ∈ Q, (if modulus x = q then weight x else 0) * G q) =
            weight x * G (modulus x) := by
        calc
          _ = ∑ q ∈ Q,
                (if modulus x = q then weight x * G q else 0) := by
                  apply Finset.sum_congr rfl
                  intro q hq
                  by_cases h : modulus x = q <;> simp [h]
          _ = (if modulus x = modulus x then
                weight x * G (modulus x) else 0) := by
                  apply Finset.sum_eq_single (modulus x)
                  · intro q hq hne
                    simp [Ne.symm hne]
                  · intro hnot
                    exact (hnot hx).elim
          _ = weight x * G (modulus x) := by simp
      simp only [List.map_cons, List.sum_cons]
      rw [ih htail]
      calc
        _ = (∑ q ∈ Q,
              (if modulus x = q then weight x else 0) * G q) +
            (∑ q ∈ Q,
              ((xs.map (fun y =>
                if modulus y = q then weight y else 0)).sum) * G q) := by
              rw [hsingle]
        _ = ∑ q ∈ Q,
              (((x :: xs).map (fun y =>
                if modulus y = q then weight y else 0)).sum) * G q := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro q hq
              simp [add_mul]

/-- Exact signed full-q grouping, for ANY original list of stopped
terminals. Q may contain extra moduli, whose fibre coefficients vanish.
No numerical error, surrogate parent or source-side absolute value occurs. -/
theorem stopped_terminal_sum_eq_full_modulus_fibres
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (ts : List (StoppedTerminal ℕ)) (Q : Finset ℕ)
    (hQ : stoppedModulusSupport N cap w ts ⊆ Q) :
    (ts.map (stoppedPhysicalTerm N cap w L X F)).sum =
      ∑ q ∈ Q, stoppedModulusFibre N cap w L ts q *
        highQTest X F q := by
  rw [physical_terminal_list_eq_factor_occurrence_sum]
  unfold stoppedModulusFibre
  exact list_weighted_pushforward
    (stoppedFactorOccurrences N cap w ts) Q factorModulus
    (factorSignedWeight N cap w L) (highQTest X F)
    (by
      intro o ho
      exact hQ (factor_modulus_mem_support N cap w ts o ho))

/-- Original root stopped population from the unmodified producer policy. -/
def rootStoppedPopulation (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : List (StoppedTerminal ℕ) :=
  stoppedTerminals 8 R (fun _ : ℕ => (1 : ℝ))
    [] true 1 (roughPrimeUniverse N cap w z)

/-- The actual signed stopped coefficient at q, independent of F and X. -/
def rootStoppedRho (R : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (q : ℕ) : ℝ :=
  stoppedModulusFibre N cap w L (rootStoppedPopulation R N cap w z) q

def pairRootStoppedSupport (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z : ℝ) : Finset ℕ :=
  stoppedModulusSupport N cap w (rootStoppedPopulation R N cap w z) ∪
    stoppedModulusSupport N cap w (rootStoppedPopulation S N cap w z)

/-- Two different admitted policies are compared on ONE and the SAME
full-q support. This equality does not subtract unrelated sieve bounds. -/
theorem stopped_root_policy_difference_by_full_modulus
    (R S : Bool → List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        [] true 1 (roughPrimeUniverse N cap w z) -
      stoppedTest 8 S (fun _ : ℕ => (1 : ℝ))
        (attachedLeafTest N cap 1 w L (highQTest X F))
        [] true 1 (roughPrimeUniverse N cap w z) =
      ∑ q ∈ pairRootStoppedSupport R S N cap w z,
        (rootStoppedRho R N cap w z L q -
          rootStoppedRho S N cap w z L q) * highQTest X F q := by
  let Q := pairRootStoppedSupport R S N cap w z
  have hr : stoppedTest 8 R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      [] true 1 (roughPrimeUniverse N cap w z) =
        ∑ q ∈ Q, rootStoppedRho R N cap w z L q * highQTest X F q := by
    rw [actual_stopped_eq_physical_terminal_sum]
    exact stopped_terminal_sum_eq_full_modulus_fibres
      N cap w L X F (rootStoppedPopulation R N cap w z) Q
      (Finset.subset_union_left)
  have hs : stoppedTest 8 S (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      [] true 1 (roughPrimeUniverse N cap w z) =
        ∑ q ∈ Q, rootStoppedRho S N cap w z L q * highQTest X F q := by
    rw [actual_stopped_eq_physical_terminal_sum]
    exact stopped_terminal_sum_eq_full_modulus_fibres
      N cap w L X F (rootStoppedPopulation S N cap w z) Q
      (Finset.subset_union_right)
  calc
    _ = (∑ q ∈ Q, rootStoppedRho R N cap w z L q * highQTest X F q) -
        (∑ q ∈ Q, rootStoppedRho S N cap w z L q * highQTest X F q) := by
          rw [hr, hs]
    _ = ∑ q ∈ Q,
          (rootStoppedRho R N cap w z L q -
            rootStoppedRho S N cap w z L q) * highQTest X F q := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro q hq
          ring

/-- The two ACTUAL original/fully licensed sixth policies, not an
artificial parent. Each producer keeps its own fourth-to-seventh history,
and all collisions in the full modulus are summed with original signs. -/
theorem actual_raw_licensed_stopped_full_modulus_identity
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    rawStopped e q om N cap w z L X F -
      licensedStopped delta n e q om N cap w z L X F =
    ∑ d ∈ pairRootStoppedSupport
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
        N cap w z,
      (rootStoppedRho
        (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
          N cap w z L d -
       rootStoppedRho
        (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
          N cap w z L d) * highQTest X F d := by
  exact stopped_root_policy_difference_by_full_modulus
    (P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ))
    (P4AOriginalFull87LicensedSixthPolicy.policy delta n e q om (N : ℝ))
    N cap w z L X F

end
end ImbalancedChen.P4AOriginalFull87StoppedModulusFibres
