import ImbalancedChen.P4AOriginalFull87PhysicalFailedWeights
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.FirstExitDepthSplice
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO FORMAL CREDIT.

P1.4: transport the ACTUAL root-to-rank-eight sixth-parent frontier
from unit enumeration weights to the real finite halfProductDensity
weights. The parent policy, exact prime source, selected histories,
incoming signs, unprocessed suffixes, owner/trim filtering, ordered
occurrences, and multiplicity remain identical. Only incoming mass
changes, by the actual selected-prefix product.

The result is NOT a signed-saving or target-deletion bound. It is
important not to multiply the eighth-prefix product again when
passing to the physical post-eight rejected attempts. No external
distribution theorem is invoked here.
-/

namespace ImbalancedChen.P4AOriginalFull87WeightedRootTransport

noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87LicensedSixthPolicy
  (policy sixthPolicy frontier_eq_new_sixth)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
    correction_eq_failed_attempt_sum)

/-- Reweight one frontier occurrence, changing only its incoming mass. -/
def massReweight {α : Type*} (h : α → ℝ) (baseMass : ℝ)
    (s : FirstExitDepthState α) : FirstExitDepthState α :=
  { s with mass := baseMass * (s.selectedPrefix.map h).prod }

/-- An induction over the LITERAL firstExitDepthFrontier recursion.
The invariant records the exact selected prefix rather than counting
only its length. A skipped prime has no mass effect; a successful select
adds precisely one factor h(p). The policy is identical on both sides. -/
theorem firstExitDepthFrontier_weight_transport {α : Type*}
    (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ) :
    ∀ (pre remaining : List α) (positive : Bool) (baseMass : ℝ),
      firstExitDepthFrontier k parent h pre positive
          (baseMass * (pre.map h).prod) remaining =
        (firstExitDepthFrontier k parent (fun _ : α => (1 : ℝ))
          pre positive baseMass remaining).map (massReweight h baseMass) := by
  intro pre remaining positive baseMass
  induction remaining generalizing pre positive baseMass with
  | nil =>
      by_cases hk : k ≤ pre.length <;>
        simp [firstExitDepthFrontier, hk, massReweight]
  | cons p ps ih =>
      by_cases hk : k ≤ pre.length
      · simp [firstExitDepthFrontier, hk, massReweight]
      · by_cases ht : parent (!positive) (p :: pre) = true
        · have hmul :
              baseMass * (pre.map h).prod * h p =
                baseMass * ((p :: pre).map h).prod := by
            simp only [List.map_cons, List.prod_cons]
            ring
          simp only [firstExitDepthFrontier, if_neg hk, if_pos ht,
            List.map_append, mul_one]
          rw [hmul, ih pre positive baseMass,
            ih (p :: pre) (!positive) baseMass]
        · simp only [firstExitDepthFrontier, if_neg hk, if_neg ht,
            List.append_nil, List.map_append, List.map_nil, mul_one]
          exact ih pre positive baseMass

/-- Root formulation. The ordered physical frontier equals the unit
frontier with its ACTUAL selected prime-product mass attached once. -/
theorem root_frontier_weight_transport {α : Type*}
    (k : ℕ) (parent : Bool → List α → Bool) (h : α → ℝ)
    (carrier : List α) :
    firstExitDepthFrontier k parent h [] true 1 carrier =
      (firstExitDepthFrontier k parent (fun _ : α => (1 : ℝ))
        [] true 1 carrier).map (massReweight h 1) := by
  simpa only [List.map_nil, List.prod_nil, mul_one] using
    firstExitDepthFrontier_weight_transport k parent h [] carrier true 1

/-- The REAL owned original87 rank-eight source has the same ordered
occurrences as its unit-weight sixth-parent list. In particular the
original owner and trim checks commute with reweighting: they read
the selected history, not the incoming mass. This is an equality of
lists, not a Finset identity or merely a membership correspondence. -/
theorem owned87_weighted_states_transport
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) (c : Cell) :
    states delta n e q om N cap w z weight c =
      (states delta n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c).map (massReweight weight 1) := by
  have hfilter (xs : List (FirstExitDepthState ℕ)) :
      ((xs.map (massReweight weight 1)).filter fun s =>
        decide (ownerAtPrefix (N : ℝ) s.selectedPrefix = some c ∧
          point8 (N : ℝ) s.selectedPrefix ∈ trim c delta)) =
      ((xs.filter fun s =>
        decide (ownerAtPrefix (N : ℝ) s.selectedPrefix = some c ∧
          point8 (N : ℝ) s.selectedPrefix ∈ trim c delta)).map
        (massReweight weight 1)) := by
    induction xs with
    | nil => rfl
    | cons s xs ih =>
        by_cases ho :
            ownerAtPrefix (N : ℝ) s.selectedPrefix = some c ∧
            point8 (N : ℝ) s.selectedPrefix ∈ trim c delta
        · simp [massReweight, ho, ih]
        · simp [massReweight, ho, ih]
  unfold states
  rw [frontier_eq_new_sixth delta n e q om (N : ℝ) weight []
      (roughPrimeUniverse N cap w z) true 1,
    frontier_eq_new_sixth delta n e q om (N : ℝ)
      (fun _ : ℕ => (1 : ℝ)) [] (roughPrimeUniverse N cap w z) true 1,
    root_frontier_weight_transport 8
      (sixthPolicy n e q om (N : ℝ)) weight
      (roughPrimeUniverse N cap w z)]
  exact hfilter _

/-- Each genuine unit-weight owner occurrence produces its physical
counterpart with the same history, sign, remaining carrier and owner.
It does not claim equality of the two incoming masses. -/
theorem owned87_weighted_occurrence_mem
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c) :
    massReweight weight 1 s ∈
      states delta n e q om N cap w z weight c := by
  rw [owned87_weighted_states_transport]
  exact List.mem_map.mpr ⟨s, hs, rfl⟩

/-- Whole owned eighth-state *physical* ordinary correction, expanded
into the genuine failed-select occurrence sum. Each entry's incoming
mass is the eighth prefix product from the ROOT transport, and the
post-eight successful, rejected and Euler-suffix factors are inserted
only by the SAME original event recursion. The frozen level reads
the unchanged prefix; no second deletion factor is charged. -/
theorem owned87_physical_correction_eq_actual_failed_sum
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) (useParent : Bool) :
    ((states delta n e q om N cap w z halfProductDensity c).map
      (fun s => firstExitCorrection
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        halfProductDensity s.selectedPrefix s.positive s.mass s.remaining)).sum =
    ((states delta n e q om N cap w z
        (fun _ : ℕ => (1 : ℝ)) c).map
      (fun s => ((firstExitRejectedAttempts
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        halfProductDensity s.selectedPrefix s.positive
        (s.selectedPrefix.map halfProductDensity).prod s.remaining).map
          (FirstExitRejectedAttempt.value halfProductDensity)).sum)).sum := by
  rw [owned87_weighted_states_transport]
  simp only [List.map_map, Function.comp_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  simpa [massReweight, actualFrozenPost8Level] using
    (correction_eq_failed_attempt_sum
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      halfProductDensity s.selectedPrefix s.remaining s.positive
      (s.selectedPrefix.map halfProductDensity).prod)

end
end ImbalancedChen.P4AOriginalFull87WeightedRootTransport
