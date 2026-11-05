import ImbalancedChen.P1SignedDescendantAccounting
import ImbalancedChen.P4AOriginalLicensedSixthSignedLedger
import ImbalancedChen.P4AOriginalFull87EighthKernelIntegration

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

Exact full87 partition of the NEW eighth arithmetic source. Each local
summand compares two ordinary continuations on the SAME selected prefix,
sign, mass, remaining carrier and full-modulus beta terminal. The old level
is the NEW filtered policy's own-sixth level. It is not the raw maximum,
the comparison R_c, or an unrelated sieve bound.

This supplies finite occurrence accounting, not the asymptotic theorem
identifying ordinary continuations with their residual-kernel integrals.
-/
namespace ImbalancedChen.P4AOriginalFull87OwnedEighthSource
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource P1SignedDescendantAccounting
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87SourceDispatch (ownerAtPrefix point8)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_append)
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalLicensedSixthSignedLedger (physical eighthChange eighth_physical_change)

/-- Exactly the old owner plus the old trim, not a new priority rule. -/
def retainedOwner (delta N : ℝ) (history : List ℕ) : Option Cell :=
  match ownerAtPrefix N history with
  | none => none
  | some c => if point8 N history ∈ trim c delta then some c else none

theorem retainedOwner_some_iff (delta N : ℝ) (history : List ℕ) (c : Cell) :
    retainedOwner delta N history = some c ↔
      ownerAtPrefix N history = some c ∧ point8 N history ∈ trim c delta := by
  cases ho : ownerAtPrefix N history with
  | none => simp [retainedOwner, ho]
  | some d =>
      by_cases ht : point8 N history ∈ trim d delta
      · simp only [retainedOwner, ho, if_pos ht, Option.some.injEq]
        constructor
        · intro he; subst d; exact ⟨rfl, ht⟩
        · rintro ⟨he, _⟩; exact he
      · constructor
        · intro he
          simp only [retainedOwner, ho, if_neg ht] at he
          cases he
        · rintro ⟨he, hm⟩
          have hdc : d = c := by simpa only [ho, Option.some.injEq] using he
          subst d
          exact (ht hm).elim

theorem selectedCap_eq_map_owner (delta : ℝ) (n : ℕ) (N : ℝ) (history : List ℕ) :
    selectedCap delta n N history =
      (retainedOwner delta N history).map (fun c => finiteCap n c (point8 N history)) := by
  cases ho : ownerAtPrefix N history with
  | none => simp [selectedCap, retainedOwner, ho]
  | some c =>
      by_cases ht : point8 N history ∈ trim c delta <;>
        simp [selectedCap, retainedOwner, ho, ht]

/-- Only queries after rank eight are needed, so the whole old continuation
has its OWN frozen sixth level. No prefix tests are restarted or omitted. -/
theorem sixth_test_eq_ordinary (n : ℕ) (e : ℚ) (q : ℕ) (om N : ℝ)
    (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (history remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 8 ≤ history.length) :
    signedTest (sixthPolicy n e q om N) weight T history positive mass remaining =
      signedTest (ordinaryParityRosserPolicy false
        (N ^ actualParent n e q om N history))
        weight T history positive mass remaining := by
  apply signedTest_congr_extensions
  intro later b
  have hdeep : ¬(later ++ history).length ≤ 6 := by
    simp only [List.length_append]
    omega
  simp only [sixthPolicy, firstExitDepthSplicePolicy, if_neg hdeep,
    frozenParityRosserPolicy, ancestorFrozenPolicy,
    rosserAncestor_append 6 later history (by omega), actualParent]

theorem eighth_test_eq_ordinary_of_owner (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (history remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 8 ≤ history.length) (c : Cell)
    (ho : retainedOwner delta N history = some c) :
    signedTest (eighthContinuation delta n e q om N) weight T
        history positive mass remaining =
      signedTest (ordinaryParityRosserPolicy false
        (N ^ (finiteCap n c (point8 N history) : ℝ)))
        weight T history positive mass remaining := by
  have hc : selectedCap delta n N history =
      some (finiteCap n c (point8 N history)) := by
    rw [selectedCap_eq_map_owner, ho]
    rfl
  apply signedTest_congr_extensions
  intro later b
  simp only [eighthContinuation, selectedCap_append delta n N later history hlen, hc]

/-- Unowned or trimmed-out prefixes have ZERO continuation change, for
arbitrary full-q tests, because the selector stays frozen on descendants. -/
theorem eighth_test_eq_sixth_of_no_owner (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om N : ℝ) (weight : ℕ → ℝ) (T : Bool → List ℕ → ℝ)
    (history remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (hlen : 8 ≤ history.length) (ho : retainedOwner delta N history = none) :
    signedTest (eighthContinuation delta n e q om N) weight T
        history positive mass remaining =
      signedTest (sixthPolicy n e q om N) weight T history positive mass remaining := by
  have hc : selectedCap delta n N history = none := by
    rw [selectedCap_eq_map_owner, ho]
    rfl
  apply signedTest_congr_extensions
  intro later b
  simp only [eighthContinuation, selectedCap_append delta n N later history hlen, hc]

/-- The exact new predecessor occurrence list, with unit arithmetic weights. -/
def frontier (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) : List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 8 (sixthPolicy n e q om (N : ℝ)) (fun _ => 1)
    [] true 1 (roughPrimeUniverse N cap w z)

theorem frontier_length (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ frontier n e q om N cap w z) : s.selectedPrefix.length = 8 :=
  firstExitDepthFrontier_selected_length 8 (sixthPolicy n e q om (N : ℝ))
    (fun _ => 1) [] (roughPrimeUniverse N cap w z) true 1 (by simp) s hs

/-- These lists are the existing new-policy lists, not copies of an old
raw frontier. Their equality is only across the rank-eight splice itself. -/
theorem states_eq_owner_filter (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    states delta n e q om N cap w z (fun _ => 1) c =
      (frontier n e q om N cap w z).filter (fun s =>
        decide (retainedOwner delta (N : ℝ) s.selectedPrefix = some c)) := by
  unfold states frontier
  rw [frontier_eq_new_sixth]
  congr 1
  funext s
  exact congrArg decide (propext (retainedOwner_some_iff delta (N : ℝ) s.selectedPrefix c).symm)

/-- The actual frontier state has positive incoming sign and unit mass at
rank eight. The continuation still has both positive and negative leaves. -/
theorem frontier_sign_mass (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (s : FirstExitDepthState ℕ)
    (hs : s ∈ frontier n e q om N cap w z) : s.positive = true ∧ s.mass = 1 := by
  have hlen := frontier_length n e q om N cap w z s hs
  have hsign := mem_firstExitDepthFrontier_positive_eq_evenListLength 8
    (sixthPolicy n e q om (N : ℝ)) (fun _ => 1)
    (roughPrimeUniverse N cap w z) s hs
  have hmass := mem_firstExitDepthFrontier_mass_eq_selected_prod 8
    (sixthPolicy n e q om (N : ℝ)) (fun _ => 1)
    (roughPrimeUniverse N cap w z) s hs
  exact ⟨by simpa [evenListLength, hlen] using hsign, by simpa using hmass⟩

/-- Saving orientation is OLD minus NEW; no positivity is asserted for an
arbitrary arithmetic test. The sign-sensitive beta terminal is unchanged. -/
def ordinarySaving (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w L : ℝ) (G : ℕ → ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) : ℝ :=
  signedTest (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
      (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
      (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.positive s.mass s.remaining

def ownedSource (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) (c : Cell) : ℝ :=
  ((states delta n e q om N cap w z (fun _ => 1) c).map
    (ordinarySaving n e q om N cap w L G c)).sum

/-- Exact full87 arithmetic partition. No tuple-existence theorem is used
as a surrogate for equality of sums; all occurrence multiplicities survive. -/
theorem physical_saving_eq_owned_sources (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ)
    (om : ℝ) (N cap : ℕ) (w z L : ℝ) (G : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G -
      physical (policy delta n e q om (N : ℝ)) N cap w z L G =
        ∑ c : Cell, ownedSource delta n e q om N cap w z L G c := by
  let oldTest (s : FirstExitDepthState ℕ) : ℝ :=
    signedTest (sixthPolicy n e q om (N : ℝ)) (fun _ => 1)
      (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining
  let newTest (s : FirstExitDepthState ℕ) : ℝ :=
    signedTest (eighthContinuation delta n e q om (N : ℝ)) (fun _ => 1)
      (attachedLeafTest N cap 1 w L G) s.selectedPrefix s.positive s.mass s.remaining
  let saving := fun s => oldTest s - newTest s
  have hroot : physical (sixthPolicy n e q om (N : ℝ)) N cap w z L G -
      physical (policy delta n e q om (N : ℝ)) N cap w z L G =
        ((frontier n e q om N cap w z).map saving).sum := by
    have h := eighth_physical_change delta n e q om N cap w z L G
    have hs := sum_map_opposite (frontier n e q om N cap w z) newTest oldTest
    change -(eighthChange delta n e q om N cap w z L G) = _ at hs
    linarith
  rw [hroot]
  have hzero : ∀ s ∈ frontier n e q om N cap w z,
      retainedOwner delta (N : ℝ) s.selectedPrefix = none → saving s = 0 := by
    intro s hs ho
    have hl := frontier_length n e q om N cap w z s hs
    have heq := eighth_test_eq_sixth_of_no_owner delta n e q om (N : ℝ)
      (fun _ => 1) (attachedLeafTest N cap 1 w L G)
      s.selectedPrefix s.remaining s.positive s.mass (by omega) ho
    dsimp only [saving, oldTest, newTest]
    rw [heq, sub_self]
  rw [sum_by_owner _ (fun s => retainedOwner delta (N : ℝ) s.selectedPrefix) saving hzero]
  apply Finset.sum_congr rfl
  intro c _
  unfold ownedSource
  rw [states_eq_owner_filter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  obtain ⟨hfront, ho⟩ := List.mem_filter.mp hs
  have howner := of_decide_eq_true ho
  have hl := frontier_length n e q om N cap w z s hfront
  dsimp only [saving, oldTest, newTest, ordinarySaving]
  rw [sixth_test_eq_ordinary n e q om (N : ℝ) _ _ _ _ _ _ (by omega),
    eighth_test_eq_ordinary_of_owner delta n e q om (N : ℝ) _ _ _ _ _ _ (by omega) c howner]

end
end ImbalancedChen.P4AOriginalFull87OwnedEighthSource
