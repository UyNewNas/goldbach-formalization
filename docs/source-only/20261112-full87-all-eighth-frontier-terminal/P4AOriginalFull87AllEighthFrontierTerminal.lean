import ImbalancedChen.P4AOriginalFull87SelectedCanonicalTerminal
import ImbalancedChen.P4AOriginalFull87InheritedTerminalLevel
import ImbalancedChen.PrimeHistoryLogCoordinates
import ImbalancedChen.FirstExitFrontierInvariants
import ImbalancedChen.RoughPrimeUniverse
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The actual rank-eight frontier, including the original occurrence list,
determines its canonical eight-prime tuple WITHOUT assuming a source witness.
We recover the tuple from the reverse-stored physical history, prove its
prime and N-deletion properties from the SAME actual carrier, and recover
the actual mass, sign and exact post-last-prime suffix. No sorting, Finset
quotient, owner substitution, or history replacement is performed.

For selectedCap=some, the original owner/strict trim follows from
selectedCap_some_spec, and the pre-existing FilteredSourceSupply may be
applied to this recovered exact tuple. The prior selected-canonical terminal
proof then applies to the SAME state. For selectedCap=none, use the literal
inherited terminal theorem with no selected-owner mask. This joins the two
actual eighth branches on every frontier occurrence, not merely the
previously singled-out canonical source states.

No external PP or asymptotic theorem is proved or invoked. All statements
remain Lean candidates pending the pinned compiler/dependency closure.
-/

namespace ImbalancedChen.P4AOriginalFull87AllEighthFrontierTerminal
noncomputable section
open scoped Classical
open P4AOriginalFull87SevenCubeAdmission (pre pre_ofFn pre_length point)
open P4AOriginalFull87ActualSourceMembership (canonicalState)
open P4AOriginalFull87FiniteEighthPolicy (selectedCap selectedCap_some_spec)
open P4AOriginalFull87LicensedSixthRealization (FilteredSourceSupply)
open P4AOriginalFull87StrictActionTrim (trim)
open P4AOriginalFull87HistoryCore (width)

/-- Every actual rank-eight occurrence (not an arbitrary synthetic source)
has a canonical tuple with its exact selected history, sign, mass and
target-deleted strict suffix. In particular all eight entries are genuine
primes not dividing N. This is a structural identity, not an extra field. -/
theorem actual_rank_eight_state_canonical
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z)) :
    ∃ p : Fin 8 → ℕ,
      (∀ i, (p i).Prime) ∧ (∀ i, ¬p i ∣ N) ∧
      state = canonicalState N cap w weight p := by
  let p : Fin 8 → ℕ := primeHistoryTuple 8 state.selectedPrefix
  have hlen : state.selectedPrefix.length = 8 :=
    firstExitDepthFrontier_selected_length 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight [] (roughPrimeUniverse N cap w z) true 1
      (by simp) state hs
  have hpre : pre p = state.selectedPrefix := by
    rw [pre_ofFn]
    exact primeHistoryTuple_reverse_ofFn hlen
  have hsign : state.positive = true := by
    have hh := mem_firstExitDepthFrontier_positive_eq_evenListLength 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight (roughPrimeUniverse N cap w z) state hs
    rw [← hpre] at hh
    simpa [pre, evenListLength] using hh
  have hmass : state.mass = ((pre p).map weight).prod := by
    have hh := mem_firstExitDepthFrontier_mass_eq_selected_prod 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight (roughPrimeUniverse N cap w z) state hs
    rwa [← hpre] at hh
  obtain ⟨last, tail, hsel, _hlastMem, hrem⟩ :=
    mem_firstExitDepthFrontier_roughPrime_remaining 8 (by decide)
      (P4AOriginalFull87LicensedSixthPolicy.policy
        delta n e q om (N : ℝ))
      weight N cap w z state hs
  have hlast : last = p 7 := by
    have hh := congrArg (fun xs : List ℕ => xs.headD 0) (hpre.trans hsel)
    simpa only [pre, List.headD_cons] using hh.symm
  have hremaining : state.remaining = roughPrimeUniverse N cap w (p 7 : ℝ) := by
    rw [hlast] at hrem
    exact hrem
  refine ⟨p, ?_, ?_, ?_⟩
  · intro i
    exact mem_roughPrimeUniverse_prime
      (primeHistoryTuple_frontier_mem 8
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        weight N cap w z state hs i)
  · intro i
    exact mem_roughPrimeUniverse_not_dvd
      (primeHistoryTuple_frontier_mem 8
        (P4AOriginalFull87LicensedSixthPolicy.policy
          delta n e q om (N : ℝ))
        weight N cap w z state hs i)
  · cases state with
    | mk selectedPrefix positive mass remaining =>
        dsimp only at hpre hsign hmass hremaining
        subst selectedPrefix
        subst positive
        subst mass
        subst remaining
        rfl

/-- The arbitrary ACTUAL selected eighth state is canonical because it
is on the original frontier, and its owner/trim is genuine because the
original selectedCap returns some a. FilteredSourceSupply is an established
manuscript-internal schedule output, not a fresh goal-shaped premise. -/
theorem actual_selected_frontier_terminal_product_lt_fixed_power
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (hsupply : FilteredSourceSupply s r n e q om)
    (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ) ^ mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (a : ℚ)
    (ha : selectedCap (width r) n (N : ℝ) state.selectedPrefix = some a)
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight state.selectedPrefix state.positive state.mass state.remaining) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  obtain ⟨p, hp, hdelete, hcanonical⟩ :=
    actual_rank_eight_state_canonical (width r) n e q om
      N cap w z weight state hstate
  obtain ⟨c, _howner, htrim, _hcap⟩ :=
    selectedCap_some_spec (width r) n (N : ℝ) state.selectedPrefix a ha
  have ht : point (N : ℝ) p ∈ trim c (width r) := by
    rw [hcanonical] at htrim
    change P4AOriginalFull87SourceDispatch.point8 (N : ℝ) (pre p) ∈
      trim c (width r) at htrim
    rw [P4AOriginalFull87FiniteEighthPolicy.point8_at_eight
      (N : ℝ) (pre p) (pre_length p)] at htrim
    exact htrim
  rw [hcanonical] at hleaf
  exact P4AOriginalFull87SelectedCanonicalTerminal.actual_selected_canonical_terminal_product_lt_fixed_power
    s r n e q om N cap w z weight hsupply hN hw hz hzcap p hp
    hdelete c ht leaf hleaf

/-- Both actual eighth continuation cases, on EVERY rank-eight occurrence:
none inherits the true sixth policy, some uses the SAME finite eighth
owner/trim. No source list is replaced and no terminal occurrences collapse.
The sixth predecessor's real nonnegativity condition is preserved in the
inherited branch (not inferred from a selected mask). -/
theorem actual_all_eighth_frontier_terminal_product_lt_fixed_power
    (s r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (hsupply : FilteredSourceSupply s r n e q om)
    (he : (0 : ℝ) ≤
      ((P4AOriginalCompleteSixthChronology.data e q om).e : ℝ))
    (hN : 1 < (N : ℝ))
    (hw : w ≤ (N : ℝ) ^ (53 / 13824 : ℝ))
    (hz : (N : ℝ) ^ mu ≤ z) (hzcap : z ≤ (cap : ℝ))
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ firstExitDepthFrontier 8
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N cap w z))
    (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (P4AOriginalFull87LicensedSixthPolicy.policy
        (width r) n e q om (N : ℝ))
      weight state.selectedPrefix state.positive state.mass state.remaining) :
    (leaf.selected.prod : ℝ) < (N : ℝ) ^ (299 / 500 : ℝ) := by
  cases hc : selectedCap (width r) n (N : ℝ) state.selectedPrefix with
  | none =>
      exact P4AOriginalFull87InheritedTerminalLevel.actual_inherited_terminal_product_lt_fixed_power
        (width r) n e q om N cap w z weight he hN state
        hstate hc leaf hleaf
  | some a =>
      exact actual_selected_frontier_terminal_product_lt_fixed_power
        s r n e q om N cap w z weight hsupply hN hw hz hzcap
        state hstate a hc leaf hleaf

end
end ImbalancedChen.P4AOriginalFull87AllEighthFrontierTerminal
