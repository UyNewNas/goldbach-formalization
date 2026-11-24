import ImbalancedChen.P4AOriginalFull87SourceDispatch
import ImbalancedChen.P4AOriginalCompleteSixthChronology

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

This module instantiates the S10 original-source dispatcher with S09's
complete sixth endpoint producer, not the held eleven-cell parent. The
actual original fourth/fifth data, saved sixth source, eleven original
cells and nineteen later sixth actions are inherited unchanged.

The list construction has no caller-supplied parent, ownership certificate
or current-parent inequality at its public terminal. Its elementary fold
lemmas prove that every source is applied and that order and repetition of
source labels do not affect the endpoint policy.

This is NOT the common compact/buffered realization. In particular, the
actual supported-third premise in S09 is not discharged. No assertion of
reverse prime-tuple admission, saved-gain preservation, finite scalar-cap
alphabet, positive-presieve saving, reserve payment or density is made.
-/
namespace ImbalancedChen.P4AOriginalFull87CompleteSixthDispatch
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary P4AOriginalFull87SourceDispatch

/-- A finite fold of the original, localized rank-eight actions. -/
def applySources (N : ℝ) (parent : Bool → List ℕ → Bool) :
    List Cell → Bool → List ℕ → Bool
  | [] => parent
  | c :: cs => localPolicy c N (applySources N parent cs)

theorem applySources_through_eight (N : ℝ)
    (parent : Bool → List ℕ → Bool) (cs : List Cell)
    (positive : Bool) (pre : List ℕ) (hl : pre.length ≤ 8) :
    applySources N parent cs positive pre = parent positive pre := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      change localPolicy c N (applySources N parent cs) positive pre = _
      rw [localPolicy_through_eight c N _ positive pre hl]
      exact ih

theorem applySources_outside (N : ℝ)
    (parent : Bool → List ℕ → Bool) (cs : List Cell)
    (positive : Bool) (pre : List ℕ)
    (ho : ∀ c ∈ cs, ownerAtPrefix N pre ≠ some c) :
    applySources N parent cs positive pre = parent positive pre := by
  revert ho
  induction cs with
  | nil => intro _; rfl
  | cons c cs ih =>
      intro ho
      change localPolicy c N (applySources N parent cs) positive pre = _
      rw [localPolicy_outside c N _ positive pre (ho c (by simp))]
      exact ih (fun d hd => ho d (by simp [hd]))

theorem applySources_selected (N : ℝ)
    (parent : Bool → List ℕ → Bool) (cs : List Cell)
    (c : Cell) (hc : c ∈ cs) (positive : Bool) (pre : List ℕ)
    (hl : 8 < pre.length) (ho : ownerAtPrefix N pre = some c) :
    applySources N parent cs positive pre =
      ordinaryParityRosserPolicy false (N ^ newCap c (point8 N pre)) positive pre := by
  revert hc
  induction cs with
  | nil => intro hc; simp at hc
  | cons d ds ih =>
      intro hc
      change localPolicy d N (applySources N parent ds) positive pre = _
      by_cases hdc : d = c
      · subst d
        exact localPolicy_selected c N _ positive pre hl ho
      · have hod : ownerAtPrefix N pre ≠ some d := by
          intro hd
          have hcd : c = d := Option.some.inj (ho.symm.trans hd)
          exact hdc hcd.symm
        rw [localPolicy_outside d N _ positive pre hod]
        have htail : c ∈ ds := by
          rcases List.mem_cons.mp hc with h | h
          · exact (hdc h.symm).elim
          · exact h
        exact ih htail

theorem applySources_even (N : ℝ) (parent : Bool → List ℕ → Bool)
    (hp : ∀ pre, parent true pre = true) (cs : List Cell) :
    ∀ pre, applySources N parent cs true pre = true := by
  induction cs with
  | nil => exact hp
  | cons c cs ih =>
      intro pre
      exact localPolicy_even c N (applySources N parent cs) ih pre

/-- Extensional finite-set dependence: reordering or duplicating labels
cannot replace a different owner's continuation. No permutation witness
or disjointness hypothesis is supplied by a caller. -/
theorem applySources_eq_of_same_membership (N : ℝ)
    (parent : Bool → List ℕ → Bool) (cs ds : List Cell)
    (hmem : ∀ c, c ∈ cs ↔ c ∈ ds) :
    applySources N parent cs = applySources N parent ds := by
  funext positive pre
  by_cases hl : pre.length ≤ 8
  · rw [applySources_through_eight N parent cs positive pre hl,
      applySources_through_eight N parent ds positive pre hl]
  · have hlt : 8 < pre.length := lt_of_not_ge hl
    cases ho : ownerAtPrefix N pre with
    | none =>
        have hc : ∀ c ∈ cs, ownerAtPrefix N pre ≠ some c := by
          intro c _
          simp [ho]
        have hd : ∀ c ∈ ds, ownerAtPrefix N pre ≠ some c := by
          intro c _
          simp [ho]
        rw [applySources_outside N parent cs positive pre hc,
          applySources_outside N parent ds positive pre hd]
    | some c =>
        by_cases hc : c ∈ cs
        · rw [applySources_selected N parent cs c hc positive pre hlt ho,
            applySources_selected N parent ds c ((hmem c).mp hc) positive pre hlt ho]
        · have hd : c ∉ ds := fun h => hc ((hmem c).mpr h)
          have hout : ∀ (ls : List Cell), c ∉ ls →
              ∀ d ∈ ls, ownerAtPrefix N pre ≠ some d := by
            intro ls hn d hdin he
            have hcd : c = d := Option.some.inj (ho.symm.trans he)
            exact hn (hcd.symm ▸ hdin)
          rw [applySources_outside N parent cs positive pre (hout cs hc),
            applySources_outside N parent ds positive pre (hout ds hd)]

/-- Every label of the original full source dictionary, exactly once.
The fold theorem makes the arbitrary Finset list ordering immaterial. -/
def allCells : List Cell := (Finset.univ : Finset Cell).toList

theorem mem_allCells (c : Cell) : c ∈ allCells := by
  simp [allCells]

theorem allCells_nodup : allCells.Nodup := by
  simp [allCells]

/-- The concrete endpoint policy: the only predecessor is S09's complete
sixth policy on R06's unchanged original fourth/fifth data. -/
def policy (e : ℚ) (q : ℕ) (omega N : ℝ) : Bool → List ℕ → Bool :=
  applySources N
    (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N) allCells

/-- Direct original-source continuation, defined independently of the
list fold. The no-owner branch inherits the complete sixth predecessor. -/
def continuation (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ) : Bool :=
  match ownerAtPrefix N pre with
  | none => P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N positive pre
  | some c =>
      ordinaryParityRosserPolicy false (N ^ newCap c (point8 N pre)) positive pre

theorem policy_through_eight (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ) (hl : pre.length ≤ 8) :
    policy e q omega N positive pre =
      P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N positive pre :=
  applySources_through_eight N _ allCells positive pre hl

theorem policy_outside (e : ℚ) (q : ℕ) (omega N : ℝ)
    (positive : Bool) (pre : List ℕ) (ho : ownerAtPrefix N pre = none) :
    policy e q omega N positive pre =
      P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N positive pre := by
  apply applySources_outside N _ allCells positive pre
  intro c _
  simp [ho]

theorem policy_selected (e : ℚ) (q : ℕ) (omega N : ℝ)
    (c : Cell) (positive : Bool) (pre : List ℕ)
    (hl : 8 < pre.length) (ho : ownerAtPrefix N pre = some c) :
    policy e q omega N positive pre =
      ordinaryParityRosserPolicy false (N ^ newCap c (point8 N pre)) positive pre :=
  applySources_selected N _ allCells c (mem_allCells c) positive pre hl ho

theorem policy_even (e : ℚ) (q : ℕ) (omega N : ℝ) (pre : List ℕ) :
    policy e q omega N true pre = true :=
  applySources_even N _
    (P4AOriginalCompleteSixthChronology.current_policy_even e q omega N) allCells pre

/-- Any complete enumeration of these original sources gives this same
concrete policy, including an enumeration arranged in original stage order. -/
theorem policy_eq_of_complete_enumeration (e : ℚ) (q : ℕ) (omega N : ℝ)
    (cs : List Cell) (hcs : ∀ c : Cell, c ∈ cs) :
    applySources N
      (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N) cs =
        policy e q omega N := by
  apply applySources_eq_of_same_membership
  intro c
  exact ⟨fun _ => mem_allCells c, fun _ => hcs c⟩

/-- The actual finite fold is a single depth-eight splice on the complete
sixth tree; no equality to the old held-eleven tree is asserted. -/
theorem policy_eq_splice (e : ℚ) (q : ℕ) (omega N : ℝ) :
    policy e q omega N =
      firstExitDepthSplicePolicy 8
        (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N)
        (continuation e q omega N) := by
  funext positive pre
  by_cases hl : pre.length ≤ 8
  · rw [policy_through_eight e q omega N positive pre hl]
    simp only [firstExitDepthSplicePolicy, if_pos hl]
  · have hlt : 8 < pre.length := lt_of_not_ge hl
    simp only [firstExitDepthSplicePolicy, if_neg hl]
    cases ho : ownerAtPrefix N pre with
    | none =>
        rw [policy_outside e q omega N positive pre ho]
        simp only [continuation, ho]
    | some c =>
        rw [policy_selected e q omega N c positive pre hlt ho]
        simp only [continuation, ho]

/-- Frontier equality is for arbitrary occurrence lists, weights, signs
and incoming mass. It neither drops duplicates nor admits new states. -/
theorem policy_frontier (e : ℚ) (q : ℕ) (omega N : ℝ)
    (weight : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (policy e q omega N) weight pre positive mass carrier =
      firstExitDepthFrontier 8
        (P4AOriginalCompleteSixthChronology.currentSixthPolicy e q omega N)
        weight pre positive mass carrier := by
  rw [policy_eq_splice]
  exact firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl _ _
    weight pre carrier positive mass

/-- Later nodes continue to use the very same selected eighth ancestor. -/
theorem policy_on_selected_descendants (e : ℚ) (q : ℕ) (omega N : ℝ)
    (c : Cell) (pre later : List ℕ) (hl : pre.length = 8)
    (hs : Source c (primeHistoryLogCoordinates N 8 pre)) (p : ℕ) (positive : Bool) :
    policy e q omega N positive ((p :: later) ++ pre) =
      ordinaryParityRosserPolicy false
        (N ^ newCap c (primeHistoryLogCoordinates N 8 pre))
        positive ((p :: later) ++ pre) := by
  have hpre : 8 ≤ pre.length := by omega
  have hlt : 8 < ((p :: later) ++ pre).length := by
    simp only [List.length_append, List.length_cons]
    omega
  have ho : ownerAtPrefix N ((p :: later) ++ pre) = some c := by
    rw [ownerAtPrefix_append N (p :: later) pre hpre]
    exact (ownerAtPrefix_rank_eight N pre hl c).mpr hs
  rw [policy_selected e q omega N c positive _ hlt ho,
    point8_append N (p :: later) pre hpre, point8,
    rosserAncestor_self_of_length 8 pre hl]

/-- An actual state of the newly constructed tree inherits the real
complete-sixth Rosser admissibility. This does not prove reverse admission. -/
theorem actual_eighth_frontier_admissible (e : ℚ) (q : ℕ) (omega : ℝ)
    (N enumerationCap : ℕ) (w z : ℝ) (weight : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hs : state ∈ firstExitDepthFrontier 8 (policy e q omega (N : ℝ))
      weight [] true 1 (roughPrimeUniverse N enumerationCap w z)) :
    ordinaryRosserPrefixAdmissible false
      ((N : ℝ) ^ P4AOriginalCompleteSixthChronology.currentSixthExponent
        e q omega (N : ℝ) (rosserAncestor 6 state.selectedPrefix))
      state.selectedPrefix := by
  rw [policy_frontier] at hs
  exact P4AOriginalCompleteSixthChronology.actual_eighth_frontier_admissible
    e q omega N enumerationCap w z weight state hs

end
end ImbalancedChen.P4AOriginalFull87CompleteSixthDispatch
