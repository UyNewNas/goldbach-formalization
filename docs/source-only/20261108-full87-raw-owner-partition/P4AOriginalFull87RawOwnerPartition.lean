import ImbalancedChen.P4AOriginalFull87ActualSourceMembership
import ImbalancedChen.P4AOriginalFull87ArchiveSourceIndex
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

An exact signed-sum partition of the ACTUAL rank-eight first-exit frontier.
The owner is the original strict affine source owner, not an assumed
classification or a replacement of the unchanged upstream policy.
A raw frontier occurrence is either outside all original 87 cells or in
exactly one cell-filter list. List filtering retains duplicate occurrences,
the actual state.mass, sign, and all other data of each occurrence.

The archive label is only provenance metadata for the owner. This does
not identify the archived numerical gain with the physical signed sum.
-/

namespace ImbalancedChen.P4AOriginalFull87RawOwnerPartition
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary
open P4AOriginalFull87ActualSourceMembership
open P4AOriginalFull87ArchiveSourceIndex
open P4AOriginalFull87SourceDispatch

/-- A finite partition identity, proved element by element. It never
quotients a List or assumes that the elements are distinct. -/
private theorem list_option_owner_partition
    {α κ : Type*} [Fintype κ] [DecidableEq κ]
    (owner : α → Option κ) (value : α → ℝ) :
    ∀ xs : List α,
      (xs.map value).sum =
        ((xs.filter (fun x => decide (owner x = none))).map value).sum +
          ∑ c : κ,
            ((xs.filter (fun x => decide (owner x = some c))).map value).sum := by
  classical
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hnone :
          (((x :: xs).filter (fun y => decide (owner y = none))).map value).sum =
            (if owner x = none then value x else 0) +
              ((xs.filter (fun y => decide (owner y = none))).map value).sum := by
        by_cases h : owner x = none <;>
          simp [List.filter_cons, h]
      have hone (c : κ) :
          (((x :: xs).filter (fun y => decide (owner y = some c))).map value).sum =
            (if owner x = some c then value x else 0) +
              ((xs.filter (fun y => decide (owner y = some c))).map value).sum := by
        by_cases h : owner x = some c <;>
          simp [List.filter_cons, h]
      have howned :
          (∑ c : κ,
            (((x :: xs).filter (fun y => decide (owner y = some c))).map value).sum) =
          (∑ c : κ, if owner x = some c then value x else 0) +
            (∑ c : κ,
              ((xs.filter (fun y => decide (owner y = some c))).map value).sum) := by
        simp_rw [hone]
        rw [Finset.sum_add_distrib]
      have hone_owner :
          (if owner x = none then value x else 0) +
            (∑ c : κ, if owner x = some c then value x else 0) =
            value x := by
        cases h : owner x with
        | none => simp [h]
        | some c => simp [h]
      calc
        ((x :: xs).map value).sum = value x + (xs.map value).sum := rfl
        _ = value x +
              (((xs.filter (fun y => decide (owner y = none))).map value).sum +
                ∑ c : κ,
                  ((xs.filter (fun y => decide (owner y = some c))).map value).sum) := by
              rw [ih]
        _ = (((x :: xs).filter (fun y => decide (owner y = none))).map value).sum +
              ∑ c : κ,
                (((x :: xs).filter (fun y => decide (owner y = some c))).map value).sum := by
              rw [hnone, howned]
              linear_combination -hone_owner

/-- Precisely the original rank-eight frontier of the COMPLETE sixth
producer. It is deliberately not reconstructed from archive row labels. -/
def actualRawFrontier (e : ℚ) (q : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) :
    List (FirstExitDepthState ℕ) :=
  firstExitDepthFrontier 8
    (P4AOriginalFull87CompleteSixthDispatch.policy e q omega (N : ℝ))
    weight [] true 1 (roughPrimeUniverse N cap w z)

/-- The exact complement of ALL 87 strict affine source owners inside the
same actual list, including states which have no selected source. -/
def actualUnownedFrontier (e : ℚ) (q : ℕ) (omega : ℝ)
    (N cap : ℕ) (w z : ℝ) (weight : ℕ → ℝ) :
    List (FirstExitDepthState ℕ) :=
  (actualRawFrontier e q omega N cap w z weight).filter
    (fun s => decide (ownerAtPrefix (N : ℝ) s.selectedPrefix = none))

/-- A raw occurrence's signed value is neither dropped nor counted twice.
The formula is valid for the real original first-exit state.mass, for
signed beta-attached tests, and for any later fixed real test function.
It does not assert that any source has a positive arithmetic saving. -/
theorem actual_raw_owned_unowned_sum
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z : ℝ) (weight : ℕ → ℝ)
    (value : FirstExitDepthState ℕ → ℝ) :
    ((actualRawFrontier e q omega N cap w z weight).map value).sum =
      ((actualUnownedFrontier e q omega N cap w z weight).map value).sum +
        ∑ c : Cell,
          ((sourceStates e q omega N cap w z weight c).map value).sum := by
  simpa [actualRawFrontier, actualUnownedFrontier, sourceStates] using
    (list_option_owner_partition
      (owner := fun s : FirstExitDepthState ℕ =>
        ownerAtPrefix (N : ℝ) s.selectedPrefix)
      (value := value)
      (xs := actualRawFrontier e q omega N cap w z weight))

/-- Two distinct affine cells cannot each charge the same raw state.
The result is derived from the ORIGINAL owner function in the filters. -/
theorem actual_owner_fibres_disjoint
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z : ℝ) (weight : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) (c d : Cell)
    (hc : s ∈ sourceStates e q omega N cap w z weight c)
    (hd : s ∈ sourceStates e q omega N cap w z weight d) : c = d := by
  have hc' : ownerAtPrefix (N : ℝ) s.selectedPrefix = some c := by
    simpa [sourceStates] using (List.mem_filter.mp hc).2
  have hd' : ownerAtPrefix (N : ℝ) s.selectedPrefix = some d := by
    simpa [sourceStates] using (List.mem_filter.mp hd).2
  exact Option.some.inj (hc'.symm.trans hd')

/-- Deterministic archive provenance of a *genuine owned* frontier state.
This is a label, not a numerical gain theorem and not a proof of a
saved geometry witness. -/
def actualArchiveKey (N : ℝ) (s : FirstExitDepthState ℕ) : Option String :=
  (ownerAtPrefix N s.selectedPrefix).map
    (fun c => (archivedRecordForOriginalCell c).1)

theorem actual_owned_state_has_original_archive_key
    (e : ℚ) (q : ℕ) (omega : ℝ) (N cap : ℕ)
    (w z : ℝ) (weight : ℕ → ℝ)
    (s : FirstExitDepthState ℕ) (c : Cell)
    (hc : s ∈ sourceStates e q omega N cap w z weight c) :
    actualArchiveKey (N : ℝ) s =
      some (archivedRecordForOriginalCell c).1 := by
  have ho : ownerAtPrefix (N : ℝ) s.selectedPrefix = some c := by
    simpa [sourceStates] using (List.mem_filter.mp hc).2
  simp [actualArchiveKey, ho]

end
end ImbalancedChen.P4AOriginalFull87RawOwnerPartition
