import ImbalancedChen.P4AOriginalFull87Ownership
import ImbalancedChen.P4AOriginalFull87PrefixBinding
import ImbalancedChen.P4AOriginalFiniteSignedHistoryRefinement
import ImbalancedChen.P4AOriginalArchiveFourteenPositivePresieve

/-!
SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.
The exact original source union has a deterministic unique owner.  A source
record is read only on its own reversed rank-eight ancestor.  The localized
replacement below preserves the old continuation outside that source;
in particular it never resets another eighth action to a sixth parent.

This is original-source dispatch and a common finite source partition.
It is NOT the finite buffered policy: no finite cap alphabet, uniform
history margin, full-sixth bound, or final density estimate is asserted.
-/
namespace ImbalancedChen.P4AOriginalFull87SourceDispatch
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87SourceDictionary P4AOriginalFull87Ownership
open P4AOriginalFiniteSignedHistoryRefinement

def sourceOwner (t : Point) : Option Cell :=
  if h : ∃ c : Cell, Source c t then some (Classical.choose h) else none

theorem sourceOwner_some_iff (t : Point) (c : Cell) :
    sourceOwner t = some c ↔ Source c t := by
  by_cases hex : ∃ d : Cell, Source d t
  · rw [sourceOwner,dif_pos hex,Option.some.injEq]
    exact ⟨fun he => he ▸ Classical.choose_spec hex,
      fun hc => source_owner_unique (Classical.choose_spec hex) hc⟩
  · rw [sourceOwner,dif_neg hex]
    constructor
    · intro h; cases h
    · intro hc; exact (hex ⟨c,hc⟩).elim

theorem sourceOwner_none_iff (t : Point) :
    sourceOwner t = none ↔ ∀ c : Cell, ¬Source c t := by
  by_cases hex : ∃ c : Cell, Source c t
  · rw [sourceOwner,dif_pos hex]
    constructor
    · intro h; cases h
    · intro h; exact (h _ (Classical.choose_spec hex)).elim
  · simp [sourceOwner,hex,not_exists.mp hex]

def point8 (N : ℝ) (pre : List ℕ) : Point :=
  primeHistoryLogCoordinates N 8 (rosserAncestor 8 pre)

def ownerAtPrefix (N : ℝ) (pre : List ℕ) : Option Cell :=
  if 8 ≤ pre.length then sourceOwner (point8 N pre) else none

theorem point8_append (N : ℝ) (later pre : List ℕ) (hpre : 8 ≤ pre.length) :
    point8 N (later ++ pre) = point8 N pre := by
  simp only [point8,rosserAncestor_append 8 later pre hpre]

theorem ownerAtPrefix_append (N : ℝ) (later pre : List ℕ) (hpre : 8 ≤ pre.length) :
    ownerAtPrefix N (later ++ pre) = ownerAtPrefix N pre := by
  have hl : 8 ≤ (later ++ pre).length := by simp only [List.length_append]; omega
  simp only [ownerAtPrefix,if_pos hpre,if_pos hl,point8_append N later pre hpre]

theorem ownerAtPrefix_rank_eight (N : ℝ) (pre : List ℕ) (hl : pre.length = 8) (c : Cell) :
    ownerAtPrefix N pre = some c ↔ Source c (primeHistoryLogCoordinates N 8 pre) := by
  rw [ownerAtPrefix,if_pos (by omega : 8 ≤ pre.length),point8,
    rosserAncestor_self_of_length 8 pre hl]
  exact sourceOwner_some_iff _ c

def selectedExponent (N : ℝ) (pre : List ℕ) : Option ℝ :=
  (ownerAtPrefix N pre).map (fun c => newCap c (point8 N pre))

theorem selectedExponent_append (N : ℝ) (later pre : List ℕ) (hl : 8 ≤ pre.length) :
    selectedExponent N (later ++ pre) = selectedExponent N pre := by
  simp only [selectedExponent,ownerAtPrefix_append N later pre hl,point8_append N later pre hl]

theorem selectedExponent_of_source (N : ℝ) (pre : List ℕ) (hl : pre.length = 8)
    (c : Cell) (hs : Source c (primeHistoryLogCoordinates N 8 pre)) :
    selectedExponent N pre = some (newCap c (primeHistoryLogCoordinates N 8 pre)) := by
  rw [selectedExponent,(ownerAtPrefix_rank_eight N pre hl c).mpr hs]
  simp only [Option.map_some,point8,rosserAncestor_self_of_length 8 pre hl]

theorem source_cap_positive {c : Cell} {t : Point} (hs : Source c t) : 0 < newCap c t := by
  have h := source_basic hs
  have h01 := h.2.2.2 0
  have h12 := h.2.2.2 1
  have h2 := h.2.1
  have hsq := (source_full_selected hs).1 0
  norm_num [prefixSquareExpr] at hsq
  norm_num at h01 h12
  linarith

theorem selectedExponent_bounds (N : ℝ) (pre : List ℕ) (a : ℝ)
    (ha : selectedExponent N pre = some a) : 0 < a ∧ a < (153/256 : ℝ) := by
  unfold selectedExponent at ha
  cases ho : ownerAtPrefix N pre with
  | none => simp [ho] at ha
  | some c =>
      simp only [ho,Option.map_some,Option.some.injEq] at ha
      have hs : Source c (point8 N pre) := by
        unfold ownerAtPrefix at ho
        split_ifs at ho with hl
        · exact (sourceOwner_some_iff _ c).mp ho
        · cases ho
      rw [← ha]
      exact ⟨source_cap_positive hs,source_physical_ceiling hs⟩

/-- Each local action changes later decisions only where its original
source owns the frozen eighth ancestor.  Outside that source it reads the
complete preceding policy, including any earlier eighth actions. -/
def localContinuation (c : Cell) (N : ℝ) (parent : Bool → List ℕ → Bool)
    (positive : Bool) (pre : List ℕ) : Bool :=
  if ownerAtPrefix N pre = some c then
    ordinaryParityRosserPolicy false (N ^ newCap c (point8 N pre)) positive pre
  else parent positive pre

def localPolicy (c : Cell) (N : ℝ) (parent : Bool → List ℕ → Bool) :
    Bool → List ℕ → Bool :=
  firstExitDepthSplicePolicy 8 parent (localContinuation c N parent)

theorem localPolicy_through_eight (c : Cell) (N : ℝ)
    (parent : Bool → List ℕ → Bool) (positive : Bool) (pre : List ℕ) (hl : pre.length ≤ 8) :
    localPolicy c N parent positive pre = parent positive pre := by
  simp only [localPolicy,firstExitDepthSplicePolicy,if_pos hl]

theorem localPolicy_outside (c : Cell) (N : ℝ)
    (parent : Bool → List ℕ → Bool) (positive : Bool) (pre : List ℕ)
    (ho : ownerAtPrefix N pre ≠ some c) :
    localPolicy c N parent positive pre = parent positive pre := by
  by_cases hl : pre.length ≤ 8
  · exact localPolicy_through_eight c N parent positive pre hl
  · simp only [localPolicy,firstExitDepthSplicePolicy,if_neg hl,localContinuation,if_neg ho]

theorem localPolicy_selected (c : Cell) (N : ℝ)
    (parent : Bool → List ℕ → Bool) (positive : Bool) (pre : List ℕ)
    (hl : 8 < pre.length) (ho : ownerAtPrefix N pre = some c) :
    localPolicy c N parent positive pre =
      ordinaryParityRosserPolicy false (N ^ newCap c (point8 N pre)) positive pre := by
  simp only [localPolicy,firstExitDepthSplicePolicy,if_neg (not_le.mpr hl),
    localContinuation,if_pos ho]

theorem localPolicy_even (c : Cell) (N : ℝ) (parent : Bool → List ℕ → Bool)
    (hp : ∀ pre, parent true pre = true) (pre : List ℕ) :
    localPolicy c N parent true pre = true := by
  by_cases hl : pre.length ≤ 8
  · rw [localPolicy_through_eight c N parent true pre hl]
    exact hp pre
  · simp [localPolicy,firstExitDepthSplicePolicy,hl,localContinuation,hp,
      ordinaryParityRosserPolicy,oddFirstExitPolicy]

theorem localPolicy_frontier (c : Cell) (N : ℝ) (parent : Bool → List ℕ → Bool)
    (h : ℕ → ℝ) (pre carrier : List ℕ) (positive : Bool) (mass : ℝ) :
    firstExitDepthFrontier 8 (localPolicy c N parent) h pre positive mass carrier =
      firstExitDepthFrontier 8 parent h pre positive mass carrier :=
  firstExitDepthFrontier_depthSplice_eq 8 8 le_rfl parent _ h pre carrier positive mass

/-- All original source actions commute because they have unique owners.
Thus chronological assembly introduces no conflicting same-stage choice. -/
theorem localPolicy_commute (c d : Cell) (N : ℝ) (parent : Bool → List ℕ → Bool) :
    localPolicy c N (localPolicy d N parent) = localPolicy d N (localPolicy c N parent) := by
  funext positive pre
  by_cases hl : pre.length ≤ 8
  · simp only [localPolicy_through_eight _ _ _ _ _ hl]
  · by_cases hc : ownerAtPrefix N pre = some c
    · by_cases hd : ownerAtPrefix N pre = some d
      · have hcd : c = d := Option.some.inj (hc.symm.trans hd)
        subst d
        rfl
      · simp only [localPolicy_selected _ _ _ _ _ (lt_of_not_ge hl) hc,
          localPolicy_outside _ _ _ _ _ hd]
    · by_cases hd : ownerAtPrefix N pre = some d
      · simp only [localPolicy_selected _ _ _ _ _ (lt_of_not_ge hl) hd,
          localPolicy_outside _ _ _ _ _ hc]
      · simp only [localPolicy_outside _ _ _ _ _ hc,localPolicy_outside _ _ _ _ _ hd]

/-- The test bank is fixed before N.  Original source guards are read at
rank8; every earlier mesh/owner test retains its own earlier rank. -/
def full87Tests : List PrefixTest :=
  (Finset.univ : Finset Cell).toList.map (fun c =>
    ⟨8,fun N pre => decide (Source c (primeHistoryLogCoordinates N 8 pre))⟩)

def commonTests (e : ℚ) (q : ℕ) (omega : ℝ) : List PrefixTest :=
  nativeTests (P4AOriginalArchiveFourteenPositivePresieve.data e q omega) ++ full87Tests

/-- Exact reindexing of occurrence Lists; a refinement neither discards
inherit/equality fibres nor creates any new member of the actual tree. -/
theorem one_common_source_partition (e : ℚ) (q : ℕ) (omega : ℝ)
    {α : Type*} (N : ℝ) (xs : List α) (prefix : α → List ℕ) (value : α → ℝ) :
    refinedSum (commonTests e q omega) N xs prefix value = (xs.map value).sum :=
  refinedSum_eq _ N xs prefix value

end
end ImbalancedChen.P4AOriginalFull87SourceDispatch
