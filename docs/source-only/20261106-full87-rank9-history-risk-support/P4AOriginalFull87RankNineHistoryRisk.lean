import ImbalancedChen.P4AOriginalFull87RankNinePhysicalInherited
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.
P1.4 actual rank-nine inherited odd-square risk on the full87 eighth source.
The threshold below is built from the SAME finite historical prime word.
The two actual frozen levels are evaluated separately; their minimum
only gives a safe support filter and does not replace either policy.
No small reserve bound or original-arithmetic identification is claimed.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87HistoryCore (width)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87FailedAttempts (FirstExitRejectedAttempt)
open P4AOriginalFull87RankNinePhysicalInherited
  (rankNineInheritedAt inheritedMode actual_rankNine_root_and_three_modes
   rankNineInheritedReciprocalCost ownedRankNineInheritedCost
   ownedRankNineInheritedSigned)

/-- All actual historical square-suffix tests, with even suffixes set
to zero. The real eighth historical word is never replaced by a set
in the event enumeration; this Finset only computes the Rosser test. -/
def historyOddSquareTerms (history : List ℕ) : List ℝ :=
  history.map (fun r =>
    if ¬ Even ((history.toFinset.filter (fun x => r ≤ x)).card) then
      (((history.toFinset.filter (fun x => r ≤ x)).prod id : ℕ) : ℝ) *
        (r : ℝ) ^ 2
    else 0)

def historyOddSquareCeiling (history : List ℕ) : ℝ :=
  (historyOddSquareTerms history).foldr max 0

private theorem le_foldr_max_of_mem (xs : List ℝ) (x : ℝ)
    (hx : x ∈ xs) : x ≤ xs.foldr max 0 := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with heq | htail
      · subst x
        simp only [List.foldr_cons]
        exact le_max_left _ _
      · simp only [List.foldr_cons]
        exact (ih htail).trans (le_max_right _ _)

private theorem foldr_max_lt_of_all (xs : List ℝ) (R : ℝ)
    (hzero : (0 : ℝ) < R) (hall : ∀ x ∈ xs, x < R) :
    xs.foldr max 0 < R := by
  induction xs with
  | nil => simpa using hzero
  | cons x ys ih =>
      simp only [List.foldr_cons]
      apply max_lt
      · exact hall x (by simp)
      · apply ih
        intro y hy
        exact hall y (by simp [hy])

/-- A strict bound on the finite historical odd-square ceiling implies
every inherited Rosser test at the ACTUAL chosen frozen level. -/
theorem upper_history_of_ceiling_lt (history : List ℕ) (R : ℝ)
    (hmargin : historyOddSquareCeiling history < R) :
    LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R history.toFinset := by
  intro r hr hodd
  let f : ℕ → ℝ := fun x =>
    if ¬ Even ((history.toFinset.filter (fun y => x ≤ y)).card) then
      (((history.toFinset.filter (fun y => x ≤ y)).prod id : ℕ) : ℝ) *
        (x : ℝ) ^ 2
    else 0
  have hmem : f r ∈ historyOddSquareTerms history := by
    change f r ∈ history.map f
    exact List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr, rfl⟩
  have hle : f r ≤ historyOddSquareCeiling history :=
    le_foldr_max_of_mem (historyOddSquareTerms history) (f r) hmem
  simpa [f, hodd] using lt_of_le_of_lt hle hmargin

/-- The ceiling is an exact finite restatement of all inherited
upper-odd history tests when R is positive. This does not say any
original87 historical state passes its NEW frozen level. -/
theorem upper_history_iff_ceiling_lt (history : List ℕ) (R : ℝ)
    (hR : 0 < R) :
    LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R history.toFinset ↔
      historyOddSquareCeiling history < R := by
  constructor
  · intro hu
    unfold historyOddSquareCeiling
    apply foldr_max_lt_of_all
    · exact hR
    · intro x hx
      unfold historyOddSquareTerms at hx
      rcases List.mem_map.mp hx with ⟨r, hr, rfl⟩
      by_cases hodd :
          ¬ Even ((history.toFinset.filter (fun y => r ≤ y)).card)
      · simpa [hodd] using hu r (List.mem_toFinset.mpr hr) hodd
      · simpa [hodd] using hR
  · exact upper_history_of_ceiling_lt history R

/-- Actual rank-nine inherited rejected occurrences vanish, as a
LIST, whenever the eighth history ceiling is strictly below the
genuine frozen level. Sign, masses and Euler suffix are untouched. -/
theorem actual_inherited_nil_of_history_ceiling
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool)
    (hmargin : historyOddSquareCeiling s.selectedPrefix <
      actualFrozenPost8Level n e q om N c s useParent) :
    rankNineInheritedAt n e q om N c s useParent = [] := by
  let R := actualFrozenPost8Level n e q om N c s useParent
  have hgood :
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
        R s.selectedPrefix.toFinset :=
    upper_history_of_ceiling_lt s.selectedPrefix R hmargin
  have hno : ∀ a : FirstExitRejectedAttempt ℕ,
      a ∉ rankNineInheritedAt n e q om N c s useParent := by
    intro a ha
    have hm := ha
    unfold rankNineInheritedAt at hm
    obtain ⟨hsource, htag⟩ := List.mem_filter.mp hm
    have hmode : inheritedMode R a := of_decide_eq_true htag
    have hroot :=
      (actual_rankNine_root_and_three_modes
        delta n e q om N cap w z c s hs useParent a hsource).1
    have hown :
        LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
          R a.older.toFinset := by
      simpa only [hroot] using hgood
    exact hmode.2 hown
  cases hlist : rankNineInheritedAt n e q om N c s useParent with
  | nil => rfl
  | cons a tail =>
      have ha : a ∈ rankNineInheritedAt n e q om N c s useParent := by
        rw [hlist]
        simp
      exact (hno a ha).elim

theorem actual_inherited_cost_zero_of_history_ceiling
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool)
    (hmargin : historyOddSquareCeiling s.selectedPrefix <
      actualFrozenPost8Level n e q om N c s useParent) :
    rankNineInheritedReciprocalCost n e q om N c s useParent = 0 := by
  unfold rankNineInheritedReciprocalCost
  rw [actual_inherited_nil_of_history_ceiling
    delta n e q om N cap w z c s hs useParent hmargin]
  simp

theorem actual_inherited_signed_zero_of_history_ceiling
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool)
    (hmargin : historyOddSquareCeiling s.selectedPrefix <
      actualFrozenPost8Level n e q om N c s useParent) :
    ((rankNineInheritedAt n e q om N c s useParent).map
      (FirstExitRejectedAttempt.value halfProductDensity)).sum = 0 := by
  rw [actual_inherited_nil_of_history_ceiling
    delta n e q om N cap w z c s hs useParent hmargin]
  simp

/-- Risk is determined by the ACTUAL history and the smaller of the
two real freeze levels; it is only a support test, not a changed policy. -/
def rankNineHistoryRisk
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) : Prop :=
  ¬ (historyOddSquareCeiling s.selectedPrefix <
    min (actualFrozenPost8Level n e q om N c s true)
        (actualFrozenPost8Level n e q om N c s false))

/-- Original owner/trim eighth states, filtered by the finite history
risk predicate only; all surviving states retain occurrence order. -/
def ownedRankNineRiskStates
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell) :
    List (FirstExitDepthState ℕ) :=
  (states (width r) n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c).filter
    (fun s => decide (rankNineHistoryRisk n e q om N c s))

private theorem list_sum_filter_of_zero {α : Type*}
    (xs : List α) (f : α → ℝ) (P : α → Prop)
    [DecidablePred P]
    (hzero : ∀ x ∈ xs, ¬ P x → f x = 0) :
    (xs.map f).sum =
      ((xs.filter (fun x => decide (P x))).map f).sum := by
  induction xs with
  | nil => simp
  | cons x ys ih =>
      have htail : ∀ y ∈ ys, ¬ P y → f y = 0 := by
        intro y hy hnot
        exact hzero y (by simp [hy]) hnot
      by_cases hp : P x
      · simp [hp, ih htail]
      · have hx : f x = 0 := hzero x (by simp) hp
        simp [hp, hx, ih htail]

/-- UNCONDITIONAL exact reduction of the physical reciprocal invoice
to only risky eighth states, independently for each actual policy.
No false claim that this remaining risk invoice is small. -/
theorem owned_inherited_cost_eq_risk_support
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (useParent : Bool) :
    ownedRankNineInheritedCost r n e q om N cap w z c useParent =
      ((ownedRankNineRiskStates r n e q om N cap w z c).map
        (fun s => rankNineInheritedReciprocalCost
          n e q om N c s useParent)).sum := by
  unfold ownedRankNineInheritedCost ownedRankNineRiskStates
  apply list_sum_filter_of_zero
  intro s hs hsafe
  have hmin : historyOddSquareCeiling s.selectedPrefix <
      min (actualFrozenPost8Level n e q om N c s true)
          (actualFrozenPost8Level n e q om N c s false) := by
    unfold rankNineHistoryRisk at hsafe
    exact not_not.mp hsafe
  cases useParent with
  | false =>
      apply actual_inherited_cost_zero_of_history_ceiling
        (width r) n e q om N cap w z c s hs false
      exact lt_of_lt_of_le hmin (min_le_right _ _)
  | true =>
      apply actual_inherited_cost_zero_of_history_ceiling
        (width r) n e q om N cap w z c s hs true
      exact lt_of_lt_of_le hmin (min_le_left _ _)

/-- The signed original physical occurrence sum has the SAME exact
risk support. This is not yet the arithmetic full-q signed gain. -/
theorem owned_inherited_signed_eq_risk_support
    (r n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (useParent : Bool) :
    ownedRankNineInheritedSigned r n e q om N cap w z c useParent =
      ((ownedRankNineRiskStates r n e q om N cap w z c).map
        (fun s => ((rankNineInheritedAt n e q om N c s useParent).map
          (FirstExitRejectedAttempt.value halfProductDensity)).sum)).sum := by
  unfold ownedRankNineInheritedSigned ownedRankNineRiskStates
  apply list_sum_filter_of_zero
  intro s hs hsafe
  have hmin : historyOddSquareCeiling s.selectedPrefix <
      min (actualFrozenPost8Level n e q om N c s true)
          (actualFrozenPost8Level n e q om N c s false) := by
    unfold rankNineHistoryRisk at hsafe
    exact not_not.mp hsafe
  cases useParent with
  | false =>
      apply actual_inherited_signed_zero_of_history_ceiling
        (width r) n e q om N cap w z c s hs false
      exact lt_of_lt_of_le hmin (min_le_right _ _)
  | true =>
      apply actual_inherited_signed_zero_of_history_ceiling
        (width r) n e q om N cap w z c s hs true
      exact lt_of_lt_of_le hmin (min_le_left _ _)

end
end ImbalancedChen.P4AOriginalFull87RankNineHistoryRisk
