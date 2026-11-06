import ImbalancedChen.P4AOriginalFull87CorrectionRankTerminal
import ImbalancedChen.P4AOriginalFull87RankNineInheritedSplit
import ImbalancedChen.P4AOriginalFull87PhysicalFailedWeights
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT.

P1.4: isolate the actual rank-nine inherited-square obstruction on the
SAME genuine original87 eighth state, with its original older word,
physical g_N mass, rejected prime and unprocessed Euler suffix.

Unlike later exits, rank nine need not pass the inherited square tests
at the newly frozen level. The three tests below are PRIORITIZED into
mutually exclusive total / inherited / new-minimum modes; neither
geometric measure zero nor a zero signed invoice is assumed.

The inherited invoice is a finite reciprocal-prime-weighted ABSOLUTE
sum. It has NOT been bounded by an o(1) analytic term or spent against
either reserve. All statements are manuscript-internal candidates.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNinePhysicalInherited
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)
open P4AOriginalFull87Post8GuardExtraction (actualFrozenPost8Level)
open P4AOriginalFull87RankNineInheritedSplit
  (rank_nine_upper_rejected_iff_three_modes)
open P4AOriginalFull87FailedAttempts
  (FirstExitRejectedAttempt firstExitRejectedAttempts
    failed_attempt_mem_has_failed_policy
    owned87_failed_attempt_actual_source)
open P4AOriginalFull87SignedDeletionLedger
  (physicalFailedAt physical_failed_has_unit_key)
open P4AOriginalFull87CorrectionRankTerminal
  (rankNinePhysicalFailedAt rankNineSigned
    rankNinePhysicalFailedAt_actual_rank)
open P4AOriginalFull87PhysicalFailedWeights
  (failed_attempt_exact_selected_mass
    owned87_actual_physical_failed_occurrence)

/-- A genuine rank-nine physical occurrence has NO intervening chosen
prime. Thus its older word and its incoming mass are EXACTLY those of
the original licensed eighth state. Its actual failed policy has the
three exhaustive rank-nine causes, without silently assuming inherited
historical admission at the new level. -/
theorem actual_rankNine_root_and_three_modes
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ rankNinePhysicalFailedAt n e q om N c s useParent) :
    a.older = s.selectedPrefix ∧
      a.positive = true ∧
      a.mass = s.mass * (s.selectedPrefix.map halfProductDensity).prod ∧
      (actualFrozenPost8Level n e q om N c s useParent ≤
          (((a.rejected :: a.older).prod : ℕ) : ℝ) ∨
        ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
          (actualFrozenPost8Level n e q om N c s useParent)
          a.older.toFinset ∨
        actualFrozenPost8Level n e q om N c s useParent ≤
          (((a.rejected :: a.older).prod : ℕ) : ℝ) *
            (a.rejected : ℝ) ^ 2) := by
  have hmem := ha
  unfold rankNinePhysicalFailedAt at hmem
  obtain ⟨hphysical, _⟩ := List.mem_filter.mp hmem
  have hfirst := hphysical
  change a ∈ firstExitRejectedAttempts
    (ordinaryParityRosserPolicy false
      (actualFrozenPost8Level n e q om N c s useParent))
    halfProductDensity s.selectedPrefix s.positive
    (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
    s.remaining at hfirst
  obtain ⟨before, chosen, hrem, _, holder, hmass⟩ :=
    failed_attempt_exact_selected_mass
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      halfProductDensity s.selectedPrefix s.remaining s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
      a hfirst
  obtain ⟨hprelen, hpreorder, _, hboundary, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  have hlen : a.older.length = 8 :=
    rankNinePhysicalFailedAt_actual_rank
      delta n e q om N cap w z c s hs useParent a ha
  have hlenEq := congrArg List.length holder
  simp only [List.length_append, List.length_reverse] at hlenEq
  have hchosenZero : chosen.length = 0 := by omega
  have hchosen : chosen = [] := List.length_eq_zero_iff.mp hchosenZero
  have hroot : a.older = s.selectedPrefix := by
    simpa [hchosen] using holder
  have hmassRoot :
      a.mass = s.mass * (s.selectedPrefix.map halfProductDensity).prod := by
    simpa [hchosen] using hmass
  obtain ⟨b, hb, _, _, _, hpositiveKey⟩ :=
    physical_failed_has_unit_key n e q om N c s useParent a hphysical
  obtain ⟨_, _, _, _, _, _, _, hpositiveB, _, _, _⟩ :=
    owned87_failed_attempt_actual_source
      delta n e q om N cap w z c s hs useParent b hb
  have hpositive : a.positive = true :=
    hpositiveKey.symm.trans hpositiveB
  have hfailed :=
    failed_attempt_mem_has_failed_policy
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      halfProductDensity s.selectedPrefix s.remaining s.positive
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod)
      a hfirst
  have hfailedOdd :
      ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        false (a.rejected :: a.older) = false := by
    simpa [hpositive] using hfailed
  have hnodup : a.older.Nodup := by
    rw [hroot]
    exact hpreorder.nodup
  have hpMem : a.rejected ∈ s.remaining := by
    rw [hrem]
    simp
  have hpmin : ∀ r ∈ a.older, a.rejected < r := by
    intro r hr
    exact hboundary a.rejected hpMem r (by simpa [hroot] using hr)
  have hthree :=
    (rank_nine_upper_rejected_iff_three_modes
      (actualFrozenPost8Level n e q om N c s useParent)
      a.older a.rejected hlen hnodup hpmin).mp hfailedOdd
  exact ⟨hroot, hpositive, hmassRoot, hthree⟩

/-- The rank-nine physical value has exactly one incoming eighth-prefix
g_N product and one rejected-prime density; no post-eight successful
prime has been inserted. The even target gives the literal 1/(p-1).
The suffix Euler product is NOT silently bounded or discarded. -/
theorem actual_rankNine_reciprocal_value
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hEven : 2 ∣ N) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ rankNinePhysicalFailedAt n e q om N c s useParent) :
    a.value halfProductDensity =
      (s.mass * (s.selectedPrefix.map halfProductDensity).prod) *
        (1 / ((a.rejected : ℝ) - 1)) *
          (a.smaller.map (fun x => 1 - halfProductDensity x)).prod := by
  obtain ⟨_, hpos, hmass, _⟩ :=
    actual_rankNine_root_and_three_modes
      delta n e q om N cap w z c s hs useParent a ha
  have hm := ha
  unfold rankNinePhysicalFailedAt at hm
  have hphysical := (List.mem_filter.mp hm).1
  have hden :
      halfProductDensity a.rejected =
        1 / ((a.rejected : ℝ) - 1) := by
    obtain ⟨_, _, _, _, _, _, _, hdensity, _, _, _⟩ :=
      owned87_actual_physical_failed_occurrence
        delta n e q om N cap hEven w z c s hs useParent a hphysical
    exact hdensity
  simp [FirstExitRejectedAttempt.value, hpos, hmass, hden,
    signedTreeCoefficient]

/-- These three conditions are mutually exclusive by PRIORITY. They
label the actual rejection, and are NOT additional retention policies. -/
def totalMode (R : ℝ) (a : FirstExitRejectedAttempt ℕ) : Prop :=
  R ≤ (((a.rejected :: a.older).prod : ℕ) : ℝ)

def inheritedMode (R : ℝ) (a : FirstExitRejectedAttempt ℕ) : Prop :=
  ¬ totalMode R a ∧
    ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R a.older.toFinset

def newSquareMode (R : ℝ) (a : FirstExitRejectedAttempt ℕ) : Prop :=
  ¬ totalMode R a ∧
    LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R a.older.toFinset

def rankNineTotalAt
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    List (FirstExitRejectedAttempt ℕ) :=
  (rankNinePhysicalFailedAt n e q om N c s useParent).filter
    (fun a => decide (totalMode
      (actualFrozenPost8Level n e q om N c s useParent) a))

def rankNineInheritedAt
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    List (FirstExitRejectedAttempt ℕ) :=
  (rankNinePhysicalFailedAt n e q om N c s useParent).filter
    (fun a => decide (inheritedMode
      (actualFrozenPost8Level n e q om N c s useParent) a))

def rankNineNewSquareAt
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    List (FirstExitRejectedAttempt ℕ) :=
  (rankNinePhysicalFailedAt n e q om N c s useParent).filter
    (fun a => decide (newSquareMode
      (actualFrozenPost8Level n e q om N c s useParent) a))

/-- Pure list arithmetic: prioritized tags partition every ORIGINAL
occurrence exactly once, including duplicates and both signs. -/
private theorem three_mode_sum
    (R : ℝ) (xs : List (FirstExitRejectedAttempt ℕ))
    (f : FirstExitRejectedAttempt ℕ → ℝ) :
    (xs.map f).sum =
      ((xs.filter (fun a => decide (totalMode R a))).map f).sum +
      ((xs.filter (fun a => decide (inheritedMode R a))).map f).sum +
      ((xs.filter (fun a => decide (newSquareMode R a))).map f).sum := by
  classical
  induction xs with
  | nil => simp
  | cons a xs ih =>
      by_cases ht : totalMode R a
      · have hi : ¬ inheritedMode R a := fun h => h.1 ht
        have hn : ¬ newSquareMode R a := fun h => h.1 ht
        simp [ht, hi, hn, ih]
        ring
      · by_cases hu :
          LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R a.older.toFinset
        · have hi : ¬ inheritedMode R a := fun h => h.2 hu
          have hn : newSquareMode R a := ⟨ht, hu⟩
          simp [ht, hi, hn, ih]
          ring
        · have hi : inheritedMode R a := ⟨ht, hu⟩
          have hn : ¬ newSquareMode R a := fun h => hu h.2
          simp [ht, hi, hn, ih]
          ring

/-- Actual rank-nine physical correction: exact mutually exclusive
total / inherited / new-square signed split at ONE genuine frozen level.
This is NOT a cap-monotonicity comparison. -/
theorem rankNine_signed_eq_three_prioritized_modes
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) :
    rankNineSigned n e q om N c s useParent =
      ((rankNineTotalAt n e q om N c s useParent).map
        (FirstExitRejectedAttempt.value halfProductDensity)).sum +
      ((rankNineInheritedAt n e q om N c s useParent).map
        (FirstExitRejectedAttempt.value halfProductDensity)).sum +
      ((rankNineNewSquareAt n e q om N c s useParent).map
        (FirstExitRejectedAttempt.value halfProductDensity)).sum := by
  unfold rankNineSigned rankNineTotalAt rankNineInheritedAt rankNineNewSquareAt
  exact three_mode_sum
    (actualFrozenPost8Level n e q om N c s useParent)
    (rankNinePhysicalFailedAt n e q om N c s useParent)
    (FirstExitRejectedAttempt.value halfProductDensity)

/-- A new-square-tagged ACTUAL failed occurrence has a genuine last
minimum-prime square failure, once the total and inherited tests have
both been ruled out at THAT original parent/cap level. -/
theorem actual_rankNine_new_tag_forces_minimum_square
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ rankNineNewSquareAt n e q om N c s useParent) :
    actualFrozenPost8Level n e q om N c s useParent ≤
      (((a.rejected :: a.older).prod : ℕ) : ℝ) *
        (a.rejected : ℝ) ^ 2 := by
  have hm := ha
  unfold rankNineNewSquareAt at hm
  obtain ⟨hsource, htag⟩ := List.mem_filter.mp hm
  have hmode : newSquareMode
      (actualFrozenPost8Level n e q om N c s useParent) a :=
    of_decide_eq_true htag
  have hcases :=
    (actual_rankNine_root_and_three_modes
      delta n e q om N cap w z c s hs useParent a hsource).2.2.2
  rcases hcases with htotal | hinherited | hnew
  · exact False.elim (hmode.1 htotal)
  · exact False.elim (hinherited hmode.2)
  · exact hnew

/-- A genuine inherited-square mode has a concrete historical r:
the full odd suffix product * r^2 exceeds the same frozen level.
This is an arithmetic obstruction, NOT a zero-measure exception. -/
theorem actual_rankNine_inherited_has_historical_witness
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) (a : FirstExitRejectedAttempt ℕ)
    (ha : a ∈ rankNineInheritedAt n e q om N c s useParent) :
    ∃ r ∈ s.selectedPrefix.toFinset,
      ¬ Even ((s.selectedPrefix.toFinset.filter (fun x => r ≤ x)).card) ∧
      actualFrozenPost8Level n e q om N c s useParent ≤
        (((s.selectedPrefix.toFinset.filter
          (fun x => r ≤ x)).prod id : ℕ) : ℝ) * (r : ℝ) ^ 2 := by
  have hm := ha
  unfold rankNineInheritedAt at hm
  obtain ⟨hsource, htag⟩ := List.mem_filter.mp hm
  have hmode : inheritedMode
      (actualFrozenPost8Level n e q om N c s useParent) a :=
    of_decide_eq_true htag
  have hroot :=
    (actual_rankNine_root_and_three_modes
      delta n e q om N cap w z c s hs useParent a hsource).1
  have hbad := hmode.2
  rw [hroot] at hbad
  unfold LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet at hbad
  push_neg at hbad
  exact hbad

/-- For the inherited mode, the original physical signed correction
has an explicit nonzero-capable finite invoice. Its denominator is
the TRUE rejected prime minus one; the TRUE suffix Euler product and
one incoming eighth mass remain attached to the same occurrence. -/
def rankNineInheritedReciprocalCost
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ) (N : ℕ) (c : Cell)
    (s : FirstExitDepthState ℕ) (useParent : Bool) : ℝ :=
  ((rankNineInheritedAt n e q om N c s useParent).map
    (fun a =>
      |(s.mass * (s.selectedPrefix.map halfProductDensity).prod) *
        (1 / ((a.rejected : ℝ) - 1)) *
        (a.smaller.map (fun x => 1 - halfProductDensity x)).prod|)).sum

private theorem list_absolute_invoice {α : Type*}
    (xs : List α) (f b : α → ℝ)
    (h : ∀ a ∈ xs, |f a| ≤ b a) :
    |(xs.map f).sum| ≤ (xs.map b).sum := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have htail : ∀ t ∈ xs, |f t| ≤ b t := by
        intro t ht
        exact h t (by simp [ht])
      have hrest := ih htail
      simp only [List.map_cons, List.sum_cons]
      calc
        |f a + (xs.map f).sum| ≤ |f a| + |(xs.map f).sum| :=
          abs_add_le _ _
        _ ≤ b a + (xs.map b).sum := add_le_add ha hrest

/-- Quantitative but UNPAID rank-nine inherited-square absolute invoice.
All events are the original actual occurrences, no Finset deduplication
or signed cancellation. No claim is made that this cost is o(1). -/
theorem actual_rankNine_inherited_absolute_invoice
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (hEven : 2 ∣ N) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z
      (fun _ : ℕ => (1 : ℝ)) c)
    (useParent : Bool) :
    |((rankNineInheritedAt n e q om N c s useParent).map
        (FirstExitRejectedAttempt.value halfProductDensity)).sum| ≤
      rankNineInheritedReciprocalCost n e q om N c s useParent := by
  unfold rankNineInheritedReciprocalCost
  apply list_absolute_invoice
  intro a ha
  have hsource : a ∈ rankNinePhysicalFailedAt n e q om N c s useParent := by
    have hm := ha
    unfold rankNineInheritedAt at hm
    exact (List.mem_filter.mp hm).1
  rw [actual_rankNine_reciprocal_value
    delta n e q om N cap hEven w z c s hs useParent a hsource]

end
end ImbalancedChen.P4AOriginalFull87RankNinePhysicalInherited
