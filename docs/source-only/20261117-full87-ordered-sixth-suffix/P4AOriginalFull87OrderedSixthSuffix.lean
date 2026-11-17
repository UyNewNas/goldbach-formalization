import ImbalancedChen.P4AOriginalFull87ActualSixthSuffix
import ImbalancedChen.RoughPrimeUniverse
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A missing property of the ORIGINAL fifth/sixth event population is
the ORDER of its retained sixth-prime carrier relative to the actual
selected history. Mere membership in roughPrimeUniverse loses this
information. The universe is sorted in strictly decreasing order, and
the event producer scans its original tail. We establish the stronger
combined-history ordered Sublist invariant for BOTH original event
constructors. The appended suffix is never an invented or resorted
source.

The new arithmetic consequence is
  p ^ selected.length <= selected.prod
for every genuine fifth-exclusive sixth candidate p. In particular,
when selected.length=5,
  ((p::selected).prod)^5 <= selected.prod^6.
This does NOT establish a global N^(3/5) modulus level, an estimate
for the surviving signed high-q tail, or a density reserve.
-/

namespace ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
noncomputable section
open scoped Classical BigOperators
open P4AOriginalFull87FirstFifthStoppedEvents
  (FifthStoppedEvent firstFifthEvents)
open P4AOriginalFull87FifthSixthStoppedEvents
  (FifthSixthStoppedEvent)
open P4AOriginalFull87SixthBothInvoice
  (fifthSixthWithoutBoth actualFifthSixthWithoutBoth)
open P4AOriginalFull87RankFourStoppedLocalization
  (sharedRankFour)
open P4AOriginalFull87ActualSixthSuffix (eventSixthSuffix)
open P1Pair12RetainedSignedSource (attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- The selected prefix belonging to the original event (not a
substitute parent or an unordered prime set). -/
def eventSelected {α : Type*} : FifthSixthStoppedEvent α → List α
  | .fifthExclusive ev => ev.selectedAfter
  | .sixthFromBoth _ ev => ev.selectedAfter

/-- Skipping one query leaves the earlier selected history fixed.
This proof does not use Nodup or erase duplicate event occurrences. -/
private theorem prefix_skip_sublist {α : Type*}
    (prefix : List α) (p : α) (tail : List α) :
    prefix ++ tail <+ prefix ++ p :: tail := by
  induction prefix with
  | nil =>
      simpa using List.sublist_cons_self p tail
  | cons a rest ih =>
      simpa only [List.cons_append] using (List.Sublist.cons a ih)

/-- All literal firstFifthEvents occurrences retain the *combined*
selected history and post-query suffix as an ordered sublist of their
input. The child history is (p::pre), so its reverse places the newly
chosen prime AFTER the prior selected history, as required. -/
private theorem first_fifth_joined_history_sublist {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ ev ∈ firstFifthEvents R S h T pre positive mass remaining,
      ev.selectedAfter.reverse ++ ev.remainingAfter <+
        pre.reverse ++ remaining := by
  induction remaining with
  | nil =>
      intro ev hev
      simp [firstFifthEvents] at hev
  | cons p ps ih =>
      intro ev hev
      have hskip :
          pre.reverse ++ ps <+ pre.reverse ++ p :: ps :=
        prefix_skip_sublist pre.reverse p ps
      have htake :
          (p :: pre).reverse ++ ps <+
            pre.reverse ++ p :: ps := by
        simpa [List.reverse_cons, List.append_assoc] using
          (List.Sublist.refl (pre.reverse ++ p :: ps))
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [firstFifthEvents, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact htake
          · exact (ih ev htail).trans hskip
        · simp [firstFifthEvents, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact htake
          · exact (ih ev htail).trans hskip
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [firstFifthEvents, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            exact htake
          · exact (ih ev htail).trans hskip
        · have htail :
            ev ∈ firstFifthEvents R S h T pre positive mass ps := by
              simpa [firstFifthEvents, hr, hs] using hev
          exact (ih ev htail).trans hskip

/-- The SAME sixth-BOTH filtered producer, without replacing it,
retains the concatenation of actual selected history and suffix.
For a sixthFromBoth event we use its genuine fifth-selected ancestor
only to recurse; the selected list returned is the inner sixth event. -/
private theorem fifth_sixth_joined_history_sublist {α : Type*}
    (R S : Bool → List α → Bool) (h : α → ℝ)
    (T : Bool → List α → ℝ)
    (pre : List α) (positive : Bool) (mass : ℝ)
    (remaining : List α) :
    ∀ ev ∈ fifthSixthWithoutBoth R S h T pre positive mass remaining,
      (eventSelected ev).reverse ++ eventSixthSuffix ev <+
        pre.reverse ++ remaining := by
  induction remaining with
  | nil =>
      intro ev hev
      simp [fifthSixthWithoutBoth] at hev
  | cons p ps ih =>
      intro ev hev
      have hskip :
          pre.reverse ++ ps <+ pre.reverse ++ p :: ps :=
        prefix_skip_sublist pre.reverse p ps
      have htake :
          (p :: pre).reverse ++ ps <+
            pre.reverse ++ p :: ps := by
        simpa [List.reverse_cons, List.append_assoc] using
          (List.Sublist.refl (pre.reverse ++ p :: ps))
      by_cases hr : R (!positive) (p :: pre) = true
      · by_cases hs : S (!positive) (p :: pre) = true
        · have hsplit : ev ∈
              (((firstFifthEvents R S h T (p :: pre) (!positive)
                (mass * h p) ps).filter
                (fun inner => decide
                  (inner.kind ≠
                    P4AOriginalFull87FirstFifthStoppedEvents.FifthAdmissionClass.both))).map
                (FifthSixthStoppedEvent.sixthFromBoth (p :: pre))) ++
              fifthSixthWithoutBoth R S h T pre positive mass ps := by
            simpa [fifthSixthWithoutBoth, hr, hs] using hev
          rcases List.mem_append.mp hsplit with hinner | htail
          · obtain ⟨inner, hfiltered, rfl⟩ := List.mem_map.mp hinner
            have hmem : inner ∈ firstFifthEvents R S h T
                (p :: pre) (!positive) (mass * h p) ps :=
              (List.mem_filter.mp hfiltered).1
            have hjoined := first_fifth_joined_history_sublist
              R S h T (p :: pre) (!positive) (mass * h p)
              ps inner hmem
            simpa [eventSelected, eventSixthSuffix,
              List.reverse_cons, List.append_assoc] using hjoined
          · exact (ih ev htail).trans hskip
        · simp [fifthSixthWithoutBoth, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            simpa [eventSelected, eventSixthSuffix] using htake
          · exact (ih ev htail).trans hskip
      · by_cases hs : S (!positive) (p :: pre) = true
        · simp [fifthSixthWithoutBoth, hr, hs] at hev
          rcases hev with heq | htail
          · subst ev
            simpa [eventSelected, eventSixthSuffix] using htake
          · exact (ih ev htail).trans hskip
        · have htail :
            ev ∈ fifthSixthWithoutBoth R S h T
              pre positive mass ps := by
              simpa [fifthSixthWithoutBoth, hr, hs] using hev
          exact (ih ev htail).trans hskip

/-- Full-87 actual event source provenance, stronger than separate
suffix membership: selected.reverse ++ suffix is a SUBLIST of exactly
the original strictly decreasing roughPrimeUniverse. -/
theorem actual_event_joined_history_original_rough
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth
      delta n e q om N cap w L X F state) :
    (eventSelected ev).reverse ++ eventSixthSuffix ev <+
      roughPrimeUniverse N cap w z := by
  let R := P4AOriginalFull87CompleteSixthDispatch.policy e q om (N : ℝ)
  let S := P4AOriginalFull87LicensedSixthPolicy.policy
    delta n e q om (N : ℝ)
  let T := attachedLeafTest N cap 1 w L (highQTest X F)
  have hjoined :
      (eventSelected ev).reverse ++ eventSixthSuffix ev <+
        state.selectedPrefix.reverse ++ state.remaining :=
    fifth_sixth_joined_history_sublist R S
      (fun _ : ℕ => (1 : ℝ)) T
      state.selectedPrefix state.positive state.mass state.remaining
      ev (by simpa only [actualFifthSixthWithoutBoth] using hev)
  have hfront :
      state.selectedPrefix.reverse ++ state.remaining <+
        roughPrimeUniverse N cap w z :=
    firstExitDepthFrontier_selected_remaining_sublist 4 R
      (fun _ : ℕ => (1 : ℝ)) []
      (roughPrimeUniverse N cap w z) true 1 state
      (by simpa only [sharedRankFour] using hstate)
  exact hjoined.trans hfront

/-- Any item of the left side of a Pairwise concatenation precedes
every item in its right side. Unlike set membership, this uses order. -/
private theorem pairwise_append_cross {α : Type*} (r : α → α → Prop)
    (xs ys : List α) (h : (xs ++ ys).Pairwise r)
    (a : α) (ha : a ∈ xs) (b : α) (hb : b ∈ ys) :
    r a b := by
  induction xs with
  | nil => simp at ha
  | cons x rest ih =>
      have hsplit := List.pairwise_cons.mp h
      rcases List.mem_cons.mp ha with heq | htail
      · subst a
        exact hsplit.1 b (List.mem_append.mpr (Or.inr hb))
      · exact ih hsplit.2 htail hb

/-- In every REAL fifth/sixth event, every unprocessed prime is
strictly smaller than EVERY previously selected prime. This is a
nontrivial consequence of the combined-history invariant and the
original decreasing scan, not of rough-universe membership alone. -/
theorem actual_event_suffix_lt_every_selected
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (ev : FifthSixthStoppedEvent ℕ)
    (hev : ev ∈ actualFifthSixthWithoutBoth
      delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ eventSixthSuffix ev)
    (r : ℕ) (hr : r ∈ eventSelected ev) :
    p < r := by
  have hjoined := actual_event_joined_history_original_rough
    delta n e q om N cap w z L X F state hstate ev hev
  have hpair :
      ((eventSelected ev).reverse ++ eventSixthSuffix ev).Pairwise
        (· > ·) :=
    (roughPrimeUniverse_pairwise_gt N cap w z).sublist hjoined
  exact pairwise_append_cross (· > ·)
    (eventSelected ev).reverse (eventSixthSuffix ev) hpair
    r (by simpa using hr) p hp

/-- Elementary integer product inequality preserving occurrences:
if an additional selected prime is at most each existing factor,
then its length-th power is bounded by their actual product. -/
private theorem pow_length_le_prod {p : ℕ} (xs : List ℕ)
    (h : ∀ q ∈ xs, p ≤ q) :
    p ^ xs.length ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      have ha : p ≤ a := h a (by simp)
      have hrest : ∀ q ∈ as, p ≤ q := by
        intro q hq
        exact h q (by simp [hq])
      calc
        p ^ (a :: as).length = p * p ^ as.length := by
          simp [pow_succ, Nat.mul_comm]
        _ ≤ a * as.prod := Nat.mul_le_mul ha (ih hrest)
        _ = (a :: as).prod := rfl

/-- NEW quantitative order saving for every actual FIFTH-EXCLUSIVE
event's unprocessed sixth candidate. This was not present in the
old suffix-only membership proof. The rank-five value is obtained
without any new prime distribution or fifth-gate assumption. -/
theorem actual_fifth_exclusive_sixth_power_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth
        delta n e q om N cap w L X F state)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    p ^ fifth.selectedAfter.length ≤ fifth.selectedAfter.prod := by
  apply pow_length_le_prod
  intro r hr
  exact Nat.le_of_lt (actual_event_suffix_lt_every_selected
    delta n e q om N cap w z L X F state hstate
    (.fifthExclusive fifth) hfifth p hp r hr)

/-- Hence the COMPLETE sixth rough modulus has its fifth power
bounded by the sixth power of the fifth history whenever that
history actually has five factors.  This shrinks the old naive z
cutoff but does not itself reach the required uniform PP exponent. -/
theorem actual_fifth_exclusive_sixth_modulus_power_bound
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (state : FirstExitDepthState ℕ)
    (hstate : state ∈ sharedRankFour e q om N cap w z)
    (fifth : FifthStoppedEvent ℕ)
    (hfifth : FifthSixthStoppedEvent.fifthExclusive fifth ∈
      actualFifthSixthWithoutBoth
        delta n e q om N cap w L X F state)
    (hlen : fifth.selectedAfter.length = 5)
    (p : ℕ) (hp : p ∈ fifth.remainingAfter) :
    ((p :: fifth.selectedAfter).prod) ^ 5 ≤
      fifth.selectedAfter.prod ^ 6 := by
  have hpPow := actual_fifth_exclusive_sixth_power_bound
    delta n e q om N cap w z L X F
    state hstate fifth hfifth p hp
  rw [hlen] at hpPow
  calc
    ((p :: fifth.selectedAfter).prod) ^ 5 =
        p ^ 5 * fifth.selectedAfter.prod ^ 5 := by
          simp [List.prod_cons, mul_pow]
    _ ≤ fifth.selectedAfter.prod * fifth.selectedAfter.prod ^ 5 :=
      Nat.mul_le_mul_right _ hpPow
    _ = fifth.selectedAfter.prod ^ 6 := by
      simp [pow_succ, Nat.mul_comm]

end
end ImbalancedChen.P4AOriginalFull87OrderedSixthSuffix
