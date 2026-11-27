import ImbalancedChen.P1OriginalHistoricalCanonicalOwnerWord
import Mathlib.Data.List.Basic

/-!
Actual first-rejection words are a prefix antichain for the original policy.
The same canonical rough word therefore determines its actual owner uniquely.
No Cartesian atom identification or signed-medium estimate is asserted.
-/
namespace ImbalancedChen.P1OriginalHistoricalOwnerUniqueness
noncomputable section
open Classical

/-- A certificate for the original policy along a selected word, without skips.
The first rejected letter is exactly the last letter of this nonempty word. -/
def RejectsAtLast {α : Type*} (retained : Bool → List α → Bool)
    (pre : List α) (positive : Bool) : List α → Prop
  | [] => False
  | p :: ps => if retained (!positive) (p :: pre) = true then
      RejectsAtLast retained (p :: pre) (!positive) ps else ps = []

theorem rejected_words_prefix_eq {α : Type*} (retained : Bool → List α → Bool)
    (pre : List α) (positive : Bool) (xs ys : List α)
    (hx : RejectsAtLast retained pre positive xs)
    (hy : RejectsAtLast retained pre positive ys) (hprefix : xs.IsPrefix ys) : xs = ys := by
  induction xs generalizing pre positive ys with
  | nil => simp [RejectsAtLast] at hx
  | cons p ps ih =>
    cases ys with
    | nil => simp [RejectsAtLast] at hy
    | cons q qs =>
      obtain ⟨rfl, htail⟩ := List.cons_prefix_cons.mp hprefix
      by_cases hp : retained (!positive) (p :: pre) = true
      · simp only [RejectsAtLast, if_pos hp] at hx hy
        exact congrArg (List.cons p) (ih (p :: pre) (!positive) qs hx hy htail)
      · simp only [RejectsAtLast, if_neg hp] at hx hy
        rw [hx, hy]

/-- The certificate comes from the actual signed-exit recursion, not an
admission or factorability assumption about a replacement family. -/
theorem exit_prefix_word {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (pre carrier : List α) (positive : Bool) (mass : ℝ)
    (state : FirstExitDepthState α)
    (hs : state ∈ p1SignedExitStates retained h pre positive mass carrier) :
    ∃ word : List α, state.selectedPrefix.reverse = pre.reverse ++ word ∧
      RejectsAtLast retained pre positive word := by
  induction carrier generalizing pre positive mass with
  | nil => simp [p1SignedExitStates] at hs
  | cons p ps ih =>
    by_cases hp : retained (!positive) (p :: pre) = true
    · rw [p1SignedExitStates, if_pos hp, List.mem_append] at hs
      rcases hs with hskip | hselect
      · exact ih pre positive mass hskip
      · obtain ⟨word, heq, hw⟩ := ih (p :: pre) (!positive) (mass * h p) hselect
        refine ⟨p :: word, ?_, ?_⟩
        · simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using heq
        · simpa only [RejectsAtLast, if_pos hp] using hw
    · rw [p1SignedExitStates, if_neg hp, List.mem_append] at hs
      rcases hs with hskip | hexit
      · exact ih pre positive mass hskip
      · simp only [List.mem_singleton] at hexit
        subst state
        refine ⟨[p], ?_, ?_⟩
        · simp only [List.reverse_cons]
        · simp only [RejectsAtLast, if_neg hp]

theorem exit_root_rejects_at_last {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) (state : FirstExitDepthState α)
    (hs : state ∈ p1SignedExitStates retained h [] true 1 carrier) :
    RejectsAtLast retained [] true state.selectedPrefix.reverse := by
  obtain ⟨word, heq, hw⟩ := exit_prefix_word retained h [] carrier true 1 state hs
  simp only [List.reverse_nil, List.nil_append] at heq
  rwa [heq]

theorem exit_prefix_eq_of_isPrefix {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) (s t : FirstExitDepthState α)
    (hs : s ∈ p1SignedExitStates retained h [] true 1 carrier)
    (ht : t ∈ p1SignedExitStates retained h [] true 1 carrier)
    (hp : s.selectedPrefix.reverse.IsPrefix t.selectedPrefix.reverse) :
    s.selectedPrefix = t.selectedPrefix := by
  have he := rejected_words_prefix_eq retained [] true _ _
    (exit_root_rejects_at_last retained h carrier s hs)
    (exit_root_rejects_at_last retained h carrier t ht) hp
  simpa only [List.reverse_reverse] using congrArg List.reverse he

/-- Once an actual selected head is fixed in a Nodup carrier, its literal
unprocessed suffix is fixed. This reuses the existing carrier decomposition. -/
theorem exit_remaining_eq_of_prefix_eq {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) (hnd : carrier.Nodup) (s t : FirstExitDepthState α)
    (hs : s ∈ p1SignedExitStates retained h [] true 1 carrier)
    (ht : t ∈ p1SignedExitStates retained h [] true 1 carrier)
    (he : s.selectedPrefix = t.selectedPrefix) : s.remaining = t.remaining := by
  obtain ⟨beforeS, p, parentS, hcS, hpS⟩ :=
    p1_mem_exitStates_carrier_decomposition retained h [] carrier true 1 s hs
  obtain ⟨beforeT, q, parentT, hcT, hpT⟩ :=
    p1_mem_exitStates_carrier_decomposition retained h [] carrier true 1 t ht
  have hpq : p = q := (List.cons.inj (hpS.symm.trans (he.trans hpT))).1
  subst q
  have hn : (beforeS ++ p :: s.remaining).Nodup := by rwa [← hcS]
  obtain ⟨_, hnrest, hbetween⟩ := List.nodup_append.mp hn
  have hfront : p ∉ beforeS := fun hm => hbetween p hm p (List.mem_cons_self ..) rfl
  have htail : p ∉ s.remaining := (List.nodup_cons.mp hnrest).1
  exact ((List.append_cons_inj_of_notMem hfront htail).mp (hcS.symm.trans hcT)).2.2

theorem exit_state_eq_of_prefix_eq {α : Type*} (retained : Bool → List α → Bool)
    (h : α → ℝ) (carrier : List α) (hnd : carrier.Nodup) (s t : FirstExitDepthState α)
    (hs : s ∈ p1SignedExitStates retained h [] true 1 carrier)
    (ht : t ∈ p1SignedExitStates retained h [] true 1 carrier)
    (he : s.selectedPrefix = t.selectedPrefix) : s = t := by
  have hss := p1_mem_exitStates_sign_mass retained h [] carrier true 1 rfl rfl s hs
  have hts := p1_mem_exitStates_sign_mass retained h [] carrier true 1 rfl rfl t ht
  have hp : s.positive = t.positive :=
    hss.1.trans ((congrArg evenListLength he).trans hts.1.symm)
  have hm : s.mass = t.mass :=
    hss.2.trans ((congrArg (fun l : List α => (l.map h).prod) he).trans hts.2.symm)
  exact FirstExitDepthState.ext he hp hm
    (exit_remaining_eq_of_prefix_eq retained h carrier hnd s t hs ht he)

open P1OriginalHistoricalRoughOwnerPartition (Realizes owner owner_spec changedRough fibre fibre_realizes)
open P1OriginalHistoricalCanonicalOwnerWord (realized_canonical_word)

/-- All actual realizing witnesses for the SAME rough b are the SAME
state, including the literal remaining carrier, sign and mass. -/
theorem realizing_state_unique (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (b : ℕ) (s t : FirstExitDepthState ℕ)
    (hs : Realizes old fresh N cap w z s b) (ht : Realizes old fresh N cap w z t b) : s = t := by
  obtain ⟨tailS, heS, _, _⟩ := realized_canonical_word old fresh N cap w z s b hs
  obtain ⟨tailT, heT, _, _⟩ := realized_canonical_word old fresh N cap w z t b ht
  have hpreS : s.selectedPrefix.reverse.IsPrefix b.primeFactorsList.reverse := ⟨tailS, heS.symm⟩
  have hpreT : t.selectedPrefix.reverse.IsPrefix b.primeFactorsList.reverse := ⟨tailT, heT.symm⟩
  let retained := p1CommonAdmissionPolicy (oddFirstExitPolicy old) (oddFirstExitPolicy fresh)
  have hprefix : s.selectedPrefix = t.selectedPrefix := by
    rcases List.prefix_or_prefix_of_prefix hpreS hpreT with hst | hts
    · exact exit_prefix_eq_of_isPrefix retained (fun _ => 1) _ s t hs.1 ht.1 hst
    · exact (exit_prefix_eq_of_isPrefix retained (fun _ => 1) _ t s ht.1 hs.1 hts).symm
  exact exit_state_eq_of_prefix_eq retained (fun _ => 1) (roughPrimeUniverse N cap w z)
    (roughPrimeUniverse_pairwise_gt N cap w z).nodup s t hs.1 ht.1 hprefix

theorem realizes_iff_owner (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (b : ℕ) (hb : b ∈ changedRough old fresh N cap w z) (state : FirstExitDepthState ℕ) :
    Realizes old fresh N cap w z state b ↔ state = owner old fresh N cap w z b := by
  constructor
  · intro hs
    exact realizing_state_unique old fresh N cap w z b state _ hs (owner_spec old fresh N cap w z b hb)
  · intro he
    rw [he]
    exact owner_spec old fresh N cap w z b hb

/-- Fibre membership is its original actual realizing condition, with
no arbitrary witness-choice cut added to that condition. -/
theorem fibre_iff_realizes (old fresh : List ℕ → Bool) (N cap : ℕ) (w z : ℝ)
    (state : FirstExitDepthState ℕ) (b : ℕ) :
    b ∈ fibre old fresh N cap w z state ↔
      b ∈ changedRough old fresh N cap w z ∧ Realizes old fresh N cap w z state b := by
  constructor
  · intro hb
    exact ⟨(Finset.mem_filter.mp hb).1, fibre_realizes old fresh N cap w z state b hb⟩
  · rintro ⟨hb, hs⟩
    exact Finset.mem_filter.mpr ⟨hb,
      realizing_state_unique old fresh N cap w z b _ state (owner_spec old fresh N cap w z b hb) hs⟩

end
end ImbalancedChen.P1OriginalHistoricalOwnerUniqueness
