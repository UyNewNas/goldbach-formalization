import ImbalancedChen.P4AOriginalFull87ActualEighthCarrier
import ImbalancedChen.P4AOriginalFull87Post8GuardExtraction
import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

P1.4: the FIRST odd test after an actual historical eighth prefix.
Unlike a later rank-11-or-higher rejection, rank nine has no previously
successful odd guard at the NEW frozen level. Its full rejection splits
into THREE exact alternatives: total product, an inherited old square,
or the new minimum prime's square. This is an equivalence, not a bound
on the inherited-square alternative. Both actual original87 levels and
the original strict thresholds are retained.

In particular, the theorem does NOT turn a retained terminal leaf
into a rejected branch. The final lemma treats the literal first
remaining candidate when its select branch really fails the policy.
-/

namespace ImbalancedChen.P4AOriginalFull87RankNineInheritedSplit

noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)
open P4AOriginalFull87OwnedEighthSource
  (frontier frontier_sign_mass states_eq_owner_filter)
open P4AOriginalFull87Post8GuardExtraction
  (upper_odd_rejected_iff actualFrozenPost8Level)
open P4AOriginalFull87ActualEighthCarrier
  (owned87_eighth_state_exact_carrier)

/-- For an even-sized set of older primes, insertion of a strictly
smaller prime leaves ALL inherited upper square tests unchanged and
creates exactly one new, odd-cardinality, minimum-prime test.
No old test is presumed true. This is what distinguishes rank nine
from the previously proved two-prime insertion at rank eleven. -/
theorem upper_one_min_even_iff_old_and_new
    (R : ℝ) (s : Finset ℕ) (p : ℕ)
    (heven : Even s.card)
    (hpmin : ∀ r ∈ s, p < r) :
    LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R (insert p s) ↔
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R s ∧
      ((((insert p s).prod id : ℕ) : ℝ) * (p : ℝ) ^ 2 < R) := by
  classical
  have hpnot : p ∉ s := by
    intro hp
    exact (lt_irrefl p) (hpmin p hp)
  have hodd : ¬ Even (insert p s).card := by
    rw [Finset.card_insert_of_not_mem hpnot]
    obtain ⟨k, hk⟩ := heven
    rintro ⟨j, hj⟩
    omega
  have hfilterNew :
      (insert p s).filter (fun r => p ≤ r) = insert p s := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hrs
    · exact le_rfl
    · exact (hpmin r hrs).le
  have hfilterOld (r : ℕ) (hr : r ∈ s) :
      (insert p s).filter (fun x => r ≤ x) =
        s.filter (fun x => r ≤ x) := by
    have hrp : ¬ r ≤ p := not_le_of_gt (hpmin r hr)
    simp [Finset.filter_insert, hrp]
  constructor
  · intro hall
    constructor
    · intro r hr hcard
      have hsame := hfilterOld r hr
      have hbig := hall r (Finset.mem_insert_of_mem hr)
        (by simpa only [hsame] using hcard)
      simpa only [hsame] using hbig
    · have hbig := hall p (by simp)
        (by simpa only [hfilterNew] using hodd)
      simpa only [hfilterNew] using hbig
  · rintro ⟨hold, hnew⟩ r hr hcard
    rcases Finset.mem_insert.mp hr with rfl | hrs
    · simpa only [hfilterNew] using hnew
    · have hsame := hfilterOld r hrs
      have hcardOld : ¬ Even ((s.filter (fun x => r ≤ x)).card) := by
        simpa only [hsame] using hcard
      simpa only [hsame] using hold r hrs hcardOld

/-- The first post-eight odd Rosser attempt has three, and only three,
possible failure modes. Unlike a late odd test, an inherited failure
is NOT forced to be a least-prime-square failure. The old set is
the literal eight-prime history, without sorting or changing weights. -/
theorem rank_nine_upper_rejected_iff_three_modes
    (R : ℝ) (older : List ℕ) (p : ℕ)
    (hlen : older.length = 8) (hnodup : older.Nodup)
    (hpmin : ∀ r ∈ older, p < r) :
    ordinaryParityRosserPolicy false R false (p :: older) = false ↔
      R ≤ (((p :: older).prod : ℕ) : ℝ) ∨
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R older.toFinset ∨
      R ≤ (((p :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 := by
  classical
  have heven : Even older.toFinset.card := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
    decide
  have hsmall : ∀ r ∈ older.toFinset, p < r :=
    fun r hr => hpmin r (List.mem_toFinset.mp hr)
  have hpnot : p ∉ older := by
    intro hp
    exact (lt_irrefl p) (hpmin p hp)
  have hnewNodup : (p :: older).Nodup :=
    List.nodup_cons.mpr ⟨hpnot, hnodup⟩
  have hprod :
      (insert p older.toFinset).prod id = (p :: older).prod := by
    have h := List.prod_toFinset (fun r : ℕ => r) hnewNodup
    simpa only [List.toFinset_cons] using h
  have hsplit :
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R
        (p :: older).toFinset ↔
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R older.toFinset ∧
        (((p :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 < R := by
    simpa only [List.toFinset_cons, hprod] using
      upper_one_min_even_iff_old_and_new R older.toFinset p heven hsmall
  rw [upper_odd_rejected_iff, hsplit]
  simp only [not_and_or, not_lt]

/-- Apply the precise rank-nine split to EVERY actual first-choice
candidate of the original87 eighth-frontier state. An arbitrary terminal
leaf is not used to infer a failure: a failure is tested only for an
actual member of the same residual carrier, at the two existing levels. -/
theorem owned87_actual_rank_nine_rejected_iff
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (p : ℕ) (hp : p ∈ s.remaining) :
    ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        false (p :: s.selectedPrefix) = false ↔
      actualFrozenPost8Level n e q om N c s useParent ≤
        (((p :: s.selectedPrefix).prod : ℕ) : ℝ) ∨
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
          (actualFrozenPost8Level n e q om N c s useParent)
          s.selectedPrefix.toFinset ∨
      actualFrozenPost8Level n e q om N c s useParent ≤
        (((p :: s.selectedPrefix).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 := by
  obtain ⟨hlen, hsorted, _, hboundary, _⟩ :=
    owned87_eighth_state_exact_carrier
      delta n e q om N cap w z c s hs
  exact rank_nine_upper_rejected_iff_three_modes
    _ s.selectedPrefix p hlen hsorted.nodup (hboundary p hp)

/-- The HEAD of the original remaining carrier is an actual rank-nine
selection attempt: when its upper test fails, the genuine first-exit
enumerator has no select subtree at that head. The skip subtree and its
original occurrence multiplicities are left intact. This does not
claim the rejected head was a selected terminal leaf or that a deeper
two-prime rejection has already been extracted. -/
theorem owned87_actual_rank_nine_rejected_head_skips_select
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (p : ℕ) (tail : List ℕ)
    (hhead : s.remaining = p :: tail)
    (hfailed : ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent)
        false (p :: s.selectedPrefix) = false) :
    firstExitRetainedLeaves
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        (fun _ : ℕ => (1 : ℝ)) s.selectedPrefix s.positive s.mass s.remaining =
      firstExitRetainedLeaves
        (ordinaryParityRosserPolicy false
          (actualFrozenPost8Level n e q om N c s useParent))
        (fun _ : ℕ => (1 : ℝ)) s.selectedPrefix s.positive s.mass tail := by
  have hfront : s ∈ frontier n e q om N cap w z := by
    have h := hs
    rw [states_eq_owner_filter] at h
    exact (List.mem_filter.mp h).1
  have hsign : s.positive = true :=
    (frontier_sign_mass n e q om N cap w z s hfront).1
  rw [hhead, hsign]
  simp [firstExitRetainedLeaves, hfailed]

end
end ImbalancedChen.P4AOriginalFull87RankNineInheritedSplit
