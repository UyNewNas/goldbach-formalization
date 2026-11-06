import ImbalancedChen.P4AOriginalFull87Post8GuardExtraction
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

P1.4: precise discharge of the inherited-square/total-product
alternatives for an odd Rosser exit TWO positions after a successfully
retained odd prefix at the SAME frozen level.

The prefix at rank eight is historical and must not be passed as such
a successful frozen-level odd prefix. The first subsequent odd test
(rank nine) may still fail on an inherited historical square. For
rank eleven and later, once the preceding post-eight odd prefix was
actually selected, inserting two strictly smaller primes leaves all
its previous square suffixes untouched, introduces one untested
even-cardinality square, and adds exactly the new least-prime odd
square. Its total product is already below the level.

The lemmas use literal UpperAdmissibleSet, literal ordinary policy,
the same actual owned87 state and both existing frozen levels.
They do not assert any exit exists or reconstruct the last-prime
logarithm, and they do not change the original source or terminal test.
-/

namespace ImbalancedChen.P4AOriginalFull87InheritedOddSquares
noncomputable section

open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P4AOriginalFull87Post8GuardExtraction
  (upper_odd_test_iff upper_odd_rejected_iff
   post8OddTrace actualFrozenPost8Level
   owned87_terminal_post8_success_guards)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)

/-- With two new strictly smaller distinct primes, all older suffixes
are literally unchanged. The intermediate prime has an EVEN-length
suffix; the new least prime has the ONLY new odd-square obligation. -/
theorem upper_two_min_insert_iff_last_square
    (R : ℝ) (s : Finset ℕ) (p q : ℕ)
    (hpq : p < q) (hqsmall : ∀ r ∈ s, q < r)
    (hodd : Odd s.card)
    (hprevious : LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R s) :
    LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
      R (insert p (insert q s)) ↔
      ((((insert p (insert q s)).prod id : ℕ) : ℝ) *
        (p : ℝ) ^ 2 < R) := by
  classical
  let t : Finset ℕ := insert p (insert q s)
  have hqnot : q ∉ s := by
    intro h
    exact (lt_irrefl q) (hqsmall q h)
  have hpnot : p ∉ insert q s := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · exact (lt_irrefl p) (hpq.trans (hqsmall p h))
  have hsize : t.card = s.card + 2 := by
    dsimp [t]
    rw [Finset.card_insert_of_not_mem hpnot,
      Finset.card_insert_of_not_mem hqnot]
    omega
  have htodd : ¬ Even t.card := by
    rw [hsize]
    rcases hodd with ⟨k, hk⟩
    rintro ⟨j, hj⟩
    omega
  have hpfilter : t.filter (fun x => p ≤ x) = t := by
    apply Finset.filter_eq_self.mpr
    intro r hr
    simp only [t, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact le_rfl
    rcases hr with rfl | hr
    · exact hpq.le
    · exact (hpq.trans (hqsmall r hr)).le
  have hqfilter : t.filter (fun x => q ≤ x) = insert q s := by
    have htail : s.filter (fun x => q ≤ x) = s :=
      Finset.filter_eq_self.mpr (fun r hr => (hqsmall r hr).le)
    simp [t, Finset.filter_insert, not_le_of_gt hpq, htail]
  have hqeven : Even ((t.filter (fun x => q ≤ x)).card) := by
    rw [hqfilter, Finset.card_insert_of_not_mem hqnot]
    rcases hodd with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have holdfilter (r : ℕ) (hr : r ∈ s) :
      t.filter (fun x => r ≤ x) = s.filter (fun x => r ≤ x) := by
    have hrq : ¬ r ≤ q := not_le_of_gt (hqsmall r hr)
    have hrp : ¬ r ≤ p :=
      not_le_of_gt (hpq.trans (hqsmall r hr))
    simp [t, Finset.filter_insert, hrp, hrq]
  constructor
  · intro hfull
    have htest := hfull p (by simp [t]) htodd
    simpa only [hpfilter] using htest
  · intro hlast
    intro r hr hcard
    by_cases hrp : r = p
    · subst r
      simpa only [hpfilter] using hlast
    by_cases hrq : r = q
    · subst r
      exact (hqeven hcard).elim
    · have hmem : r ∈ s := by
        simpa [t, hrp, hrq] using hr
      have hsame := holdfilter r hmem
      have hcard' :
          ¬ Even ((s.filter (fun x => r ≤ x)).card) := by
        simpa only [hsame] using hcard
      have htest := hprevious r hmem hcard'
      simpa only [hsame] using htest

/-- The older accepted odd-square at its least prime dominates the
entire TWO-prime extension product; the total cutoff cannot be the
first failure after a successful odd ancestor at the same level. -/
theorem upper_two_min_total_lt
    (R : ℝ) (s : Finset ℕ) (p q : ℕ)
    (hpq : p < q) (hqsmall : ∀ r ∈ s, q < r)
    (hodd : Odd s.card)
    (hprevious : LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R s) :
    ((((insert p (insert q s)).prod id : ℕ) : ℝ) < R) := by
  classical
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hs0
    simp [hs0] at hodd
  let m := s.min' hsne
  have hm : m ∈ s := Finset.min'_mem s hsne
  have hmmin : ∀ r ∈ s, m ≤ r :=
    fun r hr => Finset.min'_le s r hr
  have hfilter : s.filter (fun x => m ≤ x) = s :=
    Finset.filter_eq_self.mpr hmmin
  have hmnotEven : ¬ Even ((s.filter (fun x => m ≤ x)).card) := by
    rw [hfilter]
    rcases hodd with ⟨k, hk⟩
    rintro ⟨j, hj⟩
    omega
  have hbound : ((s.prod id : ℕ) : ℝ) * (m : ℝ) ^ 2 < R := by
    simpa only [hfilter] using hprevious m hm hmnotEven
  have hqnot : q ∉ s := by
    intro h
    exact (lt_irrefl q) (hqsmall q h)
  have hpnot : p ∉ insert q s := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · omega
    · exact (lt_irrefl p) (hpq.trans (hqsmall p h))
  have hproduct :
      (insert p (insert q s)).prod id = p * q * s.prod id := by
    rw [Finset.prod_insert hpnot, Finset.prod_insert hqnot]
    simp only [id_eq]
    ring
  have hp_le_m : p ≤ m := (hpq.trans (hqsmall m hm)).le
  have hq_le_m : q ≤ m := (hqsmall m hm).le
  have hmul : (p : ℝ) * q ≤ (m : ℝ) ^ 2 := by
    calc
      (p : ℝ) * q ≤ (m : ℝ) * q :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hp_le_m)
          (Nat.cast_nonneg _)
      _ ≤ (m : ℝ) * m :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hq_le_m)
          (Nat.cast_nonneg _)
      _ = (m : ℝ) ^ 2 := by ring
  have hnonneg : (0 : ℝ) ≤ (s.prod id : ℕ) :=
    Nat.cast_nonneg _
  calc
    (((insert p (insert q s)).prod id : ℕ) : ℝ) =
        (p : ℝ) * q * (s.prod id : ℕ) := by
          rw [hproduct]
          push_cast
          ring
    _ ≤ (m : ℝ) ^ 2 * (s.prod id : ℕ) :=
      mul_le_mul_of_nonneg_right hmul hnonneg
    _ < R := by simpa only [mul_comm] using hbound

/-- A LITERAL upper-policy rejection two places after a successful
frozen-level odd prefix is equivalent to failure of the new least
prime's square. Both alternative failure modes have been discharged.
The no-duplicate condition makes full LIST product agree with its
actual FINSET product; it is not a setification of occurrences. -/
theorem upper_reject_after_certified_odd_iff_last_square
    (R : ℝ) (older : List ℕ) (p q : ℕ)
    (hodd : Odd older.toFinset.card)
    (hnodup : older.Nodup)
    (hpq : p < q)
    (hqsmall : ∀ r ∈ older.toFinset, q < r)
    (hpassed : ordinaryParityRosserPolicy false R false older = true) :
    ordinaryParityRosserPolicy false R false (p :: q :: older) = false ↔
      R ≤ (((p :: q :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 := by
  classical
  let s := older.toFinset
  have hprevious :
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R s :=
    ((upper_odd_test_iff R older).mp hpassed).2
  have hpnotolder : p ∉ older := by
    intro h
    exact (lt_irrefl p)
      (hpq.trans (hqsmall p (List.mem_toFinset.mpr h)))
  have hqnotolder : q ∉ older := by
    intro h
    exact (lt_irrefl q) (hqsmall q (List.mem_toFinset.mpr h))
  have hpnotnew : p ∉ q :: older := by
    simp [hpq.ne, hpnotolder]
  have hn : (p :: q :: older).Nodup :=
    List.nodup_cons.mpr
      ⟨hpnotnew, List.nodup_cons.mpr ⟨hqnotolder, hnodup⟩⟩
  have hlistproduct :
      (p :: q :: older).prod = (insert p (insert q s)).prod id := by
    have hprod :
        (∏ r ∈ (p :: q :: older).toFinset, r) =
          (p :: q :: older).prod := by
      simpa using List.prod_toFinset (fun r : ℕ => r) hn
    simpa only [List.toFinset_cons, s] using hprod.symm
  have htotal :
      (((p :: q :: older).prod : ℕ) : ℝ) < R := by
    rw [hlistproduct]
    exact upper_two_min_total_lt R s p q hpq hqsmall hodd hprevious
  have hsquare :
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R
        (p :: q :: older).toFinset ↔
        (((p :: q :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 < R := by
    simpa only [List.toFinset_cons, hlistproduct] using
      (upper_two_min_insert_iff_last_square
        R s p q hpq hqsmall hodd hprevious)
  constructor
  · intro hfailed
    rcases (upper_odd_rejected_iff R (p :: q :: older)).mp hfailed
      with hbadtotal | hbadsquare
    · exact (not_le_of_gt htotal hbadtotal).elim
    · exact le_of_not_gt (fun hlt => hbadsquare (hsquare.mpr hlt))
  · intro hlast
    apply (upper_odd_rejected_iff R (p :: q :: older)).mpr
    right
    intro hgood
    exact (not_lt_of_ge hlast) (hsquare.mp hgood)

/-- The actual original87 source has the successful preceding ODD
guard at its own frozen ordinary level, for BOTH genuine continuations.
For every strictly ordered two-prime prospective extension, a failed
odd policy is now only a last-prime square failure. The rank-nine first
test is intentionally excluded: it has no preceding post-eight
successful odd guard. No new carrier, owner, beta or mask is formed. -/
theorem owned87_post8_later_odd_reject_last_square
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining) :
    ∃ chosen : List ℕ,
      chosen <+ s.remaining ∧
      leaf.selected = chosen.reverse ++ s.selectedPrefix ∧
      ∀ older ∈ post8OddTrace s.selectedPrefix true chosen,
        ∀ (p q : ℕ),
          Odd older.toFinset.card →
          older.Nodup →
          p < q →
          (∀ r ∈ older.toFinset, q < r) →
          ordinaryParityRosserPolicy false
            (actualFrozenPost8Level n e q om N c s useParent)
            false (p :: q :: older) = false →
          actualFrozenPost8Level n e q om N c s useParent ≤
            (((p :: q :: older).prod : ℕ) : ℝ) * (p : ℝ) ^ 2 := by
  let R := actualFrozenPost8Level n e q om N c s useParent
  obtain ⟨chosen, hsub, hselected, hguards⟩ :=
    owned87_terminal_post8_success_guards
      delta n e q om N cap w z c s hs useParent leaf hleaf
  refine ⟨chosen, hsub, hselected, ?_⟩
  intro older htrace p q hodd hnodup hpq hqsmall hfailed
  have hpassed : ordinaryParityRosserPolicy false R false older = true :=
    (upper_odd_test_iff R older).mpr (hguards older htrace)
  exact (upper_reject_after_certified_odd_iff_last_square
    R older p q hodd hnodup hpq hqsmall hpassed).mp hfailed

end
end ImbalancedChen.P4AOriginalFull87InheritedOddSquares
