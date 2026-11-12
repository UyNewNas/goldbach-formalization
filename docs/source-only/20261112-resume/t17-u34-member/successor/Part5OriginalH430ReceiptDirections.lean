import ImbalancedChen.Part5OriginalH430AllEmittedReceiptLanes
import ImbalancedChen.Part5OriginalH430ReceiptFourBand

/-! Positive fixed-query expansion and its exact signed base debit on a
true occupied box. The original mark, fixed physical level, root tag
and additive-prime predicate stay attached to their occurrence. -/
namespace ImbalancedChen.Part5OriginalH430ReceiptDirections
noncomputable section
open Finset Wu2008DoubleSieve
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2FrozenReceiverCountActions (frozenCount frozenCarrier quotientCount markedPhi)
open P2AllW1FrozenReceiverFiniteAction (rawTripleCount)
open P5OriginalU5FrozenSource (receiver)
open P5OriginalActionMassBound (Original106Action)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenIntegerSupport
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430SameQHistoryCells Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OwnedRootCounts Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430SelectedMemberBox Part5OriginalH430SelectedMemberFixedQuery
open Part5OriginalH430ReceiptFourBand
open scoped Classical BigOperators

def outsideReceipt (N p ell : ℕ) : Prop := receiver N ell ∧ ¬rootMask N p ell

theorem receiver_count_split (N p B : ℕ) (z : ℝ) :
    count N B (receiver N) z = count N B (rootMask N p) z + count N B (outsideReceipt N p) z := by
  let A := (sieveCarrier N B (B*N) z).filter (receiver N)
  have hi : A.filter (rootMask N p) = (sieveCarrier N B (B*N) z).filter (rootMask N p) := by
    ext ell
    simp only [A,mem_filter,rootMask]
    tauto
  have ho : A.filter (fun ell => ¬rootMask N p ell) =
      (sieveCarrier N B (B*N) z).filter (outsideReceipt N p) := by
    ext ell
    simp only [A,mem_filter,outsideReceipt,and_assoc]
  rw [count_card,count_card,count_card,←hi,←ho]
  simpa only [sum_const,nsmul_eq_mul,mul_one] using
    (sum_filter_add_sum_filter_not A (rootMask N p) (fun _ => (1:ℝ))).symm

/-- When a lower bound is needed on a child, ordinary child counts enter
the subtraction with the separate outside mass added back. Both sums keep
the very same half-open prime window and the prime child's own cutoff. -/
theorem buchstab_signed_base (N p d : ℕ) {z w : ℝ} (hzw : z≤w) :
    count N d (rootMask N p) w = count N d (receiver N) z -
      (∑ q∈primeWindow (d*N) z w, count N (d*q) (receiver N) (q:ℝ)) -
      count N d (outsideReceipt N p) z +
      ∑ q∈primeWindow (d*N) z w, count N (d*q) (outsideReceipt N p) (q:ℝ) := by
  have hb : count N d (rootMask N p) z = count N d (rootMask N p) w +
      ∑ q∈primeWindow (d*N) z w, count N (d*q) (rootMask N p) (q:ℝ) := by
    exact_mod_cast P2FrozenReceiverCountActions.frozen_selected_buchstab N d (rootMask N p) hzw
  have hc : (∑ q∈primeWindow (d*N) z w, count N (d*q) (receiver N) (q:ℝ)) =
      (∑ q∈primeWindow (d*N) z w, count N (d*q) (rootMask N p) (q:ℝ)) +
      ∑ q∈primeWindow (d*N) z w, count N (d*q) (outsideReceipt N p) (q:ℝ) := by
    rw [←sum_add_distrib]
    exact sum_congr rfl (fun q _ => receiver_count_split N p (d*q) q)
  linarith [receiver_count_split N p d z]

theorem W1_raw_positive_le_receiver (N p d M : ℕ) (z w : ℝ) :
    rawTripleCount N d M (rootMask N p) z w ≤ rawTripleCount N d M (receiver N) z w := by
  unfold rawTripleCount
  apply sum_le_sum
  intro q _
  let A := sieveCarrier N (d*(q.1*q.2.1*q.2.2)) (M*q.1) (q.2.1:ℝ)
  have hi : A.filter (rootMask N p) ⊆ A.filter (receiver N) := fun x hx =>
    mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.1⟩
  unfold quotientCount
  exact_mod_cast card_le_card hi

def fixedOutside {N n m mesh : ℕ} (k : Root) (t : ℝ) (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh) : ℝ :=
  ∑ p∈rootFibre N n m k t c, markedPhi N (cellQ N n c.1)
    (positions N n mesh k t p g act b) (fun l => parentProduct (levelOccurrence l).current.old)
    (fun l => levelMark l) (fun _ => outsideReceipt N p) (fixedQuery b)

def fixedOrdinary {N n m mesh : ℕ} (k : Root) (t : ℝ) (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh) : ℝ :=
  ∑ p∈rootFibre N n m k t c, markedPhi N (cellQ N n c.1)
    (positions N n mesh k t p g act b) (fun l => parentProduct (levelOccurrence l).current.old)
    (fun l => levelMark l) (fun _ => receiver N) (fixedQuery b)

def shellMass {N n m mesh : ℕ} (k : Root) (t : ℝ) (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh) : ℝ :=
  ∑ p∈rootFibre N n m k t c, ∑ l∈positions N n mesh k t p g act b,
    levelMark l * queryShell (cellQ N n c.1) p (levelOccurrence l) (fixedQuery b)

theorem fixed_costs_nonneg {N n m mesh : ℕ} (k : Root) (t : ℝ) (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh) :
    0 ≤ fixedOutside (N:=N) k t g act c b ∧ 0 ≤ shellMass (N:=N) k t g act c b := by
  constructor
  · apply sum_nonneg
    intro p _
    apply sum_nonneg
    intro l _
    exact mul_nonneg (mark_pos (levelOccurrence l)).le (by
      simp only [frozenCount,Int.cast_natCast]; exact Nat.cast_nonneg _)
  · apply sum_nonneg
    intro p _
    apply sum_nonneg
    intro l _
    apply mul_nonneg (mark_pos (levelOccurrence l)).le
    apply sum_nonneg
    intro q _
    simp only [frozenCount,Int.cast_natCast]
    exact Nat.cast_nonneg _

/-- A positive ordinary bound at this fixed query dominates the actual
receipt count. For a negative count the discarded complement and the
fixed-query shell both have to be added back to the signed expression. -/
theorem fixed_receipt_signed_transfer {N n m mesh : ℕ} (k : Root) {t : ℝ} (g : Fin 430)
    (act : Original106Action) (c : RootKey n m) (b : Box mesh)
    (hN : 4≤N) (ht : 0≤t) (hu : t≤1/12) (hn : 1/((n:ℝ)+1)≤11/384) :
    let R := boxMasked N n m mesh k t g act c b
    let F := fixedOrdinary (N:=N) k t g act c b
    let O := fixedOutside (N:=N) k t g act c b
    let S := shellMass (N:=N) k t g act c b
    F = R + S + O ∧ R ≤ F ∧ -R = -F + O + S := by
  dsimp only
  have hbox := fixed_query_original_receipts k g act c b hN ht hu hn
  dsimp only at hbox
  rw [← box_count_on_original_receipts k g act c b (by omega : 2≤N) ht hu hn] at hbox
  have hall : fixedOrdinary (N:=N) k t g act c b =
      (∑ p∈rootFibre N n m k t c, markedPhi N (cellQ N n c.1)
        (positions N n mesh k t p g act b) (fun l => parentProduct (levelOccurrence l).current.old)
        (fun l => levelMark l) (fun _ => rootMask N p) (fixedQuery b)) +
      fixedOutside (N:=N) k t g act c b := by
    unfold fixedOrdinary fixedOutside
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro p _
    unfold markedPhi
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro l _
    rw [←mul_add]
    exact congrArg (fun v : ℝ => levelMark l*v)
      (receiver_count_split N p (parentProduct (levelOccurrence l).current.old) _)
  rw [hbox] at hall
  change fixedOrdinary (N:=N) k t g act c b =
    boxMasked N n m mesh k t g act c b + shellMass (N:=N) k t g act c b +
    fixedOutside (N:=N) k t g act c b at hall
  obtain ⟨hO,hS⟩ := fixed_costs_nonneg (N:=N) k t g act c b
  exact ⟨hall,by linarith,by linarith⟩

end
end ImbalancedChen.Part5OriginalH430ReceiptDirections
