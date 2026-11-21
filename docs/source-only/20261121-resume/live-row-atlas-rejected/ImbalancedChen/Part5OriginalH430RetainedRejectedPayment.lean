import ImbalancedChen.Part5OriginalH430ClassicalRejectedShell
import ImbalancedChen.Part5OriginalH430ZeroFreshReceiverPayment

/-! A real retained-only subfamily of the remaining rejected history.
All occurrence positions remain. The bound is a directed cube-credit
budget, not an epsilon-small error or a final numerical reserve. -/
namespace ImbalancedChen.Part5OriginalH430RetainedRejectedPayment
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2EnhancedLowerPhysicalTransition P2EnhancedLowerFinitePhysicalGraph
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430IntegerItineraries
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430FrozenClassicalRootModuli
open Part5OriginalH430ClassicalRootThetaPayment Part5OriginalH430ClassicalRootCredits
open Part5OriginalH430ClassicalReceiverSubfamily
open Part5OriginalH430ZeroFreshReceiverPayment
open Part5OriginalH430ClassicalRejectedShell

def retainedEdge {N : ℕ} : Edge N → Bool
  | .retained _ => true
  | _ => false

theorem retained_path_zeroFresh {N : ℕ} (es : List (Edge N))
    (h : es.all retainedEdge = true) : es.all zeroFreshEdge = true := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      have hh : retainedEdge e = true ∧ es.all retainedEdge = true := by
        simpa only [List.all_cons,Bool.and_eq_true] using h
      have he : zeroFreshEdge e = true := by
        cases e <;> simp_all [retainedEdge,zeroFreshEdge]
      simp only [List.all_cons,he,ih hh.2,Bool.and_self]

/-- Retention preserves both the full physical node and the old word.
Its specified read mode is not asserted equal to the old scalar mode. -/
theorem retained_next_state {N : ℕ} (r : Request) (e : Edge N)
    (he : retainedEdge e = true) :
    (nextRequest r e).old = r.old ∧ (nextRequest r e).node = r.node := by
  cases e <;> simp_all [retainedEdge,nextRequest,edgeShape,appendedWord,
    advance,childUpper,perform]

theorem retained_replay_state {N : ℕ} (r : Request) (es : List (Edge N))
    (he : es.all retainedEdge = true) :
    (replay r es).old = r.old ∧ (replay r es).node = r.node := by
  induction es generalizing r with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
      have hh : retainedEdge e = true ∧ es.all retainedEdge = true := by
        simpa only [List.all_cons,Bool.and_eq_true] using he
      have hs := ih (nextRequest r e) hh.2
      have hn := retained_next_state r e hh.1
      exact ⟨hs.1.trans hn.1,hs.2.trans hn.2⟩

/-- The rejected set at a retained-only occurrence is the same actual
root rejected set, with D=1 and the original source cutoff. -/
theorem retained_rejected_eq_origin {N n p : ℕ} {k : Root} {τ Q : ℝ}
    {o : Occurrence N} (ho : o ∈ rootHistory N n k τ p)
    (hr : o.path.all retainedEdge = true) :
    rejectedChild N (parentProduct o.current.old) (tailProduct o) (memberCutoff Q o) =
      rejectedChild N p 1 (memberCutoff Q
        (origin (N := N) 430 (rootRequest N n k τ p))) := by
  have hs := retained_replay_state (rootRequest N n k τ p) o.path hr
  rw [← (history_facts ho).2.2] at hs
  simp only [parentProduct,tailProduct,memberCutoff,hs.1,hs.2,origin,rootRequest,
    List.prod_cons,List.prod_nil,mul_one,List.tail_cons]

def rejectedAt (N : ℕ) (Q : ℝ) (o : Occurrence N) : ℝ :=
  ((rejectedChild N (parentProduct o.current.old) (tailProduct o) (memberCutoff Q o)).card:ℝ)

theorem retained_member_rejected_le_credit {N n m p : ℕ} {τ : ℝ}
    {c : RootKey n m} {o : Occurrence N}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c)
    (ho : o ∈ rootHistory N n .U3 τ p) (hr : o.path.all retainedEdge = true) :
    rejectedAt N (cellQ N n c.1) o ≤ cubeCredit N n p τ := by
  have hb := (Finset.mem_filter.mp hp).1
  have hQ := (original_fibre_geometry hN hτ hτ' hn
    (classicalFibre_subset_rootFibre c hp)).1
  unfold rejectedAt
  rw [retained_rejected_eq_origin ho hr,hQ]
  have hsub := rejected_antitone_cutoff N p 1
    (common_cutoff_le_origin (m := m) hN hτ hτ' hn hb)
  have hc : ((rejectedChild N p 1 (memberCutoff (rootQ N n .U3 τ p)
      (origin (N := N) 430 (rootRequest N n .U3 τ p)))).card:ℝ) ≤
      ((rejectedChild N p 1 (cutoffAt N n m p τ)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (root_query_rejected_le_cubeCredit hN hτ hτ' hn hb)

def retainedRejected (N n m : ℕ) (τ : ℝ) (c : RootKey n m) (p : ℕ) : ℝ :=
  chargedList (fun o => if o.path.all retainedEdge then
    rejectedAt N (cellQ N n c.1) o else 0) (rootHistory N n .U3 τ p)

/-- The reused zero-fresh sum is precisely the actual retained-only
rejected sum here. No extra coefficient or hidden source is present. -/
theorem retainedRejected_eq_actual (N n m : ℕ) (τ : ℝ) (c : RootKey n m) (p : ℕ) :
    retainedRejected N n m τ c p =
      ((rootHistory N n .U3 τ p).map (fun o => if o.path.all retainedEdge then
        mark o * rejectedAt N (cellQ N n c.1) o else 0)).sum := by
  have h (os : List (Occurrence N)) :
      chargedList (fun o => if o.path.all retainedEdge then
        rejectedAt N (cellQ N n c.1) o else 0) os =
      (os.map (fun o => if o.path.all retainedEdge then
        mark o * rejectedAt N (cellQ N n c.1) o else 0)).sum := by
    induction os with
    | nil => rfl
    | cons o os ih =>
        apply congrArg₂ (·+·) ?_ ih
        by_cases hr : o.path.all retainedEdge = true
        · have hz := retained_path_zeroFresh o.path hr
          simp only [hr,if_true,occurrenceBudget,hz]
        · simp only [hr,if_false,mul_zero]
  exact h _

theorem retainedRejected_le_cubeCredit {N n m p : ℕ} {τ : ℝ} {c : RootKey n m}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c) :
    retainedRejected N n m τ c p ≤ 431*cubeCredit N n p τ := by
  have hcredit := cubeCredit_nonneg hN hτ hτ' hn (Finset.mem_filter.mp hp).1
  have hF : ∀ o ∈ rootHistory N n .U3 τ p,
      (if o.path.all retainedEdge then rejectedAt N (cellQ N n c.1) o else 0) ≤
        cubeCredit N n p τ := by
    intro o ho
    split_ifs with hr
    · exact retained_member_rejected_le_credit hN hτ hτ' hn hp ho hr
    · exact hcredit
  exact (chargedList_le _ _ (cubeCredit N n p τ) hF).trans
    (mul_le_mul_of_nonneg_right (zeroFresh_rootHistory_budget N n .U3 τ p) hcredit)

def rejectedHistoryTotal (N n m : ℕ) (τ : ℝ) (c : RootKey n m) (p : ℕ) : ℝ :=
  ((rootHistory N n .U3 τ p).map (fun o => mark o * rejectedAt N (cellQ N n c.1) o)).sum

def nonretainedRejected (N n m : ℕ) (τ : ℝ) (c : RootKey n m) (p : ℕ) : ℝ :=
  ((rootHistory N n .U3 τ p).map (fun o => if o.path.all retainedEdge then 0 else
    mark o * rejectedAt N (cellQ N n c.1) o)).sum

/-- The unpaid complement is named exactly, rather than discarded. -/
theorem rejectedHistory_split (N n m : ℕ) (τ : ℝ) (c : RootKey n m) (p : ℕ) :
    rejectedHistoryTotal N n m τ c p =
      retainedRejected N n m τ c p + nonretainedRejected N n m τ c p := by
  rw [retainedRejected_eq_actual]
  unfold rejectedHistoryTotal nonretainedRejected
  have h (os : List (Occurrence N)) :
      (os.map (fun o => mark o * rejectedAt N (cellQ N n c.1) o)).sum =
      (os.map (fun o => if o.path.all retainedEdge then
        mark o * rejectedAt N (cellQ N n c.1) o else 0)).sum +
      (os.map (fun o => if o.path.all retainedEdge then 0 else
        mark o * rejectedAt N (cellQ N n c.1) o)).sum := by
    induction os with
    | nil => simp
    | cons o os ih =>
        simp only [List.map_cons,List.sum_cons,ih]
        by_cases hr : o.path.all retainedEdge = true <;> simp [hr] <;> ring
  exact h _

/-- All actual retained-only rejected positions, including the origin,
with the explicit original-count subtraction. This is NOT an ε-small
remainder bound, a payment of all R_rejected, or a final reserve ≤1. -/
theorem actual_retained_rejected_credit_payment {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        retainedRejected N n m τ c p) ≤
      431*((1+ε)*classicalOwnTheta N n m τ -
        ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
          ((originalReceiver N p).card:ℝ)) := by
  filter_upwards [classical_cubeCredit_pool hτ hτ' he,
    eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn
  have hsum : (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
      retainedRejected N n m τ c p) ≤
      ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c, 431*cubeCredit N n p τ := by
    apply Finset.sum_le_sum
    intro c _
    exact Finset.sum_le_sum (fun p hp => retainedRejected_le_cubeCredit hN hτ.le hτ' hn hp)
  rw [sum_classicalFibre,← Finset.mul_sum] at hsum
  rw [classicalOwnTheta_eq hN hτ.le hτ' hn,
    sum_classicalFibre N n m τ (fun p => ((originalReceiver N p).card:ℝ))]
  exact hsum.trans (mul_le_mul_of_nonneg_left (hd hEven n hn) (by norm_num : (0:ℝ) ≤ 431))

end
end ImbalancedChen.Part5OriginalH430RetainedRejectedPayment
