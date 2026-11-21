import ImbalancedChen.Part5OriginalH430ClassicalReceiverSubfamily

/-! Actual selected zero-fresh paths, counted by LIST POSITION.  The
coefficient budget is proved from literal children: retained and W1 fixed
have weight one; the two W2 fixed reads have weights 4/5 and 1/5.  There
is no sum over unselected alternatives.  The terminal arithmetic count
uses the original root mask; rejectedChild is outside this theorem. -/
namespace ImbalancedChen.Part5OriginalH430ZeroFreshReceiverPayment
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2Selected430CausalOccurrenceExporter (iterate roundDecision Choice)
open P5OriginalActionMassBound (Original106Action)
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2EnhancedLowerFinitePhysicalGraph
open P2FrozenReceiverCountActions (frozenCount)
open Part5UpperTables.OriginalU34
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430IntegerItineraries
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430ClassicalRootThetaPayment
open Part5OriginalH430ClassicalReceiverSubfamily

/-- Exactly the literal edges that append no new prime. -/
def zeroFreshEdge {N : ℕ} : Edge N → Bool
  | .retained _ | .w1Fixed _ _ | .w2Fixed _ _ => true
  | _ => false

def edgeBudget {N : ℕ} (e : Edge N) : ℝ :=
  if zeroFreshEdge e then edgeWeight e else 0

def occurrenceBudget {N : ℕ} (o : Occurrence N) : ℝ :=
  if o.path.all zeroFreshEdge then mark o else 0

def listBudget {N : ℕ} : List (Occurrence N) → ℝ
  | [] => 0
  | o :: os => occurrenceBudget o + listBudget os

theorem zeroFresh_next_old {N : ℕ} (r : Request) (e : Edge N)
    (he : zeroFreshEdge e = true) : (nextRequest r e).old = r.old := by
  cases e <;> simp_all [zeroFreshEdge,nextRequest,edgeShape,appendedWord]

theorem zeroFresh_replay_old {N : ℕ} (r : Request) (es : List (Edge N))
    (he : es.all zeroFreshEdge = true) : (replay r es).old = r.old := by
  induction es generalizing r with
  | nil => rfl
  | cons e es ih =>
      have he' : zeroFreshEdge e = true ∧ es.all zeroFreshEdge = true := by
        simpa only [List.all_cons,Bool.and_eq_true] using he
      exact (ih (nextRequest r e) he'.2).trans (zeroFresh_next_old r e he'.1)

/-- The selector really retains the old root word, not merely its product. -/
theorem zeroFresh_original_word {N n p : ℕ} {k : Root} {τ : ℝ} {o : Occurrence N}
    (ho : o ∈ rootHistory N n k τ p) (he : o.path.all zeroFreshEdge = true) :
    o.current.old = [p] := by
  rw [(history_facts ho).2.2]
  exact zeroFresh_replay_old (rootRequest N n k τ p) o.path he

theorem edgeBudget_nonneg {N : ℕ} (e : Edge N) : 0 ≤ edgeBudget e := by
  unfold edgeBudget
  split_ifs
  · exact (edgeWeight_pos e).le
  · exact le_rfl

theorem occurrenceBudget_nonneg {N : ℕ} (o : Occurrence N) :
    0 ≤ occurrenceBudget o := by
  unfold occurrenceBudget
  split_ifs
  · exact (mark_pos o).le
  · exact le_rfl

@[simp] theorem occurrenceBudget_origin {N : ℕ} (g : ℕ) (r : Request) :
    occurrenceBudget (origin (N := N) g r) = 1 := by
  simp [occurrenceBudget,origin,mark]

theorem occurrenceBudget_prepend {N : ℕ} (e : Edge N) (o : Occurrence N) :
    occurrenceBudget (prepend e o) = edgeBudget e * occurrenceBudget o := by
  cases he : zeroFreshEdge e <;>
    simp [occurrenceBudget,edgeBudget,prepend,List.all_cons,he,mark,mul_ite]

theorem listBudget_append {N : ℕ} (xs ys : List (Occurrence N)) :
    listBudget (xs ++ ys) = listBudget xs + listBudget ys := by
  induction xs with
  | nil => simp [listBudget]
  | cons o os ih => simp only [List.cons_append,listBudget,ih,add_assoc]

theorem listBudget_map_prepend {N : ℕ} (e : Edge N) (os : List (Occurrence N)) :
    listBudget (os.map (prepend e)) = edgeBudget e * listBudget os := by
  induction os with
  | nil => simp [listBudget]
  | cons o os ih =>
      simp only [List.map_cons,listBudget,occurrenceBudget_prepend,ih,mul_add]

private theorem listBudget_flatMap {N : ℕ} {A : Type*} (es : List A)
    (f : A → List (Occurrence N)) :
    listBudget (es.flatMap f) = (es.map (fun e => listBudget (f e))).sum := by
  induction es with
  | nil => simp [listBudget]
  | cons e es ih =>
      simp only [List.flatMap_cons,listBudget_append,List.map_cons,List.sum_cons,ih]

@[simp] private theorem zeroFresh_zero_sum {A : Type*} (xs : List A) :
    (xs.map (fun _ => (0:ℝ))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih,zero_add]

/-- A per-request, actual-winner coefficient sum, proved from the
literal edge constructors.  It does not count fresh prime branches. -/
theorem zeroFresh_children_budget (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    ((children N Q g r).map edgeBudget).sum ≤ 1 := by
  have hbank (a : Original106Action) :
      ((bankEdges N Q r a).map edgeBudget).sum ≤ 1 := by
    cases a with
    | inl ij =>
        rcases ij with ⟨i,j⟩
        simp [bankEdges,w1Edges,List.map_map,Function.comp_def,
          edgeBudget,zeroFreshEdge,edgeWeight]
    | inr j =>
        norm_num [bankEdges,w2SingleEdges,w2PairEdges,List.map_map,
          Function.comp_def,edgeBudget,zeroFreshEdge,edgeWeight]
  unfold children
  cases hi : resolve (g+1) r with
  | none => simp
  | some i =>
      cases hc : (roundDecision (iterate g) r.node.upper i).choice with
      | retained => simp [branchEdges,edgeBudget,zeroFreshEdge,edgeWeight]
      | buchstab =>
          simp [branchEdges,List.map_map,Function.comp_def,edgeBudget,zeroFreshEdge]
      | bank slot => exact hbank _

/-- All list occurrences across the entire finite history are retained.
The root contributes one, so the total is g+1, not one. -/
theorem zeroFresh_history_budget (N : ℕ) (Q : ℝ) (g : ℕ) (r : Request) :
    listBudget (history N Q g r) ≤ (g:ℝ)+1 := by
  induction g generalizing r with
  | zero => simp [history,listBudget]
  | succ g ih =>
      have hsum (es : List (Edge N)) :
          (es.map (fun e => edgeBudget e * listBudget
            (history N Q g (nextRequest r e)))).sum ≤
          ((g:ℝ)+1) * (es.map edgeBudget).sum := by
        induction es with
        | nil => simp
        | cons e es he =>
            simp only [List.map_cons,List.sum_cons]
            have hm := mul_le_mul_of_nonneg_left (ih (nextRequest r e))
              (edgeBudget_nonneg e)
            calc
              _ ≤ edgeBudget e * ((g:ℝ)+1) +
                  ((g:ℝ)+1) * (es.map edgeBudget).sum := add_le_add hm he
              _ = _ := by ring
      rw [history,listBudget,occurrenceBudget_origin,listBudget_flatMap]
      simp_rw [listBudget_map_prepend]
      have hm := hsum (children N Q g r)
      have hc := mul_le_mul_of_nonneg_left (zeroFresh_children_budget N Q g r)
        (by positivity : (0:ℝ) ≤ (g:ℝ)+1)
      simp only [Nat.cast_add,Nat.cast_one,mul_one] at *
      linarith only [hm,hc]

theorem zeroFresh_rootHistory_budget (N n : ℕ) (k : Root) (τ : ℝ) (p : ℕ) :
    listBudget (rootHistory N n k τ p) ≤ 431 := by
  have h := zeroFresh_history_budget N
    (Part5OriginalH430FrozenIntegerSupport.rootQ N n k τ p) 430
    (rootRequest N n k τ p)
  norm_num only [Nat.cast_ofNat] at h
  exact h

/-- This sum has one summand per emitted list POSITION.  Equal requests,
equal quotients, and equal products at different positions stay repeated. -/
def chargedList {N : ℕ} (F : Occurrence N → ℝ) : List (Occurrence N) → ℝ
  | [] => 0
  | o :: os => occurrenceBudget o * F o + chargedList F os

theorem chargedList_eq_sum {N : ℕ} (F : Occurrence N → ℝ) (os : List (Occurrence N)) :
    chargedList F os = (os.map (fun o => occurrenceBudget o * F o)).sum := by
  induction os with
  | nil => rfl
  | cons o os ih => simp only [chargedList,List.map_cons,List.sum_cons,ih]

theorem chargedList_le {N : ℕ} (F : Occurrence N → ℝ) (os : List (Occurrence N))
    (C : ℝ) (hF : ∀ o ∈ os, F o ≤ C) :
    chargedList F os ≤ listBudget os * C := by
  induction os with
  | nil => simp [chargedList,listBudget]
  | cons o os ih =>
      rw [chargedList,listBudget,add_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hF o (List.mem_cons_self ..))
          (occurrenceBudget_nonneg o))
        (ih (fun q hq => hF q (List.mem_cons_of_mem _ hq)))

def zeroFreshReceivers (N n m : ℕ) (τ : ℝ) (c : RootKey n m) (p : ℕ) : ℝ :=
  chargedList (fun o => (frozenCount N (parentProduct o.current.old) (rootMask N p)
    (memberCutoff (cellQ N n c.1) o) : ℝ)) (rootHistory N n .U3 τ p)

/-- A genuine all-receiver sum over the zero-fresh emitted subfamily.
The only root-card bound used is for the actual original receiver set. -/
theorem zeroFresh_receivers_le_root {N n m p : ℕ} {τ : ℝ} {c : RootKey n m}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ classicalFibre N n m τ c) :
    zeroFreshReceivers N n m τ c p ≤ 431 * ((originalReceiver N p).card : ℝ) := by
  unfold zeroFreshReceivers
  apply (chargedList_le _ _ ((originalReceiver N p).card : ℝ)
    (fun o ho => actual_masked_member_le_root hN hτ hτ' hn hp ho)).trans
  exact mul_le_mul_of_nonneg_right (zeroFresh_rootHistory_budget N n .U3 τ p)
    (Nat.cast_nonneg _)

/-- The asymptotic threshold precedes BOTH common resolutions.  Each
fibre keeps its own physical Q; all 431 history levels and actual fixed
read branches are paid, including repeated positions.  This statement
does not include rejectedChild, fresh paths, adopted seeds, or bank bases. -/
theorem actual_zeroFresh_classical_receivers_paid {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        zeroFreshReceivers N n m τ c p) ≤
          431*(1+ε)*classicalOwnTheta N n m τ := by
  filter_upwards [classical_original_card_bound hτ hτ' he,
    eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn
  have hpoint : (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
      zeroFreshReceivers N n m τ c p) ≤
      ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        431*((originalReceiver N p).card : ℝ) := by
    apply Finset.sum_le_sum
    intro c _
    exact Finset.sum_le_sum (fun p hp =>
      zeroFresh_receivers_le_root hN hτ.le hτ' hn hp)
  rw [sum_classicalFibre,← Finset.mul_sum] at hpoint
  rw [classicalOwnTheta_eq hN hτ.le hτ' hn]
  exact hpoint.trans ((mul_le_mul_of_nonneg_left (hd hEven n hn)
    (by norm_num : (0:ℝ) ≤ 431)).trans_eq (by ring))

end
end ImbalancedChen.Part5OriginalH430ZeroFreshReceiverPayment
