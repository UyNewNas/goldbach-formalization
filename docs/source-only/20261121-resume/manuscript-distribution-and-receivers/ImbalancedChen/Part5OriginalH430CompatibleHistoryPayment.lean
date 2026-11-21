import ImbalancedChen.Part5OriginalH430FreshBranchIncidence

/-! Every ORIGINAL-compatible receiver in the actual selected history,
including fresh singleton/pair edges.  Positions are never deduplicated.
The fixed constant is deliberately coarse and depends only on depth 430.
The rootMask is retained; rejectedChild and adopted/base/switched sources
are not included in this payment. SOURCE ONLY / UNCOMPILED. -/
namespace ImbalancedChen.Part5OriginalH430CompatibleHistoryPayment
noncomputable section
open Finset Filter Real
open scoped Classical BigOperators Topology
open P2EnhancedLowerPrimeChildCarriers (parentProduct)
open P2FrozenReceiverCountActions (frozenCount)
open Part5OriginalH430PhysicalRoots Part5OriginalH430FrozenRootRefinement
open Part5OriginalH430FrozenIntegerSupport (rootQ)
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430IntegerItineraries
open Part5OriginalH430TaggedArithmeticReceivers Part5OriginalH430OwnedRootCounts
open Part5OriginalH430OriginalReceiptMemberPullback
open Part5OriginalH430ClassicalReceiverSubfamily
open Part5OriginalH430ClassicalRootThetaPayment
open Part5OriginalH430ReceiptPrimeBudget Part5OriginalH430FreshBranchIncidence

def pathCharge {N : ℕ} (P : Finset ℕ) (o : Occurrence N) : ℝ :=
  if ∀ e ∈ o.path, Allowed P e then mark o else 0

def pathMass {N : ℕ} (P : Finset ℕ) : List (Occurrence N) → ℝ
  | [] => 0
  | o :: os => pathCharge P o + pathMass P os

/-- No mesh, resolution, receiver, or N parameter occurs in this constant. -/
def treeBudget : ℕ → ℝ
  | 0 => 1
  | g+1 => 1 + 105 * treeBudget g

theorem treeBudget_nonneg (g : ℕ) : 0 ≤ treeBudget g := by
  induction g with
  | zero => norm_num [treeBudget]
  | succ g ih => dsimp only [treeBudget]; positivity

theorem treeBudget_closed (g : ℕ) : treeBudget g = ((105:ℝ)^(g+1)-1)/104 := by
  induction g with
  | zero => norm_num [treeBudget]
  | succ g ih =>
      rw [treeBudget,ih]
      simp only [Nat.succ_eq_add_one,pow_succ]
      ring

theorem pathCharge_nonneg {N : ℕ} (P : Finset ℕ) (o : Occurrence N) :
    0 ≤ pathCharge P o := by
  unfold pathCharge
  split_ifs
  · exact (mark_pos o).le
  · exact le_rfl

@[simp] theorem pathCharge_origin {N : ℕ} (P : Finset ℕ) (g : ℕ) (r : Request) :
    pathCharge P (origin (N := N) g r) = 1 := by simp [pathCharge,origin,mark]

theorem pathCharge_prepend {N : ℕ} (P : Finset ℕ) (e : Edge N) (o : Occurrence N) :
    pathCharge P (prepend e o) = edgeCharge P e * pathCharge P o := by
  by_cases he : Allowed P e <;>
    by_cases ho : ∀ d ∈ o.path, Allowed P d <;>
      simp [pathCharge,edgeCharge,prepend,mark,he,ho]

private theorem mass_append {N : ℕ} (P : Finset ℕ) (xs ys : List (Occurrence N)) :
    pathMass P (xs++ys) = pathMass P xs + pathMass P ys := by
  induction xs with
  | nil => simp [pathMass]
  | cons o os ih => simp only [List.cons_append,pathMass,ih,add_assoc]

private theorem mass_prepend {N : ℕ} (P : Finset ℕ) (e : Edge N) (os : List (Occurrence N)) :
    pathMass P (os.map (prepend e)) = edgeCharge P e * pathMass P os := by
  induction os with
  | nil => simp [pathMass]
  | cons o os ih => simp only [List.map_cons,pathMass,pathCharge_prepend,ih,mul_add]

private theorem mass_flatMap {N : ℕ} {A : Type*} (P : Finset ℕ) (es : List A)
    (f : A → List (Occurrence N)) :
    pathMass P (es.flatMap f) = (es.map (fun e => pathMass P (f e))).sum := by
  induction es with
  | nil => simp [pathMass]
  | cons e es ih =>
      simp only [List.flatMap_cons,mass_append,List.map_cons,List.sum_cons,ih]

/-- Recursion over the actual selected request tree.  Every order and
every repeated position is counted; no itinerary-injectivity is used. -/
theorem allowed_history_mass (N : ℕ) (P : Finset ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) (hP : P.card ≤ 11) :
    pathMass P (history N Q g r) ≤ treeBudget g := by
  induction g generalizing r with
  | zero => simp [history,pathMass,treeBudget]
  | succ g ih =>
      have hsum (es : List (Edge N)) :
          (es.map (fun e => edgeCharge P e * pathMass P
            (history N Q g (nextRequest r e)))).sum ≤ treeBudget g * edgeSum P es := by
        induction es with
        | nil => simp [edgeSum]
        | cons e es he =>
            simp only [List.map_cons,List.sum_cons]
            have hm := mul_le_mul_of_nonneg_left (ih (nextRequest r e))
              (edgeCharge_nonneg P e)
            have heq : edgeSum P (e::es) = edgeCharge P e + edgeSum P es := rfl
            rw [heq]
            calc
              _ ≤ edgeCharge P e * treeBudget g + treeBudget g * edgeSum P es :=
                add_le_add hm he
              _ = _ := by ring
      rw [history,pathMass,pathCharge_origin,mass_flatMap]
      simp_rw [mass_prepend]
      calc
        _ ≤ 1 + treeBudget g * edgeSum P (children N Q g r) :=
          add_le_add_left (hsum _) 1
        _ ≤ 1 + treeBudget g * 105 := add_le_add_left
          (mul_le_mul_of_nonneg_left (actual_children_receipt_budget N P Q g r hP)
            (treeBudget_nonneg g)) 1
        _ = treeBudget (g+1) := by rw [treeBudget]; ring

def freshWord {N : ℕ} : List (Edge N) → List ℕ
  | [] => []
  | e::es => appendedWord (edgeShape e) (edgePrimes e) ++ freshWord es

theorem replay_old_word {N : ℕ} (r : Request) (es : List (Edge N)) :
    (replay r es).old = r.old ++ freshWord es := by
  induction es generalizing r with
  | nil => simp [replay,freshWord]
  | cons e es ih =>
      simpa only [replay,freshWord,nextRequest,List.append_assoc] using ih (nextRequest r e)

private theorem freshWord_mem {N : ℕ} {es : List (Edge N)} {e : Edge N} {q : ℕ}
    (he : e ∈ es) (hq : q ∈ appendedWord (edgeShape e) (edgePrimes e)) :
    q ∈ freshWord es := by
  induction es with
  | nil => cases he
  | cons d ds ih =>
      rcases List.mem_cons.mp he with rfl | he
      · exact List.mem_append_left _ hq
      · exact List.mem_append_right _ (ih he)

private theorem member_dvd_prod {q : ℕ} {xs : List ℕ} (hq : q ∈ xs) : q ∣ xs.prod := by
  induction xs with
  | nil => cases hq
  | cons r rs ih =>
      rcases List.mem_cons.mp hq with rfl | hq
      · exact dvd_mul_right _ _
      · exact (ih hq).trans (dvd_mul_left _ _)

/-- Actual compatibility D|q forces each path letter into the original
q's prime support.  D is the chronological word product, with all
multiplicities; no converse or unique-path assertion is made. -/
theorem original_receipt_allows_path {N n m p q : ℕ} {k : Root} {τ : ℝ}
    {c : RootKey n m} {o : Occurrence N}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c)
    (ho : o ∈ rootHistory N n k τ p) (hq : q ∈ originalReceiver N p)
    (hD : tailProduct o ∣ q) : ∀ e ∈ o.path, Allowed q.primeFactors e := by
  have hband := (Finset.mem_filter.mp hp).1
  have hcoh := rootHistory_coherent (by omega : 1 < N) hτ hτ' hn
    (original_band_prime hband) (original_band_geometry hN hband) ho
  have hword : o.current.old = [p] ++ freshWord o.path := by
    rw [(history_facts ho).2.2,replay_old_word]
    rfl
  have htail : tailProduct o = (freshWord o.path).prod := by
    simp only [tailProduct,hword,List.singleton_append,List.tail_cons]
  rw [htail] at hD
  have hqpos := (chenQuotientPrimeSource_data (Finset.mem_filter.mp hq).1).1
  intro e he r hr
  have hm := freshWord_mem he hr
  have hprime : r.Prime := (hcoh.letters r (by
    rw [hword]
    exact List.mem_append_right _ hm)).1
  exact Nat.mem_primeFactors.mpr ⟨hprime,(member_dvd_prod hm).trans hD,hqpos.ne'⟩

def receiptPoint {N : ℕ} (Q : ℝ) (q : ℕ) (o : Occurrence N) : ℝ :=
  if tailProduct o ∣ q ∧ ChenPrimeRough (memberCutoff Q o) (q/tailProduct o)
  then mark o else 0

def receiptIncidence {N : ℕ} (Q : ℝ) (q : ℕ) (os : List (Occurrence N)) : ℝ :=
  (os.map (receiptPoint Q q)).sum

theorem receiptPoint_le {N n m p q : ℕ} {k : Root} {τ : ℝ}
    {c : RootKey n m} {o : Occurrence N}
    (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c)
    (ho : o ∈ rootHistory N n k τ p) (hq : q ∈ originalReceiver N p) :
    receiptPoint (cellQ N n c.1) q o ≤ pathCharge q.primeFactors o := by
  unfold receiptPoint
  split_ifs with h
  · have ha := original_receipt_allows_path hN hτ hτ' hn hp ho hq h.1
    simpa only [pathCharge,if_pos ha] using (le_rfl : mark o ≤ mark o)
  · exact pathCharge_nonneg _ _

private theorem map_sum_le_mass {N : ℕ} (P : Finset ℕ) (os : List (Occurrence N))
    (f : Occurrence N → ℝ) (hf : ∀ o ∈ os, f o ≤ pathCharge P o) :
    (os.map f).sum ≤ pathMass P os := by
  induction os with
  | nil => exact le_rfl
  | cons o os ih =>
      exact add_le_add (hf o (List.mem_cons_self ..))
        (ih (fun t ht => hf t (List.mem_cons_of_mem _ ht)))

theorem actual_receipt_incidence_le {N n m p q : ℕ} {k : Root} {τ : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c)
    (hq : q ∈ originalReceiver N p) :
    receiptIncidence (cellQ N n c.1) q (rootHistory N n k τ p) ≤ treeBudget 430 := by
  apply (map_sum_le_mass _ _ _
    (fun o ho => receiptPoint_le hN hτ hτ' hn hp ho hq)).trans
  exact allowed_history_mass N q.primeFactors (rootQ N n k τ p) 430
    (rootRequest N n k τ p) (original_receipt_primeFactors_le hN hq)

private theorem map_sum_congr {A : Type*} (xs : List A) (f g : A → ℝ)
    (h : ∀ x ∈ xs, f x = g x) : (xs.map f).sum = (xs.map g).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      exact congrArg₂ (·+·) (h x (List.mem_cons_self ..))
        (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem list_finset_swap {A B : Type*} [DecidableEq B]
    (xs : List A) (S : Finset B) (f : A → B → ℝ) :
    (xs.map (fun x => ∑ y ∈ S, f x y)).sum = ∑ y ∈ S, (xs.map (fun x => f x y)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]

/-- Complete selected feedback history, but with the actual original
rootMask at every receiver.  The physical Q stays inside its root key. -/
def compatibleTotal (N n m : ℕ) (k : Root) (τ : ℝ) (c : RootKey n m) (p : ℕ) : ℝ :=
  ((rootHistory N n k τ p).map (fun o => mark o *
    (frozenCount N (parentProduct o.current.old) (rootMask N p)
      (memberCutoff (cellQ N n c.1) o) : ℝ))).sum

theorem compatibleTotal_on_receipts {N n m p : ℕ} {k : Root} {τ : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c) :
    compatibleTotal N n m k τ c p = ∑ q ∈ originalReceiver N p,
      receiptIncidence (cellQ N n c.1) q (rootHistory N n k τ p) := by
  unfold compatibleTotal receiptIncidence
  rw [← list_finset_swap]
  apply map_sum_congr
  intro o ho
  rw [owned_member_masked_count hN hτ hτ' hn hp ho]
  unfold receiptPoint
  rw [← Finset.sum_filter]
  simp only [originalReceiptLane,Finset.sum_const,nsmul_eq_mul]
  ring

/-- All compatible fresh descendants are paid against the actual root
receipt count.  This theorem holds for either original root tag. -/
theorem compatibleTotal_le_root {N n m p : ℕ} {k : Root} {τ : ℝ}
    {c : RootKey n m} (hN : 2 ≤ N) (hτ : 0 ≤ τ) (hτ' : τ ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384) (hp : p ∈ rootFibre N n m k τ c) :
    compatibleTotal N n m k τ c p ≤ treeBudget 430 * ((originalReceiver N p).card:ℝ) := by
  rw [compatibleTotal_on_receipts hN hτ hτ' hn hp]
  calc
    _ ≤ ∑ q ∈ originalReceiver N p, treeBudget 430 := Finset.sum_le_sum
      (fun q hq => actual_receipt_incidence_le hN hτ hτ' hn hp hq)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- Arithmetic payment of EVERY original-compatible emitted receiver at
every actual feedback-history position over the classical U3 band.
The threshold is chosen before n and m.  No count, incidence-budget or
descendant-to-root-theta inequality is assumed. -/
theorem actual_compatible_classical_history_paid {τ ε : ℝ}
    (hτ : 0 < τ) (hτ' : τ ≤ 1/12) (he : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, Even N → ∀ n m : ℕ, 1/((n:ℝ)+1) ≤ 11/384 →
      (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        compatibleTotal N n m .U3 τ c p) ≤
          treeBudget 430*(1+ε)*classicalOwnTheta N n m τ := by
  filter_upwards [classical_original_card_bound hτ hτ' he,
    eventually_ge_atTop (2:ℕ)] with N hd hN
  intro hEven n m hn
  have hsum : (∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
      compatibleTotal N n m .U3 τ c p) ≤
      ∑ c : RootKey n m, ∑ p ∈ classicalFibre N n m τ c,
        treeBudget 430*((originalReceiver N p).card:ℝ) := by
    apply Finset.sum_le_sum
    intro c _
    exact Finset.sum_le_sum (fun p hp => compatibleTotal_le_root hN hτ.le hτ' hn
      (classicalFibre_subset_rootFibre c hp))
  rw [sum_classicalFibre,← Finset.mul_sum] at hsum
  rw [classicalOwnTheta_eq hN hτ.le hτ' hn]
  exact hsum.trans ((mul_le_mul_of_nonneg_left (hd hEven n hn)
    (treeBudget_nonneg 430)).trans_eq (by ring))

end
end ImbalancedChen.Part5OriginalH430CompatibleHistoryPayment
