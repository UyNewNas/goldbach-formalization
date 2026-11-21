import ImbalancedChen.Part5OriginalH430ReceiptPrimeBudget

/-! A receiver-specific count of the LITERAL selected child row.
All singleton/pair carrier points and all W2 piece labels remain.
The budget is not a theta/model integral or a per-path mark bound. -/
namespace ImbalancedChen.Part5OriginalH430FreshBranchIncidence
noncomputable section
open Finset
open scoped Classical BigOperators
open P2Selected430CausalOccurrenceExporter (iterate roundDecision Choice)
open P5OriginalActionMassBound (Original106Action)
open P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430IntegerItineraries

def Allowed {N : ℕ} (P : Finset ℕ) (e : Edge N) : Prop :=
  ∀ q ∈ appendedWord (edgeShape e) (edgePrimes e), q ∈ P

def edgeCharge {N : ℕ} (P : Finset ℕ) (e : Edge N) : ℝ :=
  if Allowed P e then edgeWeight e else 0

def edgeSum {N : ℕ} (P : Finset ℕ) (es : List (Edge N)) : ℝ :=
  (es.map (edgeCharge P)).sum

theorem edgeCharge_nonneg {N : ℕ} (P : Finset ℕ) (e : Edge N) :
    0 ≤ edgeCharge P e := by
  unfold edgeCharge
  split_ifs
  · exact (edgeWeight_pos e).le
  · exact le_rfl

private theorem sum_toList {A : Type*} [DecidableEq A] (S : Finset A) (f : A → ℝ) :
    (S.toList.map f).sum = ∑ x ∈ S, f x := by
  simpa using (List.sum_toFinset f (show S.toList.Nodup by simp)).symm

private theorem single_card {N : ℕ} (P : Finset ℕ) (S : Finset (Fin (N+1))) :
    (S.filter (fun x => x.val ∈ P)).card ≤ P.card := by
  let T := S.filter (fun x => x.val ∈ P)
  have hinj : (T.image (fun x => x.val)).card = T.card :=
    Finset.card_image_of_injOn (fun x _ y _ h => Fin.ext h)
  have hsub : T.image (fun x => x.val) ⊆ P := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact (Finset.mem_filter.mp hx).2
  exact hinj.symm.le.trans (Finset.card_le_card hsub)

private theorem pair_card {N : ℕ} (P : Finset ℕ)
    (S : Finset (Fin (N+1) × Fin (N+1))) :
    (S.filter (fun x => x.1.val ∈ P ∧ x.2.val ∈ P)).card ≤ P.card*P.card := by
  let T := S.filter (fun x => x.1.val ∈ P ∧ x.2.val ∈ P)
  let f := fun x : Fin (N+1) × Fin (N+1) => (x.1.val,x.2.val)
  have hinj : (T.image f).card = T.card := by
    apply Finset.card_image_of_injOn
    intro x _ y _ h
    exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
  have hsub : T.image f ⊆ P ×ˢ P := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr (Finset.mem_filter.mp hx).2
  have hc := hinj.symm.le.trans (Finset.card_le_card hsub)
  simpa only [Finset.card_product] using hc

theorem single_sum {N : ℕ} (P : Finset ℕ) (S : Finset (Fin (N+1)))
    (w : ℝ) (hw : 0 ≤ w) :
    (S.toList.map (fun x => if x.val ∈ P then w else 0)).sum ≤ (P.card:ℝ)*w := by
  rw [sum_toList,← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast single_card P S) hw

theorem pair_sum {N : ℕ} (P : Finset ℕ)
    (S : Finset (Fin (N+1) × Fin (N+1))) (w : ℝ) (hw : 0 ≤ w) :
    (S.toList.map (fun x => if x.1.val ∈ P ∧ x.2.val ∈ P then w else 0)).sum ≤
      (P.card:ℝ)*(P.card:ℝ)*w := by
  rw [sum_toList,← Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast pair_card P S) hw

private theorem buchstab_sum (N : ℕ) (P : Finset ℕ) (Q : ℝ) (r : Request)
    (i : Fin 200) :
    edgeSum P (branchEdges N Q r i .buchstab) ≤ (P.card:ℝ) := by
  have h := single_sum P
    (singleChildren (.buchstab r.node.upper r.node.physical.argument)
      N Q r.old r.node.physical.ceiling) 1 zero_le_one
  cases hu : r.node.upper <;>
    simpa [edgeSum,branchEdges,List.map_map,Function.comp_def,edgeCharge,Allowed,
      edgeShape,edgePrimes,appendedWord,edgeWeight,hu] using h

private theorem w1_sum (N : ℕ) (P : Finset ℕ) (Q : ℝ) (r : Request)
    (i : Fin 7) (j : Fin 10) :
    edgeSum P (w1Edges N Q r i j) ≤ (P.card:ℝ)*(1/2) := by
  simpa [edgeSum,w1Edges,List.map_map,Function.comp_def,edgeCharge,Allowed,
    edgeShape,edgePrimes,appendedWord,edgeWeight] using
    single_sum P (singleChildren (.w1 i j) N Q r.old r.node.physical.ceiling)
      (1/2:ℝ) (by norm_num)

private theorem w2_single_sum (N : ℕ) (P : Finset ℕ) (Q : ℝ) (r : Request)
    (j : Fin 36) (k : Fin 3) :
    edgeSum P (w2SingleEdges N Q r j k) ≤ (P.card:ℝ)*(1/5) := by
  simpa [edgeSum,w2SingleEdges,List.map_map,Function.comp_def,edgeCharge,Allowed,
    edgeShape,edgePrimes,appendedWord,edgeWeight] using
    single_sum P (singleChildren (.w2 j k) N Q r.old r.node.physical.ceiling)
      (1/5:ℝ) (by norm_num)

private theorem w2_pair_sum (N : ℕ) (P : Finset ℕ) (Q : ℝ) (r : Request)
    (j : Fin 36) (k : Fin 4) :
    edgeSum P (w2PairEdges N Q r j k) ≤ (P.card:ℝ)*(P.card:ℝ)*(1/5) := by
  simpa [edgeSum,w2PairEdges,List.map_map,Function.comp_def,edgeCharge,Allowed,
    edgeShape,edgePrimes,appendedWord,edgeWeight,and_comm] using
    pair_sum P (pairChildren j k N Q r.old r.node.physical.ceiling)
      (1/5:ℝ) (by norm_num)

private theorem bank_sum (N : ℕ) (P : Finset ℕ) (Q : ℝ) (r : Request)
    (hP : P.card ≤ 11) (a : Original106Action) : edgeSum P (bankEdges N Q r a) ≤ 105 := by
  have hPr : (P.card:ℝ) ≤ 11 := by exact_mod_cast hP
  have hP2 : (P.card:ℝ)*(P.card:ℝ) ≤ 121 := by
    have hh := Nat.mul_le_mul hP hP
    exact_mod_cast hh
  cases a with
  | inl ij =>
      rcases ij with ⟨i,j⟩
      have h := w1_sum N P Q r i j
      have he : edgeSum P (bankEdges N Q r (.inl (i,j))) =
          1 + edgeSum P (w1Edges N Q r i j) := by
        simp [bankEdges,edgeSum,edgeCharge,Allowed,edgeShape,appendedWord,edgeWeight]
      rw [he]
      linarith only [h,hPr]
  | inr j =>
      have h0 := w2_single_sum N P Q r j 0
      have h1 := w2_single_sum N P Q r j 1
      have h2 := w2_single_sum N P Q r j 2
      have k0 := w2_pair_sum N P Q r j 0
      have k1 := w2_pair_sum N P Q r j 1
      have k2 := w2_pair_sum N P Q r j 2
      have k3 := w2_pair_sum N P Q r j 3
      have he : edgeSum P (bankEdges N Q r (.inr j)) = 1 +
          edgeSum P (w2SingleEdges N Q r j 0) + edgeSum P (w2SingleEdges N Q r j 1) +
          edgeSum P (w2SingleEdges N Q r j 2) + edgeSum P (w2PairEdges N Q r j 0) +
          edgeSum P (w2PairEdges N Q r j 1) + edgeSum P (w2PairEdges N Q r j 2) +
          edgeSum P (w2PairEdges N Q r j 3) := by
        norm_num [bankEdges,edgeSum,List.map_append,List.sum_append,
          edgeCharge,Allowed,edgeShape,appendedWord,edgeWeight]
      rw [he]
      linarith only [h0,h1,h2,k0,k1,k2,k3,hPr,hP2]

/-- Uniform in the actual request, Q, generation and N.  Different W2
pieces are separate terms, even if their integer primes coincide. -/
theorem actual_children_receipt_budget (N : ℕ) (P : Finset ℕ) (Q : ℝ)
    (g : ℕ) (r : Request) (hP : P.card ≤ 11) :
    edgeSum P (children N Q g r) ≤ 105 := by
  unfold children
  cases hi : resolve (g+1) r with
  | none => norm_num [edgeSum]
  | some i =>
      cases hc : (roundDecision (iterate g) r.node.upper i).choice with
      | retained => norm_num [branchEdges,edgeSum,edgeCharge,Allowed,
          edgeShape,appendedWord,edgeWeight]
      | buchstab =>
          exact (buchstab_sum N P Q r i).trans
            (by exact_mod_cast (show P.card ≤ 105 by omega))
      | bank k => exact bank_sum N P Q r hP _

end
end ImbalancedChen.Part5OriginalH430FreshBranchIncidence
