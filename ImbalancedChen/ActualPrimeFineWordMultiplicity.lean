import ImbalancedChen.ActualPrimeFineLabelSortedSelector

/-!
# Literal multiplicities of the original weakly ordered label word

Run-length blocks are computed from the original word. They reconstruct
it exactly; weakly decreasing labels give strictly decreasing block
labels. Their factorial product is exactly the product, over labels
present in the original word, of the factorial of its occurrence count.

The original squarefree tuple coefficient and signed scalar identities
therefore use the original word and its literal multiplicity directly.
No caller supplies a block decomposition or fibre multiplicity licence.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

def actualPrimeFineLabelBlocksOfWord : List ℕ → List (ℕ × ℕ)
  | [] => []
  | i :: input =>
      match actualPrimeFineLabelBlocksOfWord input with
      | [] => [(i, 1)]
      | (j, m) :: blocks =>
          if i = j then (j, m + 1) :: blocks else (i, 1) :: (j, m) :: blocks

theorem actualPrimeFineLabelBlocksOfWord_word (input : List ℕ) :
    actualPrimeLabelBlocksWord (actualPrimeFineLabelBlocksOfWord input) = input := by
  induction input with
  | nil => rfl
  | cons i input ih =>
      cases hb : actualPrimeFineLabelBlocksOfWord input with
      | nil =>
          have hnil : input = [] := by
            rw [hb] at ih
            exact ih.symm
          subst input
          rfl
      | cons b blocks =>
          rcases b with ⟨j, m⟩
          have htail : List.replicate m j ++ actualPrimeLabelBlocksWord blocks = input := by
            rw [hb] at ih
            exact ih
          rw [actualPrimeFineLabelBlocksOfWord, hb]
          by_cases hij : i = j
          · rw [if_pos hij]
            subst i
            change j :: (List.replicate m j ++ actualPrimeLabelBlocksWord blocks) = j :: input
            exact congrArg (List.cons j) htail
          · rw [if_neg hij]
            change i :: (List.replicate m j ++ actualPrimeLabelBlocksWord blocks) = i :: input
            exact congrArg (List.cons i) htail

theorem actualPrimeFineLabelBlocksOfWord_positive (input : List ℕ) :
    ∀ b ∈ actualPrimeFineLabelBlocksOfWord input, 0 < b.2 := by
  induction input with
  | nil => simp [actualPrimeFineLabelBlocksOfWord]
  | cons i input ih =>
      cases hb : actualPrimeFineLabelBlocksOfWord input with
      | nil => simp [actualPrimeFineLabelBlocksOfWord, hb]
      | cons b blocks =>
          rcases b with ⟨j, m⟩
          have hprev : ∀ b ∈ (j, m) :: blocks, 0 < b.2 := by simpa only [hb] using ih
          rw [actualPrimeFineLabelBlocksOfWord, hb]
          by_cases hij : i = j
          · rw [if_pos hij]
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact Nat.succ_pos m
            · exact hprev b (List.mem_cons_of_mem _ hb)
          · rw [if_neg hij]
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · decide
            · exact hprev b hb

theorem actualPrimeLabelBlocksWord_label_mem (blocks : List (ℕ × ℕ))
    (hpositive : ∀ b ∈ blocks, 0 < b.2) (b : ℕ × ℕ) (hb : b ∈ blocks) :
    b.1 ∈ actualPrimeLabelBlocksWord blocks := by
  exact List.mem_flatMap.mpr ⟨b, hb,
    List.mem_replicate.mpr ⟨Nat.ne_of_gt (hpositive b hb), rfl⟩⟩

/-- Weak labels in the actual original word supply strictly decreasing
distinct block labels; this order is not a caller decomposition licence. -/
theorem actualPrimeFineLabelBlocksOfWord_order (input : List ℕ)
    (horder : input.Pairwise (· ≥ ·)) :
    (actualPrimeFineLabelBlocksOfWord input).Pairwise (fun b c => c.1 < b.1) := by
  induction input with
  | nil => simp [actualPrimeFineLabelBlocksOfWord]
  | cons i input ih =>
      obtain ⟨hcross, htail⟩ := List.pairwise_cons.mp horder
      have hprev := ih htail
      cases hb : actualPrimeFineLabelBlocksOfWord input with
      | nil => simp [actualPrimeFineLabelBlocksOfWord, hb]
      | cons b blocks =>
          rcases b with ⟨j, m⟩
          have hprev' : ((j, m) :: blocks).Pairwise (fun b c => c.1 < b.1) := by
            simpa only [hb] using hprev
          have hjmem : j ∈ input := by
            rw [← actualPrimeFineLabelBlocksOfWord_word input]
            apply actualPrimeLabelBlocksWord_label_mem _
              (actualPrimeFineLabelBlocksOfWord_positive input) (j, m)
            rw [hb]
            exact List.mem_cons_self
          have hji : j ≤ i := hcross j hjmem
          rw [actualPrimeFineLabelBlocksOfWord, hb]
          by_cases hij : i = j
          · rw [if_pos hij]
            obtain ⟨hhead, hrest⟩ := List.pairwise_cons.mp hprev'
            exact List.pairwise_cons.mpr ⟨fun b hb => hhead b hb, hrest⟩
          · rw [if_neg hij]
            have hji' : j < i := by omega
            apply List.pairwise_cons.mpr
            refine ⟨?_, hprev'⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb
            · exact hji'
            · exact ((List.pairwise_cons.mp hprev').1 b hb).trans hji'

theorem actualPrimeLabelBlocksWord_count (blocks : List (ℕ × ℕ))
    (hlabels : blocks.Pairwise (fun b c => b.1 ≠ c.1)) :
    ∀ b ∈ blocks, (actualPrimeLabelBlocksWord blocks).count b.1 = b.2 := by
  induction blocks with
  | nil => simp
  | cons a blocks ih =>
      obtain ⟨hcross, htail⟩ := List.pairwise_cons.mp hlabels
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have hnot : a.1 ∉ actualPrimeLabelBlocksWord blocks := by
          intro hi
          obtain ⟨c, hc, heq⟩ := actualPrimeLabelBlocksWord_mem hi
          exact hcross c hc heq
        change (List.replicate a.2 a.1 ++ actualPrimeLabelBlocksWord blocks).count a.1 = a.2
        rw [List.count_append, List.count_replicate_self, List.count_eq_zero.mpr hnot, Nat.add_zero]
      · have hzero : (List.replicate a.2 a.1).count b.1 = 0 :=
          List.count_eq_zero.mpr (fun h => hcross b hb (List.mem_replicate.mp h).2.symm)
        change (List.replicate a.2 a.1 ++ actualPrimeLabelBlocksWord blocks).count b.1 = b.2
        rw [List.count_append, hzero, Nat.zero_add, ih htail b hb]

theorem actualPrimeLabelBlocksFactorial_eq_wordCounts (blocks : List (ℕ × ℕ))
    (hpositive : ∀ b ∈ blocks, 0 < b.2)
    (hlabels : blocks.Pairwise (fun b c => b.1 ≠ c.1)) :
    actualPrimeLabelBlocksFactorial blocks =
      ∏ i ∈ (actualPrimeLabelBlocksWord blocks).toFinset,
        ((actualPrimeLabelBlocksWord blocks).count i).factorial := by
  have hnodup : (blocks.map Prod.fst).Nodup := by
    change (blocks.map Prod.fst).Pairwise (· ≠ ·)
    exact List.pairwise_map.mpr hlabels
  have hlabelsSet : (blocks.map Prod.fst).toFinset =
      (actualPrimeLabelBlocksWord blocks).toFinset := by
    ext i
    constructor
    · intro hi
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hi)
      exact List.mem_toFinset.mpr (actualPrimeLabelBlocksWord_label_mem blocks hpositive b hb)
    · intro hi
      obtain ⟨b, hb, heq⟩ := actualPrimeLabelBlocksWord_mem (List.mem_toFinset.mp hi)
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨b, hb, heq.symm⟩)
  calc
    _ = (blocks.map (fun b => ((actualPrimeLabelBlocksWord blocks).count b.1).factorial)).prod := by
      unfold actualPrimeLabelBlocksFactorial
      congr 1
      apply List.map_congr_left
      intro b hb
      rw [actualPrimeLabelBlocksWord_count blocks hlabels b hb]
    _ = ((blocks.map Prod.fst).map
        (fun i => ((actualPrimeLabelBlocksWord blocks).count i).factorial)).prod := by
      rw [List.map_map]
    _ = (blocks.map Prod.fst).toFinset.prod
        (fun i => ((actualPrimeLabelBlocksWord blocks).count i).factorial) :=
      (List.prod_toFinset _ hnodup).symm
    _ = _ := by rw [hlabelsSet]

/-- The original `M_J`, using the occurrence counts of the original word. -/
def actualPrimeFineWordMultiplicity (input : List ℕ) : ℕ :=
  ∏ i ∈ input.toFinset, (input.count i).factorial

theorem actualPrimeFineLabelBlocksOfWord_factorial (input : List ℕ)
    (horder : input.Pairwise (· ≥ ·)) :
    actualPrimeLabelBlocksFactorial (actualPrimeFineLabelBlocksOfWord input) =
      actualPrimeFineWordMultiplicity input := by
  rw [actualPrimeLabelBlocksFactorial_eq_wordCounts _
    (actualPrimeFineLabelBlocksOfWord_positive input)
    ((actualPrimeFineLabelBlocksOfWord_order input horder).imp (fun h => Nat.ne_of_gt h)),
    actualPrimeFineLabelBlocksOfWord_word]
  rfl

/-- Literal original-word multiplicity and original sorted squarefree
selector, without a supplied run-length decomposition or fibre identity. -/
theorem actualPrimeFineWord_literal_multiplicity {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (input : List ℕ) (horder : input.Pairwise (· ≥ ·)) (n : ℕ) :
    (if Squarefree n then (actualPrimeTupleCoefficient
        (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input) n : ℝ) else 0) =
      (actualPrimeFineWordMultiplicity input : ℝ) *
        (if n ∈ ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input).filter
          List.SortedGT).image List.prod then 1 else 0) := by
  have h := actualPrimeFineLabelSorted_literal_multiplicity hN hτ
    (actualPrimeFineLabelBlocksOfWord input) (actualPrimeFineLabelBlocksOfWord_order input horder) n
  simpa only [actualPrimeFineLabelBlocksOfWord_word,
    actualPrimeFineLabelBlocksOfWord_factorial input horder,
    actualPrimeFineLabelSortedIndicator, actualPrimeFineLabelSortedProducts,
    actualPrimeFineLabelSortedTuples] using h

theorem actualPrimeFineWord_original_scalar {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (input : List ℕ) (horder : input.Pairwise (· ≥ ·))
    (r : ℕ) (c : ℝ) (H : ℕ → ℝ) :
    (c / (actualPrimeFineWordMultiplicity input : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input,
          (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) =
      c * ∑ n ∈ ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) input).filter
        List.SortedGT).image List.prod,
        (ArithmeticFunction.moebius (r * n) : ℝ) * H n := by
  have h := actualPrimeFineLabelSorted_original_scalar hN hτ
    (actualPrimeFineLabelBlocksOfWord input) (actualPrimeFineLabelBlocksOfWord_order input horder) r c H
  simpa only [actualPrimeFineLabelBlocksOfWord_word,
    actualPrimeFineLabelBlocksOfWord_factorial input horder,
    actualPrimeFineLabelSortedProducts, actualPrimeFineLabelSortedTuples] using h

end

end ImbalancedChen
