import ImbalancedChen.ActualPrimeDisjointLabelProducts

/-!
# The original sorted squarefree fine-label selector

Blocks are listed in decreasing fine-label order; repetitions within each
block give the original weakly ordered slot word. Sorting inside a block
preserves its actual prime interval. Different blocks already lie in
strictly separated half-open intervals. Thus every squarefree full product
has exactly one strictly decreasing representative in the original box.

The resulting indicator is the sorted squarefree prime-box selector. Its
literal multiplicity is the product of repeated-label factorials, and the
original full-product Mobius weight and fixed signed scalar are preserved.
This finite identity makes no arithmetic distribution or mean assertion.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

theorem actualPrimeSlotBox_replicate_sort {ι : Type*} (B : ι → Finset ℕ)
    (i : ι) (m : ℕ) (ps : List ℕ)
    (hps : ps ∈ actualPrimeSlotBox B (List.replicate m i)) :
    ps.mergeSort (· ≥ ·) ∈ actualPrimeSlotBox B (List.replicate m i) ∧
      (ps.mergeSort (· ≥ ·)).Perm ps ∧ (ps.mergeSort (· ≥ ·)).SortedGE := by
  have hmem := (mem_actualPrimeSlotBox_replicate (B i) m ps).mp
    ((actualPrimeSlotBox_replicate_label_eq B i m) ▸ hps)
  refine ⟨?_, List.mergeSort_perm ps _, List.sortedGE_mergeSort⟩
  rw [actualPrimeSlotBox_replicate_label_eq]
  apply (mem_actualPrimeSlotBox_replicate (B i) m _).mpr
  exact ⟨(List.mergeSort_perm ps _).length_eq.trans hmem.1,
    fun q hq => hmem.2 q ((List.mergeSort_perm ps _).mem_iff.mp hq)⟩

theorem actualPrimeFineLabelFinset_prime_lt {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) {i j p q : ℕ} (hji : j < i)
    (hp : p ∈ actualPrimeFineLabelFinset N τ i)
    (hq : q ∈ actualPrimeFineLabelFinset N τ j) : q < p := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hcast : (j : ℝ) + 1 ≤ (i : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hji
  have hsep := Real.rpow_le_rpow_of_exponent_le hNreal
    (mul_le_mul_of_nonneg_left hcast hτ)
  have hlt : (q : ℝ) < (p : ℝ) :=
    (mem_actualPrimeFineLabelFinset.mp hq).2.2.2.trans_le
      (hsep.trans (mem_actualPrimeFineLabelFinset.mp hp).2.2.1)
  exact_mod_cast hlt

/-- Sorting is performed inside the same original label blocks. There is
no caller premise that sorting preserves its fine-label box. -/
theorem actualPrimeFineLabelBlocks_sort {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ blocks : List (ℕ × ℕ), blocks.Pairwise (fun b c => c.1 < b.1) →
      ∀ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks),
      ∃ qs ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks), qs.Perm ps ∧ qs.SortedGE := by
  intro blocks
  induction blocks with
  | nil =>
      intro _horder ps hps
      have hnil : ps = [] := by simpa [actualPrimeLabelBlocksWord, actualPrimeSlotBox] using hps
      subst ps
      exact ⟨[], by simp [actualPrimeLabelBlocksWord, actualPrimeSlotBox], List.Perm.refl _, by simp⟩
  | cons b blocks ih =>
      rcases b with ⟨i, m⟩
      intro horder ps hps
      obtain ⟨hcross, htail⟩ := List.pairwise_cons.mp horder
      obtain ⟨as, has, bs, hbs, rfl⟩ :=
        (actualPrimeSlotBox_mem_append (actualPrimeFineLabelFinset N τ)
          (List.replicate m i) (actualPrimeLabelBlocksWord blocks) ps).mp hps
      obtain ⟨hcs, hcperm, hcsorted⟩ := actualPrimeSlotBox_replicate_sort
        (actualPrimeFineLabelFinset N τ) i m as has
      obtain ⟨ds, hds, hdperm, hdsorted⟩ := ih htail bs hbs
      let cs := as.mergeSort (· ≥ ·)
      refine ⟨cs ++ ds, ?_, hcperm.append hdperm, ?_⟩
      · exact (actualPrimeSlotBox_mem_append (actualPrimeFineLabelFinset N τ)
          (List.replicate m i) (actualPrimeLabelBlocksWord blocks) _).mpr
            ⟨cs, hcs, ds, hds, rfl⟩
      · apply List.Pairwise.sortedGE
        apply List.pairwise_append.mpr
        refine ⟨hcsorted.pairwise, hdsorted.pairwise, ?_⟩
        intro p hp q hq
        have hpi : p ∈ actualPrimeFineLabelFinset N τ i :=
          ((mem_actualPrimeSlotBox_replicate _ m cs).mp
            ((actualPrimeSlotBox_replicate_label_eq _ i m) ▸ hcs)).2 p hp
        have hbelow : ∀ q ∈ ds, q < p :=
          actualPrimeSlotBox_forall (actualPrimeFineLabelFinset N τ)
            (actualPrimeLabelBlocksWord blocks) (fun q => q < p) (by
              intro j hj q hq
              obtain ⟨b, hb, rfl⟩ := actualPrimeLabelBlocksWord_mem hj
              exact actualPrimeFineLabelFinset_prime_lt hN hτ (hcross b hb) hpi hq) ds hds
        exact (hbelow q hq).le

/-- This is the original strictly decreasing prime-box carrier. The
same target-divisor exclusions and half-open fine endpoints remain in its
underlying slot box. -/
def actualPrimeFineLabelSortedTuples (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ)) :
    Finset (List ℕ) :=
  (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
    (actualPrimeLabelBlocksWord blocks)).filter List.SortedGT

def actualPrimeFineLabelSortedProducts (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ)) :
    Finset ℕ :=
  (actualPrimeFineLabelSortedTuples N τ blocks).image List.prod

def actualPrimeFineLabelSortedIndicator (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (n : ℕ) : ℝ :=
  if n ∈ actualPrimeFineLabelSortedProducts N τ blocks then 1 else 0

theorem mem_actualPrimeFineLabelSortedProducts_iff {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ))
    (horder : blocks.Pairwise (fun b c => c.1 < b.1)) (n : ℕ) :
    n ∈ actualPrimeFineLabelSortedProducts N τ blocks ↔
      Squarefree n ∧ n ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks)).image List.prod := by
  constructor
  · intro hn
    obtain ⟨ps, hps, hprod⟩ := Finset.mem_image.mp hn
    obtain ⟨hbox, hsorted⟩ := Finset.mem_filter.mp hps
    refine ⟨?_, Finset.mem_image.mpr ⟨ps, hbox, hprod⟩⟩
    rw [← hprod]
    exact actualPrimeVector_squarefree ps
      (actualPrimeSlotBox_prime _ _ (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1)
        ps hbox) hsorted.nodup
  · rintro ⟨hsquarefree, hn⟩
    obtain ⟨ps, hps, hprod⟩ := Finset.mem_image.mp hn
    have hsquarefreeProd : Squarefree ps.prod := by
      simpa only [hprod] using hsquarefree
    have hnodup := actualPrimeVector_nodup_of_squarefree ps
      (actualPrimeSlotBox_prime _ _ (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1)
        ps hps) hsquarefreeProd
    obtain ⟨qs, hqs, hperm, hsorted⟩ := actualPrimeFineLabelBlocks_sort hN hτ blocks horder ps hps
    exact Finset.mem_image.mpr ⟨qs,
      Finset.mem_filter.mpr ⟨hqs, hsorted.sortedGT_of_nodup (hperm.nodup_iff.mpr hnodup)⟩,
      hperm.prod_eq.trans hprod⟩

theorem actualPrimeFineLabelSortedTuples_product_injective (N : ℕ) (τ : ℝ)
    (blocks : List (ℕ × ℕ)) :
    ∀ ps ∈ actualPrimeFineLabelSortedTuples N τ blocks,
      ∀ qs ∈ actualPrimeFineLabelSortedTuples N τ blocks,
        ps.prod = qs.prod → ps = qs := by
  intro ps hps qs hqs hprod
  obtain ⟨hpbox, hpsorted⟩ := Finset.mem_filter.mp hps
  obtain ⟨hqbox, hqsorted⟩ := Finset.mem_filter.mp hqs
  have hpprime := actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N τ) _
    (fun _ _ p hp => (mem_actualPrimeFineLabelFinset.mp hp).1) ps hpbox
  have hqprime := actualPrimeSlotBox_prime (actualPrimeFineLabelFinset N τ) _
    (fun _ _ q hq => (mem_actualPrimeFineLabelFinset.mp hq).1) qs hqbox
  have hperm := (Nat.primeFactorsList_unique hprod hpprime).trans
    (Nat.primeFactorsList_unique (rfl : qs.prod = qs.prod) hqprime).symm
  exact List.Perm.eq_of_sortedGE hpsorted.sortedGE hqsorted.sortedGE hperm

/-- Literal full-product Mobius normalization with the actual original
sorted selector, including the zero diagonal. -/
theorem actualPrimeFineLabelSorted_moebius_fibre {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ))
    (horder : blocks.Pairwise (fun b c => c.1 < b.1)) (r n : ℕ) :
    ((ArithmeticFunction.moebius (r * n) : ℝ) * actualPrimeTupleCoefficient
        (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (actualPrimeLabelBlocksWord blocks)) n) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      (ArithmeticFunction.moebius (r * n) : ℝ) *
        actualPrimeFineLabelSortedIndicator N τ blocks n := by
  rw [actualPrimeFineLabelBlocks_moebius_fibre hN hτ blocks r n
    (horder.imp (fun h => Nat.ne_of_gt h))]
  by_cases hn : n ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
      (actualPrimeLabelBlocksWord blocks)).image List.prod
  · by_cases hsquarefree : Squarefree n
    · have hsorted := (mem_actualPrimeFineLabelSortedProducts_iff hN hτ blocks horder n).mpr
        ⟨hsquarefree, hn⟩
      simp [hn, actualPrimeFineLabelSortedIndicator, hsorted]
    · have hzero := actualPrimeVector_moebius_mul_eq_zero (r := r) hsquarefree
      simp [hzero]
  · have hnot : n ∉ actualPrimeFineLabelSortedProducts N τ blocks :=
      fun h => hn ((mem_actualPrimeFineLabelSortedProducts_iff hN hτ blocks horder n).mp h).2
    simp [hn, actualPrimeFineLabelSortedIndicator, hnot]

/-- The original `1_squarefree T_J = M_J A_J` identity. The factorial
normalizes the actual original fibre; it does not remove a diagonal. -/
theorem actualPrimeFineLabelSorted_literal_multiplicity {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ))
    (horder : blocks.Pairwise (fun b c => c.1 < b.1)) (n : ℕ) :
    (if Squarefree n then (actualPrimeTupleCoefficient
        (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (actualPrimeLabelBlocksWord blocks)) n : ℝ) else 0) =
      (actualPrimeLabelBlocksFactorial blocks : ℝ) *
        actualPrimeFineLabelSortedIndicator N τ blocks n := by
  by_cases hsquarefree : Squarefree n
  · have hmu : (ArithmeticFunction.moebius n : ℝ) ≠ 0 := by
      exact_mod_cast (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsquarefree)
    have hfactor : (actualPrimeLabelBlocksFactorial blocks : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos blocks)
    have h := actualPrimeFineLabelSorted_moebius_fibre hN hτ blocks horder 1 n
    simp only [one_mul, mul_div_assoc] at h
    have hcoeff := mul_left_cancel₀ hmu h
    have hproduct := (div_eq_iff hfactor).mp hcoeff
    simpa only [if_pos hsquarefree, mul_comm] using hproduct
  · have hnot : n ∉ actualPrimeFineLabelSortedProducts N τ blocks :=
      fun h => hsquarefree ((mem_actualPrimeFineLabelSortedProducts_iff hN hτ blocks horder n).mp h).1
    simp [hsquarefree, actualPrimeFineLabelSortedIndicator, hnot]

/-- Exact original signed scalar and full Mobius sum over the actual
sorted squarefree product selector. Only a function of the full product
is transported across within-label permutations. -/
theorem actualPrimeFineLabelSorted_original_scalar {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ))
    (horder : blocks.Pairwise (fun b c => c.1 < b.1)) (r : ℕ) (c : ℝ) (H : ℕ → ℝ) :
    (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (actualPrimeLabelBlocksWord blocks),
          (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) =
      c * ∑ n ∈ actualPrimeFineLabelSortedProducts N τ blocks,
        (ArithmeticFunction.moebius (r * n) : ℝ) * H n := by
  rw [actualPrimeFineLabelBlocks_original_scalar hN hτ blocks r c H
    (horder.imp (fun h => Nat.ne_of_gt h))]
  have hselector : actualPrimeFineLabelSortedProducts N τ blocks =
      ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks)).image List.prod).filter Squarefree := by
    ext n
    rw [mem_actualPrimeFineLabelSortedProducts_iff hN hτ blocks horder n, Finset.mem_filter]
    exact and_comm
  rw [hselector, Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hsquarefree : Squarefree n
  · simp [hsquarefree]
  · simp [hsquarefree, actualPrimeVector_moebius_mul_eq_zero (r := r) hsquarefree]

end

end ImbalancedChen
