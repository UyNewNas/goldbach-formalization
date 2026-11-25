import ImbalancedChen.P2Saving16NegativeFiniteCore

/-!
SOURCE_ONLY / NOT COMPILED / UNEVALUATED.

The fourteen original saving16 cells partition their selected negative-inner
pair occurrences at one common positive trim width. Every actual (s,d) pair,
its full product, and its signed beta-minus coefficient are retained. The
remaining original carrier is kept once, with the original negativeTest.

This is a finite set and signed-sum identity. It supplies no PP estimate,
corner schedule, new saving, or bound for the untouched complement.
-/
namespace ImbalancedChen.P2Saving16FourteenNegativeFibrePartition

noncomputable section

open scoped Classical BigOperators
open Set
open P4AUpperTaggedParityCompiler P4AUpperTaggedBetaAttachment
open P2Saving16SignedCorrectionFamilies P2Saving16NegativeOriginalFibreSum
open P2OriginalSaving16Full87SourceBinding (sourceCell)

/-- The original pair occurrences selected by at least one of the fourteen
cells. The full rough word is retained; only the cell index is forgotten. -/
def selected14 (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion (selected ret tag N cap w z tau delta)

/-- Every original pair outside the union remains in one complement. -/
def complement14 (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) : Finset (ℕ × ℕ) :=
  (smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z)).filter
    (fun x => x ∉ selected14 ret tag N cap w z tau delta)

theorem mem_selected14 (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (x : ℕ × ℕ) :
    x ∈ selected14 ret tag N cap w z tau delta ↔
      ∃ i : Fin 14, x ∈ selected ret tag N cap w z tau delta i := by
  simp only [selected14, Finset.mem_biUnion, Finset.mem_univ, true_and]

/-- Positive trim width gives strict original source membership, so an
actual pair cannot be selected by two distinct original source cells. -/
theorem selected_disjoint (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (hdelta : 0 < delta)
    (i j : Fin 14) (hij : i ≠ j) :
    Disjoint (selected ret tag N cap w z tau delta i)
      (selected ret tag N cap w z tau delta j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hi := (Finset.mem_filter.mp hx).2.2.1
  have hj := (Finset.mem_filter.mp hy).2.2.1
  have hcell := P4AOriginalFull87Ownership.source_owner_unique
    (P4AOriginalFull87StrictActionTrim.trim_subset_source (sourceCell i) hdelta hi)
    (P4AOriginalFull87StrictActionTrim.trim_subset_source (sourceCell j) hdelta hj)
  apply hij
  simpa only [sourceCell, P4AOriginalFull87SourceDictionary.Cell.remaining.injEq,
    P4AOriginalRemainingEighthSources.Cell.ascending.injEq] using hcell

theorem selected_pairwise_disjoint
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (hdelta : 0 < delta) :
    (↑(Finset.univ : Finset (Fin 14)) : Set (Fin 14)).PairwiseDisjoint
      (selected ret tag N cap w z tau delta) := by
  intro i _ j _ hij
  exact selected_disjoint ret tag N cap w z tau delta hdelta i j hij

theorem selected14_subset_carrier
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) :
    selected14 ret tag N cap w z tau delta ⊆
      smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z) := by
  intro x hx
  obtain ⟨i, hi⟩ := (mem_selected14 ret tag N cap w z tau delta x).mp hx
  exact (Finset.mem_filter.mp hi).1

theorem selected14_negativeTest
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) {x : ℕ × ℕ}
    (hx : x ∈ selected14 ret tag N cap w z tau delta) :
    negativeTest ret tag N cap w z tau x.2 := by
  obtain ⟨i, hi⟩ := (mem_selected14 ret tag N cap w z tau delta x).mp hx
  exact (Finset.mem_filter.mp hi).2.2.2

theorem selected14_disjoint_complement14
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) :
    Disjoint (selected14 ret tag N cap w z tau delta)
      (complement14 ret tag N cap w z tau delta) := by
  apply Finset.disjoint_left.mpr
  intro x hx hc
  exact (Finset.mem_filter.mp hc).2 hx

theorem selected14_union_complement14
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) :
    selected14 ret tag N cap w z tau delta ∪
        complement14 ret tag N cap w z tau delta =
      smallRoughPairs (actualSmallRosserSupport N cap w) («universe» N cap w z) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hs | hc
    · exact selected14_subset_carrier ret tag N cap w z tau delta hs
    · exact (Finset.mem_filter.mp hc).1
  · intro hx
    by_cases hs : x ∈ selected14 ret tag N cap w z tau delta
    · exact Finset.mem_union.mpr (Or.inl hs)
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hs⟩))

/-- This equality counts every selected (s,d) exactly once, even when
distinct full rough words have the same ordered eight-prefix. -/
theorem selected14_sum_eq_sum_selected
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) (hdelta : 0 < delta)
    (F : ℕ × ℕ → ℝ) :
    (∑ x ∈ selected14 ret tag N cap w z tau delta, F x) =
      ∑ i : Fin 14, ∑ x ∈ selected ret tag N cap w z tau delta i, F x := by
  unfold selected14
  exact Finset.sum_biUnion
    (selected_pairwise_disjoint ret tag N cap w z tau delta hdelta)

theorem selected14_negativeTerm_sum
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (hdelta : 0 < delta) (G : ℕ → ℝ) :
    (∑ x ∈ selected14 ret tag N cap w z tau delta,
      negativeTerm ret tag N cap w z tau L G x) =
      ∑ i : Fin 14, selectedSum ret tag N cap w z tau delta L i G := by
  rw [selected14_sum_eq_sum_selected ret tag N cap w z tau delta hdelta]
  apply Finset.sum_congr rfl
  intro i _
  unfold selectedSum
  apply Finset.sum_congr rfl
  intro x hx
  have htest : negativeTest ret tag N cap w z tau x.2 :=
    (Finset.mem_filter.mp hx).2.2.2
  simp only [negativeTerm, if_pos htest]

/-- The original negative-inner sum is split once. Its entire complement
keeps the original negativeTest, signed coefficient and full product. -/
theorem negativeInner_exact_split14
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (hdelta : 0 < delta) (G : ℕ → ℝ) :
    negativeInnerSum ret tag N cap w z tau L G =
      (∑ i : Fin 14, selectedSum ret tag N cap w z tau delta L i G) +
        ∑ x ∈ complement14 ret tag N cap w z tau delta,
          negativeTerm ret tag N cap w z tau L G x := by
  calc
    negativeInnerSum ret tag N cap w z tau L G =
        ∑ x ∈ selected14 ret tag N cap w z tau delta ∪
            complement14 ret tag N cap w z tau delta,
          negativeTerm ret tag N cap w z tau L G x := by
      rw [selected14_union_complement14 ret tag N cap w z tau delta]
      rfl
    _ = (∑ x ∈ selected14 ret tag N cap w z tau delta,
          negativeTerm ret tag N cap w z tau L G x) +
        ∑ x ∈ complement14 ret tag N cap w z tau delta,
          negativeTerm ret tag N cap w z tau L G x :=
      Finset.sum_union (selected14_disjoint_complement14 ret tag N cap w z tau delta)
    _ = _ := by
      rw [selected14_negativeTerm_sum ret tag N cap w z tau delta L hdelta G]

/-- Product uniqueness holds on the original small/rough carrier and
therefore on its fourteen-cell union, without an extra geometric premise. -/
theorem selected14_full_modulus_injective
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ)
    {x y : ℕ × ℕ} (hx : x ∈ selected14 ret tag N cap w z tau delta)
    (hy : y ∈ selected14 ret tag N cap w z tau delta)
    (hxy : x.1 * x.2 = y.1 * y.2) : x = y := by
  have hx' := Finset.mem_product.mp
    (selected14_subset_carrier ret tag N cap w z tau delta hx)
  have hy' := Finset.mem_product.mp
    (selected14_subset_carrier ret tag N cap w z tau delta hy)
  have h := product_unique N cap w z hx'.1 hx'.2 hy'.1 hy'.2 hxy
  exact Prod.ext h.1 h.2

theorem selected14_term_is_actual_compiler_difference
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (G : ℕ → ℝ)
    {x : ℕ × ℕ} (hx : x ∈ selected14 ret tag N cap w z tau delta) :
    (rho ret tag N cap w z tau L (x.1 * x.2) -
      actualSmallRoughRho ret N cap w z L (x.1 * x.2)) * G (x.1 * x.2) =
      actualSmallRosserMinus N cap w L x.1 * G (x.1 * x.2) := by
  obtain ⟨i, hi⟩ := (mem_selected14 ret tag N cap w z tau delta x).mp hx
  exact selected_term_is_actual_compiler_difference ret tag N cap w z tau delta L i G hi

theorem selected14_moduli_subset_Q
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta : ℝ) :
    (selected14 ret tag N cap w z tau delta).image (fun x => x.1 * x.2) ⊆
      support N cap w z := by
  intro m hm
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨i, hi⟩ := (mem_selected14 ret tag N cap w z tau delta x).mp hx
  exact selected_moduli_subset_Q ret tag N cap w z tau delta i
    (Finset.mem_image.mpr ⟨x, hi, rfl⟩)

/-- The selected correction at the actual full-modulus image equals the
fourteen pair sums. The image is used only after product injectivity. -/
theorem selected14Sum_eq_full_Q_correction
    (ret : List ℕ → Bool) (tag : ℕ → List Bool)
    (N cap : ℕ) (w z tau delta L : ℝ) (hdelta : 0 < delta) (G : ℕ → ℝ) :
    (∑ m ∈ (selected14 ret tag N cap w z tau delta).image (fun x => x.1 * x.2),
      (rho ret tag N cap w z tau L m - actualSmallRoughRho ret N cap w z L m) * G m) =
      ∑ i : Fin 14, selectedSum ret tag N cap w z tau delta L i G := by
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2)
      (selected14 ret tag N cap w z tau delta) := by
    intro x hx y hy hxy
    exact selected14_full_modulus_injective ret tag N cap w z tau delta hx hy hxy
  rw [Finset.sum_image hinj]
  calc
    (∑ x ∈ selected14 ret tag N cap w z tau delta,
        (rho ret tag N cap w z tau L (x.1 * x.2) -
          actualSmallRoughRho ret N cap w z L (x.1 * x.2)) * G (x.1 * x.2)) =
        ∑ x ∈ selected14 ret tag N cap w z tau delta,
          actualSmallRosserMinus N cap w L x.1 * G (x.1 * x.2) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact selected14_term_is_actual_compiler_difference
        ret tag N cap w z tau delta L G hx
    _ = _ := by
      simpa only [selectedSum] using
        selected14_sum_eq_sum_selected ret tag N cap w z tau delta hdelta
          (fun x => actualSmallRosserMinus N cap w L x.1 * G (x.1 * x.2))

end
end ImbalancedChen.P2Saving16FourteenNegativeFibrePartition
