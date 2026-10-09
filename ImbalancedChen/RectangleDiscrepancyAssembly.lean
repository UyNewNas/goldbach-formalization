import ImbalancedChen.ActualGridEnvelopes
import ImbalancedChen.TotientReciprocalBudget

/-!
# Finite assembly of the actual prime-rectangle discrepancies

The rectangle discrepancy here is the literal count of ordered prime pairs
in one full grid rectangle, with the coprime pair count divided by `φ(d)`.
Disjoint ownership is used before taking products. Product fibres retain
their multiplicity, and the common carrier retains all exterior products.

The curved discrepancy is reduced to the sum of these actual rectangle
discrepancies plus an explicit boundary cost. This is a finite reduction,
not a prime-rectangle distribution theorem or an analytic supplier.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators

/-- Summing literal product fibres over a predicate counts exactly the
pairs whose product satisfies that predicate. The full image is retained. -/
theorem sum_pairProductWeight_filter
    (B : Finset (ℕ × ℕ)) (M : Finset ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hM : B.image (fun p => p.1 * p.2) ⊆ M) :
    (∑ m ∈ M with P m, pairProductWeight B m) =
      ((B.filter (fun p => P (p.1 * p.2))).card : ℝ) := by
  classical
  have hf : B.filter (fun p => p.1 * p.2 ∈ M.filter P) =
      B.filter (fun p => P (p.1 * p.2)) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1, h.2.2⟩
    · exact fun h => ⟨h.1, hM (Finset.mem_image_of_mem _ h.1), h.2⟩
  have hc := Finset.sum_card_fiberwise_eq_card_filter B (M.filter P)
    (fun p => p.1 * p.2)
  rw [hf] at hc
  unfold pairProductWeight
  exact_mod_cast hc

/-- A full rectangle's discrepancy is defined directly from its prime-pair
counts. No order restriction, curved cutoff, or arbitrary weight occurs. -/
def actualGridRectangleDiscrepancy (κ : ℝ) (ij : ℕ × ℕ) (a d : ℕ) : ℝ :=
  (((actualGridPrimeRectangle κ ij).filter
      (fun p => Nat.ModEq d (p.1 * p.2) a)).card : ℝ) -
    (((actualGridPrimeRectangle κ ij).filter
      (fun p => Nat.Coprime (p.1 * p.2) d)).card : ℝ) / (Nat.totient d : ℝ)

/-- Evaluation on any carrier containing the full rectangle product image
agrees with the literal pair-count discrepancy, including repeated products. -/
theorem finitePrimitiveDiscrepancy_actualGridPrimeRectangle
    (κ : ℝ) (ij : ℕ × ℕ) (M : Finset ℕ) (a d : ℕ)
    (hM : (actualGridPrimeRectangle κ ij).image (fun p => p.1 * p.2) ⊆ M) :
    finitePrimitiveDiscrepancy M (pairProductWeight (actualGridPrimeRectangle κ ij))
        a d = actualGridRectangleDiscrepancy κ ij a d := by
  unfold finitePrimitiveDiscrepancy finiteCongruenceMass finiteCoprimeMass
  rw [sum_pairProductWeight_filter _ _ _ hM,
    sum_pairProductWeight_filter _ _ _ hM]
  rfl

/-- Disjoint grid ownership makes the union's fibre weight exactly the sum
of rectangle fibre weights, without requiring injective multiplication. -/
theorem pairProductWeight_actualGridPrimePairs
    {κ : ℝ} (hκ : 1 < κ) (I : Finset (ℕ × ℕ)) (m : ℕ) :
    pairProductWeight (actualGridPrimePairs κ I) m =
      ∑ ij ∈ I, pairProductWeight (actualGridPrimeRectangle κ ij) m := by
  classical
  have hf : (actualGridPrimePairs κ I).filter (fun p => p.1 * p.2 = m) =
      I.biUnion (fun ij =>
        (actualGridPrimeRectangle κ ij).filter (fun p => p.1 * p.2 = m)) := by
    ext p
    simp only [actualGridPrimePairs, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨⟨ij, hij, hp⟩, hpm⟩
      exact ⟨ij, hij, hp, hpm⟩
    · rintro ⟨ij, hij, hp, hpm⟩
      exact ⟨⟨ij, hij, hp⟩, hpm⟩
  have hd : (I : Set (ℕ × ℕ)).PairwiseDisjoint (fun ij =>
      (actualGridPrimeRectangle κ ij).filter (fun p => p.1 * p.2 = m)) := by
    intro ij _ kl _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact Finset.disjoint_left.mp (actualGridPrimeRectangle_disjoint hκ hne)
      (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1
  have hc := Finset.card_biUnion hd
  unfold pairProductWeight
  rw [hf]
  exact_mod_cast hc

/-- The discrepancy of a grid family is exactly the sum of its actual
rectangle discrepancies on any carrier containing the family's full image. -/
theorem finitePrimitiveDiscrepancy_actualGridPrimePairs
    {κ : ℝ} (hκ : 1 < κ) (I : Finset (ℕ × ℕ)) (M : Finset ℕ) (a d : ℕ)
    (hM : (actualGridPrimePairs κ I).image (fun p => p.1 * p.2) ⊆ M) :
    finitePrimitiveDiscrepancy M (pairProductWeight (actualGridPrimePairs κ I)) a d =
      ∑ ij ∈ I, actualGridRectangleDiscrepancy κ ij a d := by
  have hw : pairProductWeight (actualGridPrimePairs κ I) =
      fun m => ∑ ij ∈ I, pairProductWeight (actualGridPrimeRectangle κ ij) m := by
    funext m
    exact pairProductWeight_actualGridPrimePairs hκ I m
  rw [hw, finitePrimitiveDiscrepancy_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  apply finitePrimitiveDiscrepancy_actualGridPrimeRectangle
  intro m hm
  obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp hm
  apply hM
  exact Finset.mem_image.mpr ⟨p, Finset.mem_biUnion.mpr ⟨ij, hij, hp⟩, hpm⟩

/-- Triangle inequality for the actual rectangle terms. -/
theorem abs_finitePrimitiveDiscrepancy_actualGridPrimePairs_le
    {κ : ℝ} (hκ : 1 < κ) (I : Finset (ℕ × ℕ)) (M : Finset ℕ) (a d : ℕ)
    (hM : (actualGridPrimePairs κ I).image (fun p => p.1 * p.2) ⊆ M) :
    |finitePrimitiveDiscrepancy M (pairProductWeight (actualGridPrimePairs κ I)) a d| ≤
      ∑ ij ∈ I, |actualGridRectangleDiscrepancy κ ij a d| := by
  rw [finitePrimitiveDiscrepancy_actualGridPrimePairs hκ I M a d hM]
  exact Finset.abs_sum_le_sum_abs _ _

/-- Every selected subfamily uses the same full upper-envelope carrier.
There is no restriction to products below the curved cutoff. -/
theorem actualGridPrimePairs_image_subset_carrier
    {num den N : ℕ} {T κ : ℝ} {I : Finset (ℕ × ℕ)}
    (hI : I ⊆ actualGridIntersectingIndices num den N T κ) :
    (actualGridPrimePairs κ I).image (fun p => p.1 * p.2) ⊆
      actualGridProductCarrier num den N T κ := by
  intro m hm
  obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp hm
  obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_image.mpr
    ⟨p, Finset.mem_biUnion.mpr ⟨ij, hI hij, hpij⟩, hpm⟩

/-- Exact discrepancy assembly for the literal lower envelope. -/
theorem finitePrimitiveDiscrepancy_actualGridLowerWeight
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (a d : ℕ) :
    finitePrimitiveDiscrepancy (actualGridProductCarrier num den N T κ)
        (actualGridLowerWeight num den N T κ) a d =
      ∑ ij ∈ actualGridInsideIndices num den N T κ,
        actualGridRectangleDiscrepancy κ ij a d := by
  classical
  apply finitePrimitiveDiscrepancy_actualGridPrimePairs hκ
  exact actualGridPrimePairs_image_subset_carrier (Finset.filter_subset _ _)

/-- Exact discrepancy assembly for the literal upper envelope. -/
theorem finitePrimitiveDiscrepancy_actualGridUpperWeight
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (a d : ℕ) :
    finitePrimitiveDiscrepancy (actualGridProductCarrier num den N T κ)
        (actualGridUpperWeight num den N T κ) a d =
      ∑ ij ∈ actualGridIntersectingIndices num den N T κ,
        actualGridRectangleDiscrepancy κ ij a d := by
  classical
  apply finitePrimitiveDiscrepancy_actualGridPrimePairs hκ
  exact actualGridPrimePairs_image_subset_carrier (fun _ h => h)

/-- The difference of the envelopes is exactly the sum over full boundary
rectangles. In particular, exterior prime pairs are not deleted. -/
theorem finitePrimitiveDiscrepancy_actualGridBoundaryWeight
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) (a d : ℕ) :
    finitePrimitiveDiscrepancy (actualGridProductCarrier num den N T κ)
        (fun m => actualGridUpperWeight num den N T κ m -
          actualGridLowerWeight num den N T κ m) a d =
      ∑ ij ∈ actualGridIntersectingIndices num den N T κ \
          actualGridInsideIndices num den N T κ,
        actualGridRectangleDiscrepancy κ ij a d := by
  simp_rw [actualGridUpperWeight_sub_lower]
  rw [actualGridBoundaryPairs_eq_union hκ]
  apply finitePrimitiveDiscrepancy_actualGridPrimePairs hκ
  exact actualGridPrimePairs_image_subset_carrier
    (fun _ h => (Finset.mem_sdiff.mp h).1)

/-- The two envelope families partition the selected rectangles. Hence
the transfer uses each rectangle once, with boundary constant one. -/
theorem abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) (hκ : 1 < κ) (d : ℕ) :
    |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| ≤
      (∑ ij ∈ actualGridIntersectingIndices num den N T κ,
        |actualGridRectangleDiscrepancy κ ij N d|) +
      finiteSourceMass (actualGridProductCarrier num den N T κ)
        (fun m => actualGridUpperWeight num den N T κ m -
          actualGridLowerWeight num den N T κ m) / (Nat.totient d : ℝ) := by
  classical
  have h := abs_halfProductPrimitiveDiscrepancy_le_actualGridEnvelopes
    (num := num) (N := N) (T := T) hden hκ d
  rw [finitePrimitiveDiscrepancy_actualGridLowerWeight hκ,
    finitePrimitiveDiscrepancy_actualGridBoundaryWeight hκ] at h
  have hl :
      |∑ ij ∈ actualGridInsideIndices num den N T κ,
        actualGridRectangleDiscrepancy κ ij N d| ≤
      ∑ ij ∈ actualGridInsideIndices num den N T κ,
        |actualGridRectangleDiscrepancy κ ij N d| :=
    Finset.abs_sum_le_sum_abs _ _
  have hb :
      |∑ ij ∈ actualGridIntersectingIndices num den N T κ \
          actualGridInsideIndices num den N T κ,
        actualGridRectangleDiscrepancy κ ij N d| ≤
      ∑ ij ∈ actualGridIntersectingIndices num den N T κ \
          actualGridInsideIndices num den N T κ,
        |actualGridRectangleDiscrepancy κ ij N d| :=
    Finset.abs_sum_le_sum_abs _ _
  have hs :
      (∑ ij ∈ actualGridIntersectingIndices num den N T κ \
          actualGridInsideIndices num den N T κ,
        |actualGridRectangleDiscrepancy κ ij N d|) +
      (∑ ij ∈ actualGridInsideIndices num den N T κ,
        |actualGridRectangleDiscrepancy κ ij N d|) =
      ∑ ij ∈ actualGridIntersectingIndices num den N T κ,
        |actualGridRectangleDiscrepancy κ ij N d| :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  linarith

/-- Summation over any finite moduli retains the actual rectangle terms.
The only additional cost is the boundary mass times the totient sum. -/
theorem sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) (hκ : 1 < κ)
    (S : Finset ℕ) :
    (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
      (∑ ij ∈ actualGridIntersectingIndices num den N T κ,
        ∑ d ∈ S, |actualGridRectangleDiscrepancy κ ij N d|) +
      finiteSourceMass (actualGridProductCarrier num den N T κ)
        (fun m => actualGridUpperWeight num den N T κ m -
          actualGridLowerWeight num den N T κ m) *
        (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) := by
  calc
    _ ≤ ∑ d ∈ S,
        ((∑ ij ∈ actualGridIntersectingIndices num den N T κ,
          |actualGridRectangleDiscrepancy κ ij N d|) +
        finiteSourceMass (actualGridProductCarrier num den N T κ)
          (fun m => actualGridUpperWeight num den N T κ m -
            actualGridLowerWeight num den N T κ m) / (Nat.totient d : ℝ)) :=
      Finset.sum_le_sum fun d _ =>
        abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles hden hκ d
    _ = _ := by
      rw [Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_comm
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        ring

/-- Fully explicit finite reduction for any selected positive moduli below
`D`. The remaining double sum contains only genuine full prime-rectangle
discrepancies. No distribution estimate is among the assumptions. -/
theorem sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles_log
    {num den N : ℕ} {T δ : ℝ} (hden : 0 < den)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hTN : T ≤ (N : ℝ))
    (hN : 1 ≤ (N : ℝ)) (hb1 : (num : ℝ) / (den : ℝ) ≤ 1)
    (S : Finset ℕ) (D : ℕ) (hS : S ⊆ Finset.Icc 1 D) :
    (∑ d ∈ S, |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)|) ≤
      (∑ ij ∈ actualGridIntersectingIndices num den N T (1 + δ),
        ∑ d ∈ S, |actualGridRectangleDiscrepancy (1 + δ) ij N d|) +
      4 * (12 * δ * N * Real.log (3 * N) + 216 * δ * N +
        14 * (N : ℝ) ^ (1 / (1 + (num : ℝ) / (den : ℝ)))) *
        (1 + Real.log (max 1 (D : ℝ))) := by
  have hκ : 1 < 1 + δ := by linarith
  have hm : 0 ≤ finiteSourceMass (actualGridProductCarrier num den N T (1 + δ))
      (fun m => actualGridUpperWeight num den N T (1 + δ) m -
        actualGridLowerWeight num den N T (1 + δ) m) := by
    rw [actualGrid_boundary_mass_eq_card]
    exact Nat.cast_nonneg _
  have hl : 0 ≤ 1 + Real.log (max 1 (D : ℝ)) := by
    have hlog := Real.log_nonneg (le_max_left (1 : ℝ) (D : ℝ))
    linarith
  have hrecip := mul_le_mul_of_nonneg_left
    (sum_reciprocal_totient_subset_le_log S D hS) hm
  have hboundary := mul_le_mul_of_nonneg_right
    (actualGrid_boundary_mass_le_explicit hden hδ hδ1 hT hTN hN hb1)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hl)
  have hcost :
      finiteSourceMass (actualGridProductCarrier num den N T (1 + δ))
        (fun m => actualGridUpperWeight num den N T (1 + δ) m -
          actualGridLowerWeight num den N T (1 + δ) m) *
        (∑ d ∈ S, 1 / (Nat.totient d : ℝ)) ≤
      4 * (12 * δ * N * Real.log (3 * N) + 216 * δ * N +
        14 * (N : ℝ) ^ (1 / (1 + (num : ℝ) / (den : ℝ)))) *
        (1 + Real.log (max 1 (D : ℝ))) := by
    calc
      _ ≤ _ := hrecip.trans hboundary
      _ = _ := by ring
  exact (sum_abs_halfProductPrimitiveDiscrepancy_le_actualGridRectangles hden hκ S).trans
    (add_le_add le_rfl hcost)

/-- The actual selected rectangles obey the proved finite logarithmic
index count; empty or exterior parts of their full cells are not removed. -/
theorem actualGridIntersectingIndices_card_le_log (num den N : ℕ) (T κ : ℝ) :
    (actualGridIntersectingIndices num den N T κ).card ≤
      (Nat.floor (Real.log (N : ℝ) / Real.log κ) + 1) ^ 2 := by
  exact multiplicativeGrid_subfamily_card_le (Finset.filter_subset _ _)

end

end ImbalancedChen
