import ImbalancedChen.MultiplicativeGridPartition
import ImbalancedChen.BoundaryGlobalCaps

/-!
# Literal finite prime-pair envelopes for the curved half-product source

The intersecting cells are the full grid rectangles containing at least one
actual source pair. An inside cell is an intersecting cell all of whose
natural points satisfy the real curved-region inequalities. Thus every
remaining cell has both a genuine inside witness and a genuine outside
witness. This integer-point version of inside is sufficient for prime
convolutions and for the real crossing-cell containment theorem.

Every prime pair in each selected rectangle is retained. In particular,
the upper envelope is not cut by the diagonal or by the product cutoff.
Its product fibres count multiplicity, while ordered factor uniqueness
identifies the actual source fibres with its indicator, including squares.
The common carrier is the full upper-envelope product image.

This is an exact finite construction and boundary-mass bridge. No prime
rectangle distribution estimate or target source-mass bound is assumed.
-/

namespace ImbalancedChen

noncomputable section

/-- A full rectangle of prime pairs, with no order or product restriction. -/
def actualGridPrimeRectangle (κ : ℝ) (ij : ℕ × ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact (multiplicativeGridRectangle κ ij).filter fun p =>
    Nat.Prime p.1 ∧ Nat.Prime p.2

/-- The rectangle really is a product of two interval-restricted prime sets. -/
theorem actualGridPrimeRectangle_eq_product (κ : ℝ) (ij : ℕ × ℕ) :
    actualGridPrimeRectangle κ ij =
      ((multiplicativeGridSide κ ij.1).filter Nat.Prime).product
        ((multiplicativeGridSide κ ij.2).filter Nat.Prime) := by
  classical
  ext p
  simp only [actualGridPrimeRectangle, multiplicativeGridRectangle,
    Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product]
  tauto

/-- Finite indices of cells with an actual prime-pair source witness. -/
def actualGridIntersectingIndices (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (multiplicativeGridIndices κ N).filter fun ij =>
    ∃ p ∈ halfProductPairs num den N T, p ∈ multiplicativeGridRectangle κ ij

/-- Inside means all natural points of the full cell satisfy the geometry,
not merely that all prime points happen to lie in the source. -/
def actualGridCellInside (num den N : ℕ) (T κ : ℝ) (ij : ℕ × ℕ) : Prop :=
  ∀ p ∈ multiplicativeGridRectangle κ ij,
    halfProductRealRegion T N ((num : ℝ) / (den : ℝ)) ((p.1 : ℝ), (p.2 : ℝ))

/-- Inside indices are selected from the intersecting family. -/
def actualGridInsideIndices (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact (actualGridIntersectingIndices num den N T κ).filter
    (actualGridCellInside num den N T κ)

/-- Union of full prime rectangles over a finite index family. -/
def actualGridPrimePairs (κ : ℝ) (I : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  I.biUnion (actualGridPrimeRectangle κ)

def actualGridLowerPairs (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) :=
  actualGridPrimePairs κ (actualGridInsideIndices num den N T κ)

def actualGridUpperPairs (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) :=
  actualGridPrimePairs κ (actualGridIntersectingIndices num den N T κ)

/-- Boundary pairs retain every exterior prime pair in a boundary rectangle. -/
def actualGridBoundaryPairs (num den N : ℕ) (T κ : ℝ) : Finset (ℕ × ℕ) :=
  actualGridUpperPairs num den N T κ \ actualGridLowerPairs num den N T κ

/-- The common carrier is not intersected with the original product cutoff. -/
def actualGridProductCarrier (num den N : ℕ) (T κ : ℝ) : Finset ℕ :=
  (actualGridUpperPairs num den N T κ).image (fun p => p.1 * p.2)

def actualGridLowerWeight (num den N : ℕ) (T κ : ℝ) : ℕ → ℝ :=
  pairProductWeight (actualGridLowerPairs num den N T κ)

def actualGridUpperWeight (num den N : ℕ) (T κ : ℝ) : ℕ → ℝ :=
  pairProductWeight (actualGridUpperPairs num den N T κ)

/-- The real geometric test is exactly the original source test on primes. -/
theorem halfProductPairs_iff_prime_realRegion
    {num den N : ℕ} {T : ℝ} {p : ℕ × ℕ} (hden : 0 < den) :
    p ∈ halfProductPairs num den N T ↔
      Nat.Prime p.1 ∧ Nat.Prime p.2 ∧
        halfProductRealRegion T N ((num : ℝ) / (den : ℝ))
          ((p.1 : ℝ), (p.2 : ℝ)) :=
  mem_halfProductPairs_iff_prime_realRegion hden

/-- Each actual pair is covered by one of the selected full prime rectangles. -/
theorem halfProductPairs_subset_actualGridUpperPairs
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) :
    halfProductPairs num den N T ⊆ actualGridUpperPairs num den N T κ := by
  classical
  intro p hp
  rcases p with ⟨r, q⟩
  obtain ⟨hr, hq, _, _, _, hN⟩ := mem_halfProductPairs.mp hp
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hrN : r ≤ N := (by
    simpa using Nat.mul_le_mul_left r hq1 : r ≤ r * q).trans hN
  have hqN : q ≤ N := (by
    simpa using Nat.mul_le_mul_right q hr1 : q ≤ r * q).trans hN
  obtain ⟨ij, hij, _⟩ := multiplicativeGrid_existsUnique_rectangle
    (N := (N : ℝ)) (p := (r, q)) hκ hr1 hq1
    (by exact_mod_cast hrN) (by exact_mod_cast hqN)
  apply Finset.mem_biUnion.mpr
  refine ⟨ij, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨hij.1, ⟨(r, q), hp, hij.2⟩⟩
  · exact Finset.mem_filter.mpr ⟨hij.2, hr, hq⟩

/-- No inside prime pair is added to the actual source. -/
theorem actualGridLowerPairs_subset_halfProductPairs
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) :
    actualGridLowerPairs num den N T κ ⊆ halfProductPairs num den N T := by
  classical
  intro p hp
  obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
  have hi := Finset.mem_filter.mp hij
  have hp' := Finset.mem_filter.mp hpij
  exact (halfProductPairs_iff_prime_realRegion hden).mpr
    ⟨hp'.2.1, hp'.2.2, hi.2 p hp'.1⟩

theorem actualGridLowerPairs_subset_upper
    (num den N : ℕ) (T κ : ℝ) :
    actualGridLowerPairs num den N T κ ⊆ actualGridUpperPairs num den N T κ := by
  classical
  intro p hp
  obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
  exact Finset.mem_biUnion.mpr ⟨ij, (Finset.mem_filter.mp hij).1, hpij⟩

/-- Distinct prime rectangles are disjoint before projection to products. -/
theorem actualGridPrimeRectangle_disjoint {κ : ℝ} (hκ : 1 < κ)
    {ij kl : ℕ × ℕ} (hne : ij ≠ kl) :
    Disjoint (actualGridPrimeRectangle κ ij) (actualGridPrimeRectangle κ kl) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp (multiplicativeGridRectangle_disjoint hκ hne)
    (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1

/-- Grid disjointness makes the pair difference exactly the union of the
boundary rectangles, with no arbitrary removal of their prime points. -/
theorem actualGridBoundaryPairs_eq_union
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) :
    actualGridBoundaryPairs num den N T κ = actualGridPrimePairs κ
      (actualGridIntersectingIndices num den N T κ \
        actualGridInsideIndices num den N T κ) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hu, hl⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hu
    apply Finset.mem_biUnion.mpr
    refine ⟨ij, Finset.mem_sdiff.mpr ⟨hij, ?_⟩, hpij⟩
    intro hi
    exact hl (Finset.mem_biUnion.mpr ⟨ij, hi, hpij⟩)
  · intro hp
    obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨hi, hni⟩ := Finset.mem_sdiff.mp hij
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_biUnion.mpr ⟨ij, hi, hpij⟩, ?_⟩
    intro hl
    obtain ⟨kl, hkl, hpkl⟩ := Finset.mem_biUnion.mp hl
    have heq : ij = kl :=
      (multiplicativeGridRectangle_index_eq hκ (Finset.mem_filter.mp hpij).1).symm.trans
        (multiplicativeGridRectangle_index_eq hκ (Finset.mem_filter.mp hpkl).1)
    exact hni (heq.symm ▸ hkl)

/-- Monotonicity for literal product fibres, without any injectivity premise. -/
theorem pairProductWeight_mono {A B : Finset (ℕ × ℕ)} (hAB : A ⊆ B) (m : ℕ) :
    pairProductWeight A m ≤ pairProductWeight B m := by
  classical
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  exact Finset.mem_filter.mpr ⟨hAB (Finset.mem_filter.mp hp).1,
    (Finset.mem_filter.mp hp).2⟩

/-- Ordered uniqueness gives fibres of size zero or one, including squares. -/
theorem pairProductWeight_halfProductPairs (num den N : ℕ) (T : ℝ) (m : ℕ) :
    pairProductWeight (halfProductPairs num den N T) m =
      if m ∈ halfProductSource num den N T then 1 else 0 := by
  classical
  by_cases hm : m ∈ halfProductSource num den N T
  · obtain ⟨a, ha, _⟩ := halfProductSource_existsUnique_pair hm
    have hf : (halfProductPairs num den N T).filter (fun p => p.1 * p.2 = m) =
        {a} := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · intro hp
        exact halfProductPairs_mul_injective hp.1 ha.1 (hp.2.trans ha.2.symm)
      · intro hp
        subst p
        exact ha
    simp only [pairProductWeight, hf, Finset.card_singleton, Nat.cast_one, if_pos hm]
  · have hf : (halfProductPairs num den N T).filter (fun p => p.1 * p.2 = m) =
        ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp, hpm⟩ := Finset.mem_filter.mp hp
      exact hm (hpm ▸ mul_mem_halfProductSource hp)
    simp only [pairProductWeight, hf, Finset.card_empty, Nat.cast_zero, if_neg hm]

/-- The manuscript's pointwise sandwich, valid on every natural product. -/
theorem actualGridWeight_sandwich
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) (hκ : 1 < κ) (m : ℕ) :
    0 ≤ actualGridLowerWeight num den N T κ m ∧
      actualGridLowerWeight num den N T κ m ≤
        (if m ∈ halfProductSource num den N T then 1 else 0) ∧
      (if m ∈ halfProductSource num den N T then 1 else 0) ≤
        actualGridUpperWeight num den N T κ m := by
  classical
  rw [← pairProductWeight_halfProductPairs]
  exact ⟨pairProductWeight_nonneg _ _,
    pairProductWeight_mono (actualGridLowerPairs_subset_halfProductPairs hden) m,
    pairProductWeight_mono (halfProductPairs_subset_actualGridUpperPairs hκ) m⟩

/-- Fibre subtraction is exact because the lower pair set is a subset. -/
theorem pairProductWeight_sdiff {A B : Finset (ℕ × ℕ)} (hAB : A ⊆ B) (m : ℕ) :
    pairProductWeight (B \ A) m = pairProductWeight B m - pairProductWeight A m := by
  classical
  have hf : (B \ A).filter (fun p => p.1 * p.2 = m) =
      (B.filter (fun p => p.1 * p.2 = m)) \ (A.filter (fun p => p.1 * p.2 = m)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hs : A.filter (fun p => p.1 * p.2 = m) ⊆
      B.filter (fun p => p.1 * p.2 = m) := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨hAB (Finset.mem_filter.mp hp).1,
      (Finset.mem_filter.mp hp).2⟩
  have hc := Finset.card_sdiff_add_card_eq_card hs
  have hcR :
      (((B.filter (fun p => p.1 * p.2 = m)) \
        (A.filter (fun p => p.1 * p.2 = m))).card : ℝ) +
        ((A.filter (fun p => p.1 * p.2 = m)).card : ℝ) =
          ((B.filter (fun p => p.1 * p.2 = m)).card : ℝ) := by
    exact_mod_cast hc
  unfold pairProductWeight
  rw [hf]
  linarith

/-- The envelope difference is the actual boundary convolution. -/
theorem actualGridUpperWeight_sub_lower (num den N : ℕ) (T κ : ℝ) (m : ℕ) :
    actualGridUpperWeight num den N T κ m - actualGridLowerWeight num den N T κ m =
      pairProductWeight (actualGridBoundaryPairs num den N T κ) m :=
  (pairProductWeight_sdiff (actualGridLowerPairs_subset_upper num den N T κ) m).symm

/-- Every boundary pair lies in a genuinely crossing positive cell. -/
theorem actualGridBoundaryPairs_crossing
    {num den N : ℕ} {T δ : ℝ} (hden : 0 < den) (hδ : 0 < δ)
    {p : ℕ × ℕ} (hp : p ∈ actualGridBoundaryPairs num den N T (1 + δ)) :
    inHalfProductCrossingCell δ T N ((num : ℝ) / (den : ℝ))
      ((p.1 : ℝ), (p.2 : ℝ)) := by
  classical
  have hκ : 1 < 1 + δ := by linarith
  rw [actualGridBoundaryPairs_eq_union hκ] at hp
  obtain ⟨ij, hij, hpij⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hi, hni⟩ := Finset.mem_sdiff.mp hij
  obtain ⟨_, a, ha, haij⟩ := Finset.mem_filter.mp hi
  have hnot : ¬ actualGridCellInside num den N T (1 + δ) ij := by
    intro h
    exact hni (Finset.mem_filter.mpr ⟨hi, h⟩)
  unfold actualGridCellInside at hnot
  push_neg at hnot
  obtain ⟨c, hcij, hc⟩ := hnot
  refine ⟨(1 + δ) ^ ij.1, (1 + δ) ^ ij.2,
    ((a.1 : ℝ), (a.2 : ℝ)), ((c.1 : ℝ), (c.2 : ℝ)),
    pow_pos (by linarith) _, pow_pos (by linarith) _,
    multiplicativeGridRectangle_mem_boundaryCell haij,
    ((halfProductPairs_iff_prime_realRegion hden).mp ha).2.2,
    multiplicativeGridRectangle_mem_boundaryCell hcij, hc,
    multiplicativeGridRectangle_mem_boundaryCell (Finset.mem_filter.mp hpij).1⟩

/-- The common carrier contains the original source with both endpoints. -/
theorem halfProductSource_subset_actualGridProductCarrier
    {num den N : ℕ} {T κ : ℝ} (hκ : 1 < κ) :
    halfProductSource num den N T ⊆ actualGridProductCarrier num den N T κ := by
  classical
  intro m hm
  obtain ⟨p, hp, _⟩ := halfProductSource_existsUnique_pair hm
  exact Finset.mem_image.mpr
    ⟨p, halfProductPairs_subset_actualGridUpperPairs hκ hp.1, hp.2⟩

/-- All boundary product fibres are retained, including products above `N`. -/
theorem actualGridBoundaryPairs_image_subset_carrier (num den N : ℕ) (T κ : ℝ) :
    (actualGridBoundaryPairs num den N T κ).image (fun p => p.1 * p.2) ⊆
      actualGridProductCarrier num den N T κ := by
  classical
  intro m hm
  obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp hm
  exact Finset.mem_image.mpr ⟨p, (Finset.mem_sdiff.mp hp).1, hpm⟩

/-- The total boundary convolution mass is its literal prime-pair count. -/
theorem actualGrid_boundary_mass_eq_card (num den N : ℕ) (T κ : ℝ) :
    finiteSourceMass (actualGridProductCarrier num den N T κ)
      (fun m => actualGridUpperWeight num den N T κ m -
        actualGridLowerWeight num den N T κ m) =
      ((actualGridBoundaryPairs num den N T κ).card : ℝ) := by
  simp_rw [actualGridUpperWeight_sub_lower]
  exact finiteSourceMass_pairProductWeight _ _
    (actualGridBoundaryPairs_image_subset_carrier num den N T κ)

/-- The literal envelopes satisfy an explicit uniform finite boundary budget.
The only exponent assumptions here are `0 ≤ b ≤ 1`, so this includes every
manuscript exponent `1/2 < b < 1`. No mass estimate is an input. -/
theorem actualGrid_boundary_mass_le_explicit
    {num den N : ℕ} {T δ : ℝ} (hden : 0 < den)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : 0 ≤ T) (hTN : T ≤ (N : ℝ))
    (hN : 1 ≤ (N : ℝ)) (hb1 : (num : ℝ) / (den : ℝ) ≤ 1) :
    finiteSourceMass (actualGridProductCarrier num den N T (1 + δ))
      (fun m => actualGridUpperWeight num den N T (1 + δ) m -
        actualGridLowerWeight num den N T (1 + δ) m) ≤
      12 * δ * N * Real.log (3 * N) + 216 * δ * N +
        14 * (N : ℝ) ^ (1 / (1 + (num : ℝ) / (den : ℝ))) := by
  rw [actualGrid_boundary_mass_eq_card]
  exact crossingCells_card_le_explicit _ hδ.le hδ1 hT hTN hN
    (div_nonneg (Nat.cast_nonneg num) (Nat.cast_nonneg den)) hb1
    (fun _ hp => actualGridBoundaryPairs_crossing hden hδ hp)

/-- Feed the constructed envelopes directly to the pre-existing actual
half-product discrepancy transfer on their full product carrier. -/
theorem abs_halfProductPrimitiveDiscrepancy_le_actualGridEnvelopes
    {num den N : ℕ} {T κ : ℝ} (hden : 0 < den) (hκ : 1 < κ) (d : ℕ) :
    |halfProductCongruenceMass num den N T d -
        halfProductCoprimeMass num den N T d / (Nat.totient d : ℝ)| ≤
      |finitePrimitiveDiscrepancy (actualGridProductCarrier num den N T κ)
        (actualGridLowerWeight num den N T κ) N d| +
      |finitePrimitiveDiscrepancy (actualGridProductCarrier num den N T κ)
        (fun m => actualGridUpperWeight num den N T κ m -
          actualGridLowerWeight num den N T κ m) N d| +
      finiteSourceMass (actualGridProductCarrier num den N T κ)
        (fun m => actualGridUpperWeight num den N T κ m -
          actualGridLowerWeight num den N T κ m) / (Nat.totient d : ℝ) := by
  exact abs_halfProductPrimitiveDiscrepancy_le_of_sandwich num den N T _ _ _ d
    (halfProductSource_subset_actualGridProductCarrier hκ)
    (fun m _ => (actualGridWeight_sandwich hden hκ m).2.1)
    (fun m _ => (actualGridWeight_sandwich hden hκ m).2.2)

end

end ImbalancedChen
