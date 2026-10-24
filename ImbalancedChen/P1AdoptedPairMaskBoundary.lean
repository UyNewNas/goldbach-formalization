import ImbalancedChen.P1AdoptedPairMaskAncestorSupport
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
SOURCE ONLY, 2026-10-24; eventual integration imports the preceding two drafts.

Arithmetic boundary terms are retained as literal finite coordinate fibres.
No Lebesgue-null argument removes an integer or prime tuple, and no analytic
smallness estimate is asserted. Endpoint sums retain all tuple multiplicity.
-/

namespace ImbalancedChen.P1AdoptedPairMaskBoundary

noncomputable section

open Set Certificates.PairedV2
open FullMask.P1E0E1
open P1AdoptedPairMaskAncestorSupport
open scoped BigOperators

def strictPairCell (r : FullMask.Row) : Set (ℝ × ℝ) :=
  {y | y ∈ pairCell r ∧
    (tLower (FullMask.indices r).1 : ℝ) < y.1 ∧
    (uLower (FullMask.indices r).2 : ℝ) < y.2}

def lowerTWall (r : FullMask.Row) : Set (ℝ × ℝ) :=
  {y | y ∈ pairCell r ∧ y.1 = (tLower (FullMask.indices r).1 : ℝ)}

def lowerUWall (r : FullMask.Row) : Set (ℝ × ℝ) :=
  {y | y ∈ pairCell r ∧ y.2 = (uLower (FullMask.indices r).2 : ℝ)}

/-- Both walls retain the original strict upper endpoints from pairCell. -/
theorem pairCell_diff_strict_eq_walls (r : FullMask.Row) :
    pairCell r \ strictPairCell r = lowerTWall r ∪ lowerUWall r := by
  ext y
  constructor
  · rintro ⟨hy, hnot⟩
    by_cases ht : (tLower (FullMask.indices r).1 : ℝ) < y.1
    · by_cases hu : (uLower (FullMask.indices r).2 : ℝ) < y.2
      · exact False.elim (hnot ⟨hy, ht, hu⟩)
      · exact Or.inr ⟨hy, le_antisymm (le_of_not_gt hu) hy.2.2.1⟩
    · exact Or.inl ⟨hy, le_antisymm (le_of_not_gt ht) hy.1⟩
  · rintro (⟨hy, heq⟩ | ⟨hy, heq⟩)
    · refine ⟨hy, ?_⟩
      intro hs
      have ht := hs.2.1
      rw [heq] at ht
      exact lt_irrefl _ ht
    · refine ⟨hy, ?_⟩
      intro hs
      have hu := hs.2.2
      rw [heq] at hu
      exact lt_irrefl _ hu

theorem pairCell_diff_fibre_projection_eq_walls (r : FullMask.Row) :
    pairCell r \ ((fun x : Fin 4 → ℝ => (x 0, x 1)) '' FullMask.support r) =
      lowerTWall r ∪ lowerUWall r := by
  rw [fibre_image_pair_projection]
  exact pairCell_diff_strict_eq_walls r

def strictPairRegion : Set (ℝ × ℝ) := {y | ∃ r : FullMask.Row, y ∈ strictPairCell r}

def boundaryRegion : Set (ℝ × ℝ) := pairRegion \ strictPairRegion

theorem strictPairRegion_eq_fibre_image :
    strictPairRegion =
      (fun x : Fin 4 → ℝ => (x 0, x 1)) '' FullMask.region := by
  ext y
  constructor
  · rintro ⟨r, hr⟩
    have himage : y ∈ (fun x : Fin 4 → ℝ => (x 0, x 1)) '' FullMask.support r := by
      rw [fibre_image_pair_projection]
      exact hr
    obtain ⟨x, hx, heq⟩ := himage
    exact ⟨x, Set.mem_iUnion.mpr ⟨r, hx⟩, heq⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    have himage : (x 0, x 1) ∈
        (fun x : Fin 4 → ℝ => (x 0, x 1)) '' FullMask.support r := ⟨x, hr, rfl⟩
    rw [fibre_image_pair_projection] at himage
    exact ⟨r, himage⟩

/-- Exact finite union identity. Distinct-row strict interiors cannot cover
another row's wall, because half-open pairCell already has unique ownership. -/
theorem boundaryRegion_eq_lower_wall_union :
    boundaryRegion = ⋃ r : FullMask.Row, lowerTWall r ∪ lowerUWall r := by
  ext y
  constructor
  · rintro ⟨⟨r, hr⟩, hnot⟩
    apply Set.mem_iUnion.mpr
    refine ⟨r, ?_⟩
    rw [← pairCell_diff_strict_eq_walls]
    exact ⟨hr, fun hs => hnot ⟨r, hs⟩⟩
  · intro hy
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hy
    rw [← pairCell_diff_strict_eq_walls] at hr
    refine ⟨⟨r, hr.1⟩, ?_⟩
    rintro ⟨s, hs⟩
    have hsr : s = r := pairCell_unique_owner hs.1 hr.1
    subst s
    exact hr.2 hs

theorem boundaryRegion_subset_lower_wall_union :
    boundaryRegion ⊆ ⋃ r : FullMask.Row, lowerTWall r ∪ lowerUWall r := by
  intro y hy
  rw [boundaryRegion_eq_lower_wall_union] at hy
  exact hy

/-- Positive integer values are uniquely determined by their normalized log
coordinate when N>1. Zero/negative inputs are not admitted to log injectivity. -/
theorem normalized_log_nat_injective {N : ℝ} (hN : 1 < N)
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (heq : Real.log (p : ℝ) / Real.log N = Real.log (q : ℝ) / Real.log N) : p = q := by
  have hlog : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hm := congrArg (fun t : ℝ => t * Real.log N) heq
  simp only [div_mul_cancel₀ _ hlog] at hm
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hpq : (p : ℝ) = (q : ℝ) := Real.log_injOn_pos hpR hqR hm
  exact_mod_cast hpq

theorem lowerTWall_integer_coordinate_unique {N : ℝ} (hN : 1 < N)
    (r : FullMask.Row) {p q : ℕ × ℕ} (hp : 0 < p.2) (hq : 0 < q.2)
    (hpw : primePairCoordinates N p ∈ lowerTWall r)
    (hqw : primePairCoordinates N q ∈ lowerTWall r) : p.2 = q.2 := by
  apply normalized_log_nat_injective hN hp hq
  exact hpw.2.trans hqw.2.symm

theorem lowerUWall_integer_coordinate_unique {N : ℝ} (hN : 1 < N)
    (r : FullMask.Row) {p q : ℕ × ℕ} (hp : 0 < p.1) (hq : 0 < q.1)
    (hpw : primePairCoordinates N p ∈ lowerUWall r)
    (hqw : primePairCoordinates N q ∈ lowerUWall r) : p.1 = q.1 := by
  apply normalized_log_nat_injective hN hp hq
  exact hpw.2.trans hqw.2.symm

def interiorDeletionMask (N : ℝ) (p : ℕ × ℕ) : Prop :=
  primePairCoordinates N p ∈ strictPairRegion

def boundaryDeletionMask (N : ℝ) (p : ℕ × ℕ) : Prop :=
  primePairCoordinates N p ∈ boundaryRegion

theorem interiorDeletionMask_implies_deletionMask (N : ℝ) (p : ℕ × ℕ)
    (hp : interiorDeletionMask N p) : deletionMask N p := by
  obtain ⟨r, hr⟩ := hp
  exact ⟨r, hr.1⟩

/-- The arithmetic discrepancy retains its actual pair source. -/
def boundaryCarrier {α : Type*} (S : Finset α) (pair : α → ℕ × ℕ) (N : ℝ) : Finset α := by
  classical
  exact S.filter fun x => primePairCoordinates N (pair x) ∈ boundaryRegion

/-- This counts source tuples at an endpoint, retaining every other coordinate. -/
def endpointCarrier {α : Type*} (S : Finset α) (value : α → ℕ)
    (N c : ℝ) : Finset α := by
  classical
  exact S.filter fun x => Real.log (value x : ℝ) / Real.log N = c

def endpointValues {α : Type*} (S : Finset α) (value : α → ℕ)
    (N c : ℝ) : Finset ℕ := by
  classical
  exact (S.image value).filter fun q => Real.log (q : ℝ) / Real.log N = c

/-- A wall can select at most one integer coordinate value, though its
source-tuple fibre may contain many tuples. -/
theorem endpointValues_card_le_one {α : Type*} (S : Finset α) (value : α → ℕ)
    {N : ℝ} (hN : 1 < N) (c : ℝ) (hpos : ∀ x ∈ S, 0 < value x) :
    (endpointValues S value N c).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hpimage, hpc⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqimage, hqc⟩ := Finset.mem_filter.mp hq
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hpimage
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hqimage
  exact normalized_log_nat_injective hN (hpos x hx) (hpos y hy) (hpc.trans hqc.symm)

/-- An endpoint fibre is empty or equals a literal single-value coordinate
fibre of the original finite source; multiplicity is not collapsed. -/
theorem endpointCarrier_empty_or_value_fibre {α : Type*} (S : Finset α)
    (value : α → ℕ) {N : ℝ} (hN : 1 < N) (c : ℝ)
    (hpos : ∀ x ∈ S, 0 < value x) :
    endpointCarrier S value N c = ∅ ∨
      ∃ q : ℕ, q ∈ S.image value ∧
        Real.log (q : ℝ) / Real.log N = c ∧
        endpointCarrier S value N c = S.filter (fun x => value x = q) := by
  classical
  rcases (endpointCarrier S value N c).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · exact Or.inl he
  · obtain ⟨hxS, hxc⟩ := Finset.mem_filter.mp hx
    refine Or.inr ⟨value x, Finset.mem_image.mpr ⟨x, hxS, rfl⟩, hxc, ?_⟩
    ext y
    simp only [endpointCarrier, Finset.mem_filter]
    constructor
    · rintro ⟨hyS, hyc⟩
      exact ⟨hyS, normalized_log_nat_injective hN (hpos y hyS) (hpos x hxS)
        (hyc.trans hxc.symm)⟩
    · rintro ⟨hyS, heq⟩
      exact ⟨hyS, by rw [heq]; exact hxc⟩

private theorem card_biUnion_le_sum {ι α : Type*} [DecidableEq α]
    (s : Finset ι) (F : ι → Finset α) :
    (s.biUnion F).card ≤ ∑ i ∈ s, (F i).card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hi]
      exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left ih _)

/-- A finite source boundary is covered by the actual adopted rows' two
endpoint-coordinate fibres. No global count bound is assumed. -/
theorem boundaryCarrier_subset_endpoint_cover {α : Type*} [DecidableEq α] (S : Finset α)
    (pair : α → ℕ × ℕ) (N : ℝ) :
    boundaryCarrier S pair N ⊆ Finset.univ.biUnion (fun r : FullMask.Row =>
      endpointCarrier S (fun x => (pair x).2) N (tLower (FullMask.indices r).1 : ℝ) ∪
        endpointCarrier S (fun x => (pair x).1) N (uLower (FullMask.indices r).2 : ℝ)) := by
  classical
  intro x hx
  obtain ⟨hxS, hxb⟩ := Finset.mem_filter.mp hx
  rw [boundaryRegion_eq_lower_wall_union] at hxb
  obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hxb
  apply Finset.mem_biUnion.mpr
  refine ⟨r, Finset.mem_univ r, ?_⟩
  rcases hr with ht | hu
  · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hxS, ht.2⟩))
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hxS, hu.2⟩))

theorem boundaryCarrier_card_le_endpoint_sum {α : Type*} (S : Finset α)
    (pair : α → ℕ × ℕ) (N : ℝ) :
    (boundaryCarrier S pair N).card ≤ ∑ r : FullMask.Row,
      ((endpointCarrier S (fun x => (pair x).2) N (tLower (FullMask.indices r).1 : ℝ)).card +
        (endpointCarrier S (fun x => (pair x).1) N (uLower (FullMask.indices r).2 : ℝ)).card) := by
  classical
  calc
    (boundaryCarrier S pair N).card ≤
        (Finset.univ.biUnion (fun r : FullMask.Row =>
          endpointCarrier S (fun x => (pair x).2) N (tLower (FullMask.indices r).1 : ℝ) ∪
            endpointCarrier S (fun x => (pair x).1) N (uLower (FullMask.indices r).2 : ℝ))).card :=
      Finset.card_le_card (boundaryCarrier_subset_endpoint_cover S pair N)
    _ ≤ ∑ r : FullMask.Row,
        (endpointCarrier S (fun x => (pair x).2) N (tLower (FullMask.indices r).1 : ℝ) ∪
          endpointCarrier S (fun x => (pair x).1) N (uLower (FullMask.indices r).2 : ℝ)).card :=
      card_biUnion_le_sum _ _
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => Finset.card_union_le _ _)

theorem selectedY6_boundary_difference (n : ℕ) (A H D N : ℝ) :
    chenY6SelectedTuples n A H D (deletionMask N) \
        chenY6SelectedTuples n A H D (interiorDeletionMask N) =
      boundaryCarrier (chenY6Tuples n A H D) id N := by
  classical
  ext p
  by_cases hp : p ∈ chenY6Tuples n A H D <;>
    simp [Finset.mem_sdiff, mem_chenY6SelectedTuples, boundaryCarrier,
      boundaryRegion, deletionMask, interiorDeletionMask, hp]

theorem selectedY11_boundary_difference (n : ℕ) (A H D N : ℝ) :
    chenY11SelectedTuples n A H D (deletionMask N) \
        chenY11SelectedTuples n A H D (interiorDeletionMask N) =
      boundaryCarrier (chenY11FullTuples n A H D) (fun p => p.2) N := by
  classical
  ext p
  by_cases hp : p ∈ chenY11FullTuples n A H D <;>
    simp [Finset.mem_sdiff, mem_chenY11SelectedTuples, boundaryCarrier,
      boundaryRegion, deletionMask, interiorDeletionMask, hp]

theorem y6_boundaryCarrier_eq_selected (n : ℕ) (A H D N : ℝ) :
    boundaryCarrier (chenY6Tuples n A H D) id N =
      chenY6SelectedTuples n A H D (boundaryDeletionMask N) := by
  rfl

theorem y11_boundaryCarrier_eq_selected (n : ℕ) (A H D N : ℝ) :
    boundaryCarrier (chenY11FullTuples n A H D) (fun p => p.2) N =
      chenY11SelectedTuples n A H D (boundaryDeletionMask N) := by
  rfl

/-- Existing same-last-pair injection also applies to this exact arithmetic
boundary discrepancy; it does not require a real null-set argument. -/
theorem y11_boundary_card_le_y6_boundary {n : ℕ} (A H D N : ℝ)
    (hn : Squarefree n) :
    (boundaryCarrier (chenY11FullTuples n A H D) (fun p => p.2) N).card ≤
      (boundaryCarrier (chenY6Tuples n A H D) id N).card := by
  rw [y11_boundaryCarrier_eq_selected, y6_boundaryCarrier_eq_selected]
  exact chenY11Selected_le_chenY6Selected (A := A) (H := H) (D := D) hn (boundaryDeletionMask N)

/-- Exact arithmetic count bookkeeping, before any boundary-size estimate. -/
theorem selectedY6_boundary_add_interior_card (n : ℕ) (A H D N : ℝ) :
    (boundaryCarrier (chenY6Tuples n A H D) id N).card +
        (chenY6SelectedTuples n A H D (interiorDeletionMask N)).card =
      (chenY6SelectedTuples n A H D (deletionMask N)).card := by
  classical
  have hs : chenY6SelectedTuples n A H D (interiorDeletionMask N) ⊆
      chenY6SelectedTuples n A H D (deletionMask N) := by
    intro p hp
    obtain ⟨hpS, hpi⟩ := mem_chenY6SelectedTuples.mp hp
    exact mem_chenY6SelectedTuples.mpr
      ⟨hpS, interiorDeletionMask_implies_deletionMask N p hpi⟩
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [selectedY6_boundary_difference] at hc
  exact hc

theorem selectedY11_boundary_add_interior_card (n : ℕ) (A H D N : ℝ) :
    (boundaryCarrier (chenY11FullTuples n A H D) (fun p => p.2) N).card +
        (chenY11SelectedTuples n A H D (interiorDeletionMask N)).card =
      (chenY11SelectedTuples n A H D (deletionMask N)).card := by
  classical
  have hs : chenY11SelectedTuples n A H D (interiorDeletionMask N) ⊆
      chenY11SelectedTuples n A H D (deletionMask N) := by
    intro p hp
    obtain ⟨hpS, hpi⟩ := mem_chenY11SelectedTuples.mp hp
    exact mem_chenY11SelectedTuples.mpr
      ⟨hpS, interiorDeletionMask_implies_deletionMask N p.2 hpi⟩
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [selectedY11_boundary_difference] at hc
  exact hc

/-- The exact arithmetic Y6 discrepancy is bounded by explicit endpoint
fibres, counted on the original Y6 source. -/
theorem selectedY6_boundary_card_le (n : ℕ) (A H D N : ℝ) :
    (chenY6SelectedTuples n A H D (deletionMask N) \
        chenY6SelectedTuples n A H D (interiorDeletionMask N)).card ≤
      ∑ r : FullMask.Row,
        ((endpointCarrier (chenY6Tuples n A H D) Prod.snd N
            (tLower (FullMask.indices r).1 : ℝ)).card +
          (endpointCarrier (chenY6Tuples n A H D) Prod.fst N
            (uLower (FullMask.indices r).2 : ℝ)).card) := by
  rw [selectedY6_boundary_difference]
  exact boundaryCarrier_card_le_endpoint_sum (chenY6Tuples n A H D) id N

/-- The Y11 bound keeps the first pair's multiplicity and fixes only one
coordinate of its last pair at each endpoint. -/
theorem selectedY11_boundary_card_le (n : ℕ) (A H D N : ℝ) :
    (chenY11SelectedTuples n A H D (deletionMask N) \
        chenY11SelectedTuples n A H D (interiorDeletionMask N)).card ≤
      ∑ r : FullMask.Row,
        ((endpointCarrier (chenY11FullTuples n A H D) (fun p => p.2.2) N
            (tLower (FullMask.indices r).1 : ℝ)).card +
          (endpointCarrier (chenY11FullTuples n A H D) (fun p => p.2.1) N
            (uLower (FullMask.indices r).2 : ℝ)).card) := by
  rw [selectedY11_boundary_difference]
  exact boundaryCarrier_card_le_endpoint_sum (chenY11FullTuples n A H D) (fun p => p.2) N

theorem y6_pair_values_pos {n : ℕ} {A H D : ℝ} {p : ℕ × ℕ}
    (hp : p ∈ chenY6Tuples n A H D) : 0 < p.1 ∧ 0 < p.2 := by
  classical
  have hc : p ∈ chenInitialPairCarrier n := (Finset.mem_filter.mp hp).1
  change p ∈ n.primeFactors ×ˢ n.primeFactors at hc
  obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp hc
  exact ⟨(Nat.mem_primeFactors.mp hfirst).1.pos, (Nat.mem_primeFactors.mp hsecond).1.pos⟩

theorem y11_last_pair_values_pos {n : ℕ} {A H D : ℝ}
    {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : p ∈ chenY11FullTuples n A H D) :
    0 < p.2.1 ∧ 0 < p.2.2 := by
  classical
  have hc : p ∈ chenFourPrimeCarrier n := (Finset.mem_filter.mp hp).1
  change p ∈ (n.primeFactors ×ˢ n.primeFactors) ×ˢ (n.primeFactors ×ˢ n.primeFactors) at hc
  have hlast := (Finset.mem_product.mp hc).2
  obtain ⟨hfirst, hsecond⟩ := Finset.mem_product.mp hlast
  exact ⟨(Nat.mem_primeFactors.mp hfirst).1.pos, (Nat.mem_primeFactors.mp hsecond).1.pos⟩

theorem y6_t_endpoint_values_card_le_one (n : ℕ) (A H D : ℝ)
    {N : ℝ} (hN : 1 < N) (r : FullMask.Row) :
    (endpointValues (chenY6Tuples n A H D) Prod.snd N
      (tLower (FullMask.indices r).1 : ℝ)).card ≤ 1 := by
  apply endpointValues_card_le_one _ _ hN
  intro p hp
  exact (y6_pair_values_pos hp).2

theorem y6_u_endpoint_values_card_le_one (n : ℕ) (A H D : ℝ)
    {N : ℝ} (hN : 1 < N) (r : FullMask.Row) :
    (endpointValues (chenY6Tuples n A H D) Prod.fst N
      (uLower (FullMask.indices r).2 : ℝ)).card ≤ 1 := by
  apply endpointValues_card_le_one _ _ hN
  intro p hp
  exact (y6_pair_values_pos hp).1

theorem y11_t_endpoint_values_card_le_one (n : ℕ) (A H D : ℝ)
    {N : ℝ} (hN : 1 < N) (r : FullMask.Row) :
    (endpointValues (chenY11FullTuples n A H D) (fun p => p.2.2) N
      (tLower (FullMask.indices r).1 : ℝ)).card ≤ 1 := by
  apply endpointValues_card_le_one _ _ hN
  intro p hp
  exact (y11_last_pair_values_pos hp).2

theorem y11_u_endpoint_values_card_le_one (n : ℕ) (A H D : ℝ)
    {N : ℝ} (hN : 1 < N) (r : FullMask.Row) :
    (endpointValues (chenY11FullTuples n A H D) (fun p => p.2.1) N
      (uLower (FullMask.indices r).2 : ℝ)).card ≤ 1 := by
  apply endpointValues_card_le_one _ _ hN
  intro p hp
  exact (y11_last_pair_values_pos hp).1

end

end ImbalancedChen.P1AdoptedPairMaskBoundary
