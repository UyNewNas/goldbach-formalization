import ImbalancedChen.P4BLabelledPairDictionary
import ImbalancedChen.CurvedRegionDiscrepancy
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual labelled outer-source pushforward to integer products

YELLOW / SOURCE-ONLY / UNCOMPILED DRAFT.

The future project import names the sibling genuine pair dictionary.
The integer carrier contains every product in the actual labelled prime
carrier, including products above N. A fibre sum retains every outer
weight contribution. All identities precede any sign or analytic estimate.
Nonnegativity and W<=V are used only for pointwise source domination.
No integer-shift sieve theorem or Part 3 estimate is asserted here.
-/

namespace ImbalancedChen.P4BLabelledOuterPushforward

noncomputable section

open scoped BigOperators
open Classical
open ImbalancedChen.Part3 ImbalancedChen.P4BLabelledPairDictionary

/-- The actual finite integer product image; no m<=N truncation is made. -/
def productCarrier (N : ℕ) : Finset ℕ :=
  (labelledPrimeTuples 2 N).image labelledProduct

/-- Sum the genuine outer tuple weight over its exact product fibre. -/
def productWeight (N : ℕ) (V : (Fin 2 → Fin (N + 1)) → ℝ) (m : ℕ) : ℝ :=
  ∑ t ∈ (labelledPrimeTuples 2 N).filter (fun t => labelledProduct t = m), V t

/-- An active integer weight has an actual active labelled fibre witness.
This holds even when the tuple coefficients have arbitrary signs. -/
theorem exists_nonzero_fibre_of_productWeight_ne_zero {N m : ℕ}
    {V : (Fin 2 → Fin (N + 1)) → ℝ} (hweight : productWeight N V m ≠ 0) :
    ∃ t : Fin 2 → Fin (N + 1), t ∈ labelledPrimeTuples 2 N ∧
      labelledProduct t = m ∧ V t ≠ 0 := by
  classical
  by_contra hnone
  apply hweight
  apply Finset.sum_eq_zero
  intro t ht
  have htfibre := Finset.mem_filter.mp ht
  by_contra hV
  exact hnone ⟨t, htfibre.1, htfibre.2, hV⟩

/-- Exact finite pushforward against any signed real integer kernel.
Neither V nor the kernel is assumed nonnegative. -/
theorem weighted_pushforward (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (F : ℕ → ℝ) :
    (∑ m ∈ productCarrier N, productWeight N V m * F m) =
      ∑ t ∈ labelledPrimeTuples 2 N, V t * F (labelledProduct t) := by
  classical
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := labelledPrimeTuples 2 N) (t := productCarrier N)
    (g := labelledProduct)
    (fun t ht => Finset.mem_image_of_mem labelledProduct ht)
    (fun t => V t * F (labelledProduct t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  unfold productWeight
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

theorem finiteSourceMass_eq_labelled (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) :
    finiteSourceMass (productCarrier N) (productWeight N V) =
      ∑ t ∈ labelledPrimeTuples 2 N, V t := by
  simpa only [finiteSourceMass, mul_one] using
    weighted_pushforward N V (fun _ => 1)

/-- Every mask is pushed through the same fibre sum, without dropping
outer points outside the original curved source. -/
theorem sum_filter_productWeight (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (∑ m ∈ (productCarrier N).filter P, productWeight N V m) =
      ∑ t ∈ labelledPrimeTuples 2 N,
        if P (labelledProduct t) then V t else 0 := by
  classical
  simpa only [Finset.sum_filter, mul_ite, mul_one, mul_zero] using
    weighted_pushforward N V (fun m => if P m then 1 else 0)

theorem finiteCongruenceMass_eq_labelled (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (a d : ℕ) :
    finiteCongruenceMass (productCarrier N) (productWeight N V) a d =
      ∑ t ∈ labelledPrimeTuples 2 N,
        if Nat.ModEq d (labelledProduct t) a then V t else 0 := by
  exact sum_filter_productWeight N V (fun m => Nat.ModEq d m a)

theorem finiteCoprimeMass_eq_labelled (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (d : ℕ) :
    finiteCoprimeMass (productCarrier N) (productWeight N V) d =
      ∑ t ∈ labelledPrimeTuples 2 N,
        if Nat.Coprime (labelledProduct t) d then V t else 0 := by
  exact sum_filter_productWeight N V (fun m => Nat.Coprime m d)

/-- The primitive normalized kernel, including its actual coprime mask,
is unchanged by the pushforward. Modulus zero is covered by total division. -/
theorem finitePrimitiveDiscrepancy_eq_labelled (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (a d : ℕ) :
    finitePrimitiveDiscrepancy (productCarrier N) (productWeight N V) a d =
      ∑ t ∈ labelledPrimeTuples 2 N, V t *
        ((if Nat.ModEq d (labelledProduct t) a then (1 : ℝ) else 0) -
          (if Nat.Coprime (labelledProduct t) d then (1 : ℝ) else 0) /
            (Nat.totient d : ℝ)) := by
  classical
  unfold finitePrimitiveDiscrepancy
  rw [finiteCongruenceMass_eq_labelled, finiteCoprimeMass_eq_labelled,
    ← Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hmod : Nat.ModEq d (labelledProduct t) a <;>
    by_cases hcop : Nat.Coprime (labelledProduct t) d <;>
    simp [hmod, hcop] <;> ring

/-- One same-rho signed sum, exactly the actual rank-two Part 3 error.
No absolute value is moved inside the physical modulus sum. -/
theorem signed_productWeight_eq_primeProductSignedError (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) :
    (∑ d ∈ Q, rho d *
      finitePrimitiveDiscrepancy (productCarrier N) (productWeight N V) N d) =
        primeProductSignedError 2 N N Q rho V := by
  unfold primeProductSignedError
  apply Finset.sum_congr rfl
  intro d hd
  rw [finitePrimitiveDiscrepancy_eq_labelled]

/-- A real source integer has its genuine ordered-pair representative in
the actual labelled prime carrier, with W exactly one. -/
theorem exists_labelled_source_representative {b T : ℝ} {N m : ℕ}
    (hm : m ∈ realHalfProductSource b N T) :
    ∃ t : Fin 2 → Fin (N + 1), t ∈ labelledPrimeTuples 2 N ∧
      labelledProduct t = m ∧ W b N T t = 1 := by
  classical
  obtain ⟨a, ha, _⟩ := realHalfProductSource_existsUnique_pair hm
  let t := pairTuple N a (pair_coordinates_le ha.1).1 (pair_coordinates_le ha.1).2
  have ht : t ∈ activeCarrier b N T := pairTuple_mem_activeCarrier ha.1
  have htprime : t ∈ labelledPrimeTuples 2 N := (Finset.mem_filter.mp ht).1
  have htgeometry : geometry b N T t := (Finset.mem_filter.mp ht).2
  refine ⟨t, htprime, ?_, ?_⟩
  · change labelledProduct
      (pairTuple N a (pair_coordinates_le ha.1).1 (pair_coordinates_le ha.1).2) = m
    rw [labelledProduct_pairTuple]
    exact ha.2
  · simp only [W, if_pos htgeometry]

/-- Original source containment is unconditional: the full labelled
product carrier includes every genuine ordered-pair image. -/
theorem source_subset_productCarrier (b : ℝ) (N : ℕ) (T : ℝ) :
    realHalfProductSource b N T ⊆ productCarrier N := by
  intro m hm
  obtain ⟨t, ht, hproduct, _⟩ := exists_labelled_source_representative hm
  exact Finset.mem_image.mpr ⟨t, ht, hproduct⟩

theorem productWeight_nonneg (N : ℕ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, 0 ≤ V t) (m : ℕ) :
    0 ≤ productWeight N V m := by
  apply Finset.sum_nonneg
  intro t ht
  exact hV t (Finset.mem_filter.mp ht).1

/-- Each actual labelled contribution lies below its full product fibre.
No injectivity of outer tuples is assumed or needed. -/
theorem single_le_productWeight {N m : ℕ}
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, 0 ≤ V t)
    {t : Fin 2 → Fin (N + 1)} (ht : t ∈ labelledPrimeTuples 2 N)
    (hproduct : labelledProduct t = m) : V t ≤ productWeight N V m := by
  unfold productWeight
  apply Finset.single_le_sum
  · intro u hu
    exact hV u (Finset.mem_filter.mp hu).1
  · exact Finset.mem_filter.mpr ⟨ht, hproduct⟩

/-- The actual integer source indicator is dominated at every integer,
including outer-carrier points outside the original source. The genuine
ordered representative gives the unit contribution; nonnegativity pays
all other labelled representations. Prime squares require just that unit. -/
theorem actualIndicator_le_productWeight (b : ℝ) (N : ℕ) (T : ℝ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, 0 ≤ V t)
    (hWV : ∀ t ∈ labelledPrimeTuples 2 N, W b N T t ≤ V t) (m : ℕ) :
    (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤
      productWeight N V m := by
  classical
  by_cases hm : m ∈ realHalfProductSource b N T
  · rw [if_pos hm]
    obtain ⟨t, ht, hproduct, hW⟩ := exists_labelled_source_representative hm
    have hone : 1 ≤ V t := by simpa only [hW] using hWV t ht
    exact hone.trans (single_le_productWeight V hV ht hproduct)
  · rw [if_neg hm]
    exact productWeight_nonneg N V hV m

/-- Concrete carrier and pointwise outer comparison ready for an
integer-shift sieve interface. No product<=N hypothesis is introduced. -/
theorem actual_outer_pushforward_majorant (b : ℝ) (N : ℕ) (T : ℝ)
    (V : (Fin 2 → Fin (N + 1)) → ℝ)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, 0 ≤ V t)
    (hWV : ∀ t ∈ labelledPrimeTuples 2 N, W b N T t ≤ V t) :
    realHalfProductSource b N T ⊆ productCarrier N ∧
      ∀ m ∈ productCarrier N,
        (if m ∈ realHalfProductSource b N T then (1 : ℝ) else 0) ≤
          productWeight N V m := by
  refine ⟨source_subset_productCarrier b N T, ?_⟩
  intro m hm
  exact actualIndicator_le_productWeight b N T V hV hWV m

end

end ImbalancedChen.P4BLabelledOuterPushforward
