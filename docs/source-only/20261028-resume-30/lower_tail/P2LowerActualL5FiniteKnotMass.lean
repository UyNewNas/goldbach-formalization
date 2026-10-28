import ImbalancedChen.P2LowerActualL5L6PrimeKnots

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite arithmetic knot mass on the genuine L5 pair selector.  The factor
`a` is retained when a query interval is converted to an affine strip.
The proof sums over actual pairs, then pays their four possible affine
branches and the finite knot list by one-prime Mertens and finite Fubini.
Neither a boundary-mass conclusion nor an h248 mean is assumed.

The two final scalar lemmas isolate the positive-measure U10/U11 clamp.
They do not identify an ideal policy residual with a compiled row level.
-/

namespace ImbalancedChen.P2LowerActualL5FiniteKnotMass

noncomputable section
open scoped Classical BigOperators
open P2LowerFinitePrimeBandMass P2LowerCapPlanIntegerRetention
open P2LowerActualL5L6PrimeKnots P2LowerH248QueryKnotDictionary

private abbrev a : ℝ := Part5OriginalUpsilon5CausalDictionary.a

/-- Exact width conversion, including the equality endpoints. -/
theorem quotient_band_iff {L w q tau : ℝ} (hw : 0 < w) :
    |L / w - q| ≤ tau ↔ |L - q * w| ≤ tau * w := by
  have heq : L - q * w = (L / w - q) * w := by
    field_simp [hw.ne']
    <;> ring
  rw [heq, abs_mul, abs_of_pos hw]
  exact (mul_le_mul_right hw).symm

theorem actual_l5_query_has_affine_strip {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N)
    (q tau : ℝ) (htau : 0 ≤ tau)
    (hnear : |Part5OriginalUpsilon5CausalDictionary.argument
      (P5OriginalU5CausalFinite.coordinates N t) - q| ≤ tau) :
    ∃ j : Fin 4,
      |l5PivotSlope j * coordinate N t.1 +
        l5KnotRest j q ![0, coordinate N t.2]| ≤ tau * a := by
  have ha : 0 < a := by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  have hr : |P5OriginalU5CausalFinite.originalResidual N t - q * a| ≤ tau * a := by
    apply (quotient_band_iff ha).mp
    exact hnear
  obtain ⟨j, hj⟩ := actual_l5_prime_pair_knot hN ht q (tau * a)
    (mul_nonneg htau ha.le) hr
  refine ⟨j, ?_⟩
  have hz : Function.update (P5OriginalU5CausalFinite.coordinates N t) 0 0 =
      Function.update (![0, coordinate N t.2] : Fin 2 → ℝ) 0 0 := by
    funext i
    fin_cases i <;>
      simp [P5OriginalU5CausalFinite.coordinates, actualPrimeTupleLog,
        coordinate, Function.update]
  have hrest : l5KnotRest j q (P5OriginalU5CausalFinite.coordinates N t) =
      l5KnotRest j q ![0, coordinate N t.2] := by
    simp only [l5KnotRest, hz]
  rw [hrest] at hj
  exact hj

def pairWeight (t : ℕ × ℕ) : ℝ :=
  reciprocalPrime t.1 * reciprocalPrime t.2

theorem pairWeight_nonneg (t : ℕ × ℕ) : 0 ≤ pairWeight t :=
  mul_nonneg (reciprocalPrime_nonneg _) (reciprocalPrime_nonneg _)

/-- On the actual source, ordering gives distinct primes, so the product
weight is the original reciprocal totient of the pair multiplier. -/
theorem pairWeight_eq_original_totient {N : ℕ} {t : ℕ × ℕ}
    (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N) :
    pairWeight t = 1 / (Nat.totient (t.1 * t.2) : ℝ) := by
  obtain ⟨hc, hA, horder, hH⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  have hpprime := (mem_chenAdditivePrimeCarrier.mp hp).2.1
  have hqprime := (mem_chenAdditivePrimeCarrier.mp hq).2.1
  have hcop : Nat.Coprime t.1 t.2 :=
    (Nat.coprime_primes hpprime hqprime).mpr (ne_of_lt horder)
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  simp [pairWeight, reciprocalPrime, one_div_mul_one_div]

def branchMassTerm (N : ℕ) (q tau : ℝ) (j : Fin 4)
    (t : ℕ × ℕ) : ℝ :=
  if |l5PivotSlope j * coordinate N t.1 +
      l5KnotRest j q ![0, coordinate N t.2]| ≤ tau * a
  then pairWeight t else 0

theorem branchMassTerm_nonneg (N : ℕ) (q tau : ℝ) (j : Fin 4)
    (t : ℕ × ℕ) : 0 ≤ branchMassTerm N q tau j t := by
  unfold branchMassTerm
  split_ifs
  · exact pairWeight_nonneg _
  · exact le_rfl

/-- Actual source membership and the genuine query are kept inside the
finite arithmetic sum. The enclosing rectangle only drops order and gates
after the exact branch witness has been obtained. -/
def actualL5KnotMass (N : ℕ) (S : Finset ℕ) (Q : Finset ℝ)
    (tau : ℝ) : ℝ :=
  ∑ t ∈ S.product S,
    if t ∈ P5OriginalU5CausalFinite.pairSupport N ∧
        ∃ q ∈ Q, |Part5OriginalUpsilon5CausalDictionary.argument
          (P5OriginalU5CausalFinite.coordinates N t) - q| ≤ tau
    then pairWeight t else 0

theorem actualL5KnotMass_eq_original_totient_sum
    (N : ℕ) (S : Finset ℕ) (Q : Finset ℝ) (tau : ℝ) :
    actualL5KnotMass N S Q tau =
      ∑ t ∈ S.product S,
        if t ∈ P5OriginalU5CausalFinite.pairSupport N ∧
            ∃ q ∈ Q, |Part5OriginalUpsilon5CausalDictionary.argument
              (P5OriginalU5CausalFinite.coordinates N t) - q| ≤ tau
        then 1 / (Nat.totient (t.1 * t.2) : ℝ) else 0 := by
  unfold actualL5KnotMass
  apply Finset.sum_congr rfl
  intro t ht
  split_ifs with h
  · exact pairWeight_eq_original_totient h.1
  · rfl

theorem actual_l5_knot_mass_le_branch_sum {N : ℕ} (hN : 2 ≤ N)
    (S : Finset ℕ) (Q : Finset ℝ) (tau : ℝ) (htau : 0 ≤ tau) :
    actualL5KnotMass N S Q tau ≤
      ∑ t ∈ S.product S, ∑ q ∈ Q, ∑ j : Fin 4,
        branchMassTerm N q tau j t := by
  unfold actualL5KnotMass
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : t ∈ P5OriginalU5CausalFinite.pairSupport N ∧
      ∃ q ∈ Q, |Part5OriginalUpsilon5CausalDictionary.argument
        (P5OriginalU5CausalFinite.coordinates N t) - q| ≤ tau
  · rw [if_pos h]
    obtain ⟨hs, q, hq, hnear⟩ := h
    obtain ⟨j, hj⟩ := actual_l5_query_has_affine_strip hN hs q tau htau hnear
    have hfirst : pairWeight t ≤ ∑ i : Fin 4, branchMassTerm N q tau i t := by
      have hsingle := Finset.single_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) =>
          branchMassTerm_nonneg N q tau i t) (Finset.mem_univ j)
      simpa only [branchMassTerm, if_pos hj] using hsingle
    apply hfirst.trans
    exact Finset.single_le_sum
      (fun q' _ => Finset.sum_nonneg
        (fun i _ => branchMassTerm_nonneg N q' tau i t)) hq
  · rw [if_neg h]
    apply Finset.sum_nonneg
    intro q hq
    exact Finset.sum_nonneg (fun j _ => branchMassTerm_nonneg N q tau j t)

/-- Finite Fubini on the same actual integer primes. The larger prime is
the residual coordinate; its value is permitted to move the strip center. -/
theorem branch_rectangle_eq_fibres (N : ℕ) (S : Finset ℕ)
    (q tau : ℝ) (j : Fin 4) :
    (∑ t ∈ S.product S, branchMassTerm N q tau j t) =
      ∑ r ∈ S, reciprocalPrime r *
        (∑ p ∈ S,
          if |l5PivotSlope j * coordinate N p +
            l5KnotRest j q ![0, coordinate N r]| ≤ tau * a
          then reciprocalPrime p else 0) := by
  rw [Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  unfold branchMassTerm pairWeight
  split_ifs <;> ring

theorem branch_rectangle_mass_le_mertens (N : ℕ) (S : Finset ℕ)
    {eta eps : ℝ} (hM : PrimeIntervalMertens N eta eps S)
    (q tau : ℝ) (htau : 0 ≤ tau) (j : Fin 4) :
    (∑ t ∈ S.product S, branchMassTerm N q tau j t) ≤
      (∑ p ∈ S, reciprocalPrime p) *
        (2 * (tau * a / l5PivotSlope j) / eta + eps) := by
  have ha : 0 ≤ a := by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  rw [branch_rectangle_eq_fibres, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left
    (l5_branch_closed_prime_strip N S hM j q (coordinate N r)
      (tau * a) (mul_nonneg htau ha)) (reciprocalPrime_nonneg r)

/-- No global boundary estimate is a premise: the complete finite actual
L5 query-neighbourhood mass is derived from one-dimensional Mertens. -/
theorem actual_l5_finite_knot_mass_le_mertens {N : ℕ} (hN : 2 ≤ N)
    (S : Finset ℕ) (Q : Finset ℝ)
    {eta eps tau : ℝ} (hM : PrimeIntervalMertens N eta eps S)
    (htau : 0 ≤ tau) :
    actualL5KnotMass N S Q tau ≤
      ∑ q ∈ Q, ∑ j : Fin 4,
        (∑ p ∈ S, reciprocalPrime p) *
          (2 * (tau * a / l5PivotSlope j) / eta + eps) := by
  apply (actual_l5_knot_mass_le_branch_sum hN S Q tau htau).trans
  calc
    (∑ t ∈ S.product S, ∑ q ∈ Q, ∑ j : Fin 4, branchMassTerm N q tau j t) =
        ∑ q ∈ Q, ∑ j : Fin 4, ∑ t ∈ S.product S,
          branchMassTerm N q tau j t := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.sum_comm]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro j hj
      exact branch_rectangle_mass_le_mertens N S hM q tau htau j

theorem actual_l5_table_knot_mass_le_mertens {N : ℕ} (hN : 2 ≤ N)
    (S : Finset ℕ) {eta eps tau : ℝ}
    (hM : PrimeIntervalMertens N eta eps S) (htau : 0 ≤ tau) :
    actualL5KnotMass N S actualH248ActiveKnots tau ≤
      ∑ q ∈ actualH248ActiveKnots, ∑ j : Fin 4,
        (∑ p ∈ S, reciprocalPrime p) *
          (2 * (tau * a / l5PivotSlope j) / eta + eps) :=
  actual_l5_finite_knot_mass_le_mertens hN S actualH248ActiveKnots hM htau

/-- The compact universe is made from the actual eligible primes and
the genuine L5 coordinate range. It is not an arbitrary enclosing set
whose coverage would have to be supplied as a new hypothesis. -/
def l5PrimeUniverse (N : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun p =>
    a ≤ coordinate N p ∧ coordinate N p ≤ Part5OriginalUpsilon5CausalDictionary.h)

theorem actual_l5_pair_in_compact_universe {N : ℕ} (hN : 2 ≤ N)
    {t : ℕ × ℕ} (ht : t ∈ P5OriginalU5CausalFinite.pairSupport N) :
    t ∈ (l5PrimeUniverse N).product (l5PrimeUniverse N) := by
  have hcoords : a ≤ coordinate N t.1 ∧
      coordinate N t.1 < coordinate N t.2 ∧
      coordinate N t.2 < Part5OriginalUpsilon5CausalDictionary.h := by
    simpa [P5OriginalU5CausalFinite.coordinates, actualPrimeTupleLog, coordinate] using
      (Part5OriginalUpsilon5CausalDictionary.mem_triangle.mp
        (P5OriginalU5CausalFinite.coordinates_mem_triangle hN ht))
  obtain ⟨hc, hA, horder, hH⟩ := Finset.mem_filter.mp ht
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  apply Finset.mem_product.mpr
  constructor
  · exact Finset.mem_filter.mpr
      ⟨hp, hcoords.1, hcoords.2.1.le.trans hcoords.2.2.le⟩
  · exact Finset.mem_filter.mpr
      ⟨hq, hcoords.1.trans hcoords.2.1.le, hcoords.2.2.le⟩

def sourceL5KnotMass (N : ℕ) (Q : Finset ℝ) (tau : ℝ) : ℝ :=
  ∑ t ∈ P5OriginalU5CausalFinite.pairSupport N,
    if ∃ q ∈ Q, |Part5OriginalUpsilon5CausalDictionary.argument
        (P5OriginalU5CausalFinite.coordinates N t) - q| ≤ tau
    then 1 / (Nat.totient (t.1 * t.2) : ℝ) else 0

/-- The rectangle bound covers the whole original L5 occurrence. -/
theorem source_l5_knot_mass_eq_rectangle {N : ℕ} (hN : 2 ≤ N)
    (Q : Finset ℝ) (tau : ℝ) :
    sourceL5KnotMass N Q tau = actualL5KnotMass N (l5PrimeUniverse N) Q tau := by
  have hfilter :
      ((l5PrimeUniverse N).product (l5PrimeUniverse N)).filter
        (fun t => t ∈ P5OriginalU5CausalFinite.pairSupport N) =
      P5OriginalU5CausalFinite.pairSupport N := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun ht => ⟨actual_l5_pair_in_compact_universe hN ht, ht⟩⟩
  rw [actualL5KnotMass_eq_original_totient_sum]
  unfold sourceL5KnotMass
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : t ∈ P5OriginalU5CausalFinite.pairSupport N
  · simp only [hs, true_and, if_true]
  · simp only [hs, false_and, if_false]

/-- Actual source and actual finite adopted knot list, with no pair
coverage or two-dimensional boundary-mass premise. The remaining analytic
input is exactly the one-dimensional reciprocal-prime interval primitive. -/
theorem source_l5_table_knot_mass_le_mertens {N : ℕ} (hN : 2 ≤ N)
    {eps tau : ℝ}
    (hM : PrimeIntervalMertens N a eps (l5PrimeUniverse N)) (htau : 0 ≤ tau) :
    sourceL5KnotMass N actualH248ActiveKnots tau ≤
      ∑ q ∈ actualH248ActiveKnots, ∑ j : Fin 4,
        (∑ p ∈ l5PrimeUniverse N, reciprocalPrime p) *
          (2 * (tau * a / l5PivotSlope j) / a + eps) := by
  rw [source_l5_knot_mass_eq_rectangle hN]
  exact actual_l5_table_knot_mass_le_mertens hN (l5PrimeUniverse N) hM htau

/-- A clamp state has positive volume and is retained as a state. -/
theorem clamped_query_eq_two_iff {L w : ℝ} (hw : 0 < w) :
    max (2 : ℝ) (L / w) = 2 ↔ L ≤ 2 * w := by
  rw [max_eq_left_iff, div_le_iff₀ hw]

/-- Only a query knot separated from the clamp by more than the query
radius can be charged entirely to a proper affine strip. -/
theorem proper_clamped_query_band {L w q tau : ℝ}
    (hw : 0 < w) (hgap : 2 + tau < q)
    (hnear : |max (2 : ℝ) (L / w) - q| ≤ tau) :
    |L - q * w| ≤ tau * w := by
  have hlo := (abs_le.mp hnear).1
  have hraw : 2 < L / w := by
    by_contra h
    have hclamp : max (2 : ℝ) (L / w) = 2 :=
      max_eq_left (le_of_not_gt h)
    rw [hclamp] at hlo
    linarith
  rw [max_eq_right hraw.le] at hnear
  exact (quotient_band_iff hw).mp hnear

end
end ImbalancedChen.P2LowerActualL5FiniteKnotMass
