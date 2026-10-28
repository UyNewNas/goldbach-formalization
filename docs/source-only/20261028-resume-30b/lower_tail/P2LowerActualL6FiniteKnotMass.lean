import ImbalancedChen.P2LowerActualL5FiniteKnotMass
import ImbalancedChen.CurrentChenUpsilon6LogDomain

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The complete actual retained L6 source is used, not only its strict
ordinary inner selector. Its original deletion mask and product buffer
remain in the finite sum. Exact prime-band geometry proves coverage by
the compact prime universe. Closed h248 query strips are then paid by
one-prime Mertens and finite Fubini with the original reciprocal totient.

`query` is the original analytic residual (1/2-u-t)/a. No identity with
the rounded physical lower-row level, and no h248 count mean, is asserted.
-/

namespace ImbalancedChen.P2LowerActualL6FiniteKnotMass

noncomputable section
open scoped Classical BigOperators
open P2LowerFinitePrimeBandMass P2LowerCapPlanIntegerRetention
open P2LowerActualL5FiniteKnotMass P2LowerActualL5L6PrimeKnots
open P2LowerH248QueryKnotDictionary

private abbrev a : ℝ := Part5OriginalUpsilon5CausalDictionary.a
private abbrev d : ℝ := 59 / 250

def query (N : ℕ) (t : ℕ × ℕ) : ℝ :=
  ((1 / 2 : ℝ) - coordinate N t.1 - coordinate N t.2) / a

theorem query_eq_original_profile (N : ℕ) (t : ℕ × ℕ) :
    query N t = currentChenUpsilon6OrdinaryProfile (l6Coordinates N t) := rfl

/-- No floor or physical level is substituted into this analytic query. -/
theorem query_band_iff (N : ℕ) (t : ℕ × ℕ) (q tau : ℝ) :
    |query N t - q| ≤ tau ↔
      |coordinate N t.1 + (q * a + coordinate N t.2 - 1 / 2)| ≤ tau * a := by
  have ha : 0 < a := by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  rw [query, quotient_band_iff ha]
  have heq : (1 / 2 : ℝ) - coordinate N t.1 - coordinate N t.2 - q * a =
      -(coordinate N t.1 + (q * a + coordinate N t.2 - 1 / 2)) := by ring
  rw [heq, abs_neg]

def primeUniverse (N : ℕ) : Finset ℕ :=
  (chenAdditivePrimeCarrier N).filter (fun p =>
    a ≤ coordinate N p ∧ coordinate N p ≤ d)

/-- Every retained actual pair, with its unchanged E mask, lies in the
explicit compact universe. There is no caller-supplied coverage premise. -/
theorem retained_pair_in_compact_universe {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) (beta : ℝ) {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6RetainedSelector N E beta) :
    t ∈ (primeUniverse N).product (primeUniverse N) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  obtain ⟨hp, hq, hE, hx⟩ :=
    (mem_currentChenUpsilon6RetainedSelector_log_iff hNr E beta t).mp ht
  have hcoords : a ≤ coordinate N t.1 ∧ coordinate N t.1 < 19 / 125 ∧
      (19 / 125 : ℝ) ≤ coordinate N t.2 ∧ coordinate N t.2 < d := by
    simpa [currentChenUpsilon6LogCoordinates, coordinate, a,
      Part5OriginalUpsilon5CausalDictionary.a, d] using
      (mem_currentChenUpsilon6LogRectangle.mp hx.1)
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨hp, hcoords.1, ?_⟩
    exact hcoords.2.1.le.trans (by norm_num [d])
  · apply Finset.mem_filter.mpr
    refine ⟨hq, ?_, hcoords.2.2.2.le⟩
    exact (by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a] :
      a ≤ (19 / 125 : ℝ)).trans hcoords.2.2.1

/-- The original sixth bands are disjoint. They prove prime distinctness
and hence the exact original reciprocal-totient weight. -/
theorem retained_pairWeight_eq_original_totient (N : ℕ)
    (E : ℕ × ℕ → Prop) (beta : ℝ) {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6RetainedSelector N E beta) :
    pairWeight t = 1 / (Nat.totient (t.1 * t.2) : ℝ) := by
  have hraw := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).1).1
  obtain ⟨hc, hA, hH, hH', hD⟩ := Finset.mem_filter.mp hraw
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  have hpprime := (mem_chenAdditivePrimeCarrier.mp hp).2.1
  have hqprime := (mem_chenAdditivePrimeCarrier.mp hq).2.1
  have horder : t.1 < t.2 := by exact_mod_cast (hH.trans_le hH')
  have hcop : Nat.Coprime t.1 t.2 :=
    (Nat.coprime_primes hpprime hqprime).mpr (ne_of_lt horder)
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  simp [pairWeight, reciprocalPrime, one_div_mul_one_div]

/-- This membership still belongs to the same signed lower coefficient
bank. It assigns neither its mean nor its physical level to `query`. -/
theorem retained_pair_in_native_lowerRows (N : ℕ)
    (E : ℕ × ℕ → Prop) (beta : ℝ) {t : ℕ × ℕ}
    (ht : t ∈ currentChenUpsilon6RetainedSelector N E beta) :
    t ∈ P5JointNativeSignedRegroup.lowerRows N E := by
  exact (Finset.mem_filter.mp ht).1

/-- Exact active h248 gate on the original native lowerRows. This uses
the original half-level analytic residual and actual prime product, and
does not identify either with a rounded compiled lower-row level. -/
theorem original_query_ge_two_iff_product_bound {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) {t : ℕ × ℕ}
    (ht : t ∈ P5JointNativeSignedRegroup.lowerRows N E) :
    2 ≤ query N t ↔ ((t.1 * t.2 : ℕ) : ℝ) ≤
      (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ)) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hraw := (Finset.mem_filter.mp ht).1
  have hc := (Finset.mem_filter.mp hraw).1
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hc
  have hp0 := (mem_chenAdditivePrimeCarrier.mp hp).2.1.pos
  have hq0 := (mem_chenAdditivePrimeCarrier.mp hq).2.1.pos
  have hpow : (N : ℝ) ^ (coordinate N t.1 + coordinate N t.2) =
      ((t.1 * t.2 : ℕ) : ℝ) := by
    rw [Real.rpow_add (zero_lt_one.trans hNr),
      coordinate_power hNr hp0, coordinate_power hNr hq0, Nat.cast_mul]
  have ha : 0 < a := by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  rw [← hpow, Real.rpow_le_rpow_left_iff hNr, query, le_div_iff₀ ha]
  norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  constructor <;> intro h <;> linarith

def activeOriginalSource (N : ℕ) (E : ℕ × ℕ → Prop) : Finset (ℕ × ℕ) :=
  (P5JointNativeSignedRegroup.lowerRows N E).filter (fun t => 2 ≤ query N t)

/-- At beta=0 this is the entire genuine h248-active L6 occurrence,
including the equality query=2, not only its strict ordinary inner set. -/
theorem active_original_source_eq_retained_zero {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) :
    activeOriginalSource N E = currentChenUpsilon6RetainedSelector N E 0 := by
  ext t
  change (t ∈ P5JointNativeSignedRegroup.lowerRows N E ∧ 2 ≤ query N t) ↔
    (t ∈ P5JointNativeSignedRegroup.lowerRows N E ∧
      ((t.1 * t.2 : ℕ) : ℝ) ≤
        (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - 0))
  rw [sub_zero]
  constructor
  · rintro ⟨ht, hq⟩
    exact ⟨ht, (original_query_ge_two_iff_product_bound hN E ht).mp hq⟩
  · rintro ⟨ht, hp⟩
    exact ⟨ht, (original_query_ge_two_iff_product_bound hN E ht).mpr hp⟩

def stripTerm (N : ℕ) (q tau : ℝ) (t : ℕ × ℕ) : ℝ :=
  if |coordinate N t.1 + (q * a + coordinate N t.2 - 1 / 2)| ≤ tau * a
  then pairWeight t else 0

theorem stripTerm_nonneg (N : ℕ) (q tau : ℝ) (t : ℕ × ℕ) :
    0 ≤ stripTerm N q tau t := by
  unfold stripTerm
  split_ifs
  · exact pairWeight_nonneg _
  · exact le_rfl

theorem strip_rectangle_eq_fibres (N : ℕ) (S : Finset ℕ) (q tau : ℝ) :
    (∑ t ∈ S.product S, stripTerm N q tau t) =
      ∑ r ∈ S, reciprocalPrime r *
        (∑ p ∈ S,
          if |coordinate N p + (q * a + coordinate N r - 1 / 2)| ≤ tau * a
          then reciprocalPrime p else 0) := by
  rw [Finset.sum_product, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  unfold stripTerm pairWeight
  split_ifs <;> ring

theorem strip_rectangle_le_mertens (N : ℕ) (S : Finset ℕ)
    {eta eps : ℝ} (hM : PrimeIntervalMertens N eta eps S)
    (q tau : ℝ) (htau : 0 ≤ tau) :
    (∑ t ∈ S.product S, stripTerm N q tau t) ≤
      (∑ p ∈ S, reciprocalPrime p) * (2 * (tau * a) / eta + eps) := by
  have ha : 0 ≤ a := by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  rw [strip_rectangle_eq_fibres, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  exact mul_le_mul_of_nonneg_left
    (l6_closed_prime_strip N S hM q (coordinate N r) (tau * a)
      (mul_nonneg htau ha)) (reciprocalPrime_nonneg r)

/-- An arithmetic union over the genuine query, including equality. -/
def rectangleSourceMass (N : ℕ) (E : ℕ × ℕ → Prop) (beta : ℝ)
    (S : Finset ℕ) (Q : Finset ℝ) (tau : ℝ) : ℝ :=
  ∑ t ∈ S.product S,
    if t ∈ currentChenUpsilon6RetainedSelector N E beta ∧
      ∃ q ∈ Q, |query N t - q| ≤ tau
    then pairWeight t else 0

theorem rectangle_source_mass_le_strip_sum (N : ℕ) (E : ℕ × ℕ → Prop)
    (beta : ℝ) (S : Finset ℕ) (Q : Finset ℝ) (tau : ℝ) :
    rectangleSourceMass N E beta S Q tau ≤
      ∑ t ∈ S.product S, ∑ q ∈ Q, stripTerm N q tau t := by
  unfold rectangleSourceMass
  apply Finset.sum_le_sum
  intro t ht
  by_cases h : t ∈ currentChenUpsilon6RetainedSelector N E beta ∧
      ∃ q ∈ Q, |query N t - q| ≤ tau
  · rw [if_pos h]
    obtain ⟨hs, q, hq, hnear⟩ := h
    have hstrip := (query_band_iff N t q tau).mp hnear
    have hsingle := Finset.single_le_sum
      (fun q' _ => stripTerm_nonneg N q' tau t) hq
    simpa only [stripTerm, if_pos hstrip] using hsingle
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun q _ => stripTerm_nonneg N q tau t)

def sourceMass (N : ℕ) (E : ℕ × ℕ → Prop) (beta : ℝ)
    (Q : Finset ℝ) (tau : ℝ) : ℝ :=
  ∑ t ∈ currentChenUpsilon6RetainedSelector N E beta,
    if ∃ q ∈ Q, |query N t - q| ≤ tau
    then 1 / (Nat.totient (t.1 * t.2) : ℝ) else 0

theorem source_mass_eq_rectangle {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) (beta : ℝ) (Q : Finset ℝ) (tau : ℝ) :
    sourceMass N E beta Q tau =
      rectangleSourceMass N E beta (primeUniverse N) Q tau := by
  have hfilter : ((primeUniverse N).product (primeUniverse N)).filter
      (fun t => t ∈ currentChenUpsilon6RetainedSelector N E beta) =
      currentChenUpsilon6RetainedSelector N E beta := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun ht =>
      ⟨retained_pair_in_compact_universe hN E beta ht, ht⟩⟩
  unfold sourceMass rectangleSourceMass
  conv_lhs => rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hs : t ∈ currentChenUpsilon6RetainedSelector N E beta
  · rw [if_pos hs]
    by_cases hk : ∃ q ∈ Q, |query N t - q| ≤ tau
    · rw [if_pos hk, if_pos ⟨hs, hk⟩]
      exact (retained_pairWeight_eq_original_totient N E beta hs).symm
    · rw [if_neg hk, if_neg (by simp only [hs, true_and, hk, not_false_eq_true])]
  · rw [if_neg hs, if_neg (by simp only [hs, false_and, not_false_eq_true])]

/-- The whole actual retained L6 occurrence, at the same E and beta, is
paid by explicit finite one-prime interval estimates. No two-dimensional
boundary loss or physical-row density estimate is assumed. -/
theorem source_finite_knot_mass_le_mertens {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) (beta : ℝ) (Q : Finset ℝ)
    {eps tau : ℝ}
    (hM : PrimeIntervalMertens N a eps (primeUniverse N)) (htau : 0 ≤ tau) :
    sourceMass N E beta Q tau ≤
      ∑ q ∈ Q, (∑ p ∈ primeUniverse N, reciprocalPrime p) * (2 * tau + eps) := by
  rw [source_mass_eq_rectangle hN]
  apply (rectangle_source_mass_le_strip_sum N E beta (primeUniverse N) Q tau).trans
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro q hq
  have h := strip_rectangle_le_mertens N (primeUniverse N) hM q tau htau
  have ha : a ≠ 0 := by norm_num [a, Part5OriginalUpsilon5CausalDictionary.a]
  have hscale : 2 * (tau * a) / a = 2 * tau := by field_simp [ha]
  simpa only [hscale] using h

theorem source_actual_table_knot_mass_le_mertens {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) (beta : ℝ) {eps tau : ℝ}
    (hM : PrimeIntervalMertens N a eps (primeUniverse N)) (htau : 0 ≤ tau) :
    sourceMass N E beta actualH248ActiveKnots tau ≤
      ((actualH248ActiveKnots.card : ℕ) : ℝ) *
        (∑ p ∈ primeUniverse N, reciprocalPrime p) * (2 * tau + eps) := by
  have h := source_finite_knot_mass_le_mertens hN E beta actualH248ActiveKnots hM htau
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using h

/-- The final caller mentions the original signed lowerRows and its
entire active query region. The paired-deletion mask is unchanged, all
closed knots are retained, and physical mean semantics remain separate. -/
theorem active_original_table_knot_mass_le_mertens {N : ℕ} (hN : 2 ≤ N)
    (E : ℕ × ℕ → Prop) {eps tau : ℝ}
    (hM : PrimeIntervalMertens N a eps (primeUniverse N)) (htau : 0 ≤ tau) :
    (∑ t ∈ activeOriginalSource N E,
      if ∃ q ∈ actualH248ActiveKnots, |query N t - q| ≤ tau
      then 1 / (Nat.totient (t.1 * t.2) : ℝ) else 0) ≤
      ((actualH248ActiveKnots.card : ℕ) : ℝ) *
        (∑ p ∈ primeUniverse N, reciprocalPrime p) * (2 * tau + eps) := by
  rw [active_original_source_eq_retained_zero hN]
  exact source_actual_table_knot_mass_le_mertens hN E 0 hM htau

end
end ImbalancedChen.P2LowerActualL6FiniteKnotMass
