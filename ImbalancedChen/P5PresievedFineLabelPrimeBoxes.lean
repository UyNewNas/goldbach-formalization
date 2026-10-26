import ImbalancedChen.P5JointPresievedSlotAffineRealization

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual rough fine-label prime boxes: ORIGINAL target exclusions, prime
ceiling, rough lower cutoff and literal half-open log endpoints are kept.
The original residual upper gates hold on a WHOLE certified fine box.
Every fixed three-group assignment has literal product identity and the
actual summed endpoint lengths; no tuplewise regrouping is substituted.
Original per-label coefficient normalization is supplied separately.
-/
namespace ImbalancedChen.P5Z.PresievedFineLabelPrimeBoxes
noncomputable section
open Classical Set
open scoped BigOperators
open PresievedRoughSlotAffineGates

def finePrimeSet (N cap : ℕ) (w Z a b : ℝ) : Finset ℕ :=
  (roughPrimeFinset N cap w Z).filter (fun p => (N : ℝ) ^ a ≤ (p : ℝ) ∧ (p : ℝ) < (N : ℝ) ^ b)

theorem finePrimeSet_prime {N cap p : ℕ} {w Z a b : ℝ}
    (hp : p ∈ finePrimeSet N cap w Z a b) : Nat.Prime p :=
  (mem_roughPrimeFinset.mp (Finset.mem_filter.mp hp).1).2.1

/-- Actual Cartesian slot membership, with every occurrence retained.
Repeated labels remain repeated slots; no factorial is taken here. -/
theorem mem_primeSlotBox_ofFn {ι : Type*} (B : ι → Finset ℕ) :
    ∀ {r : ℕ} (labels : Fin r → ι) (p : Fin r → ℕ),
      List.ofFn p ∈ actualPrimeSlotBox B (List.ofFn labels) ↔ ∀ i, p i ∈ B (labels i) := by
  intro r
  induction r with
  | zero => intro labels p; simp [List.ofFn_zero, actualPrimeSlotBox]
  | succ r ih =>
    intro labels p
    simp only [List.ofFn_succ, actualPrimeSlotBox]
    constructor
    · intro hp
      obtain ⟨⟨q, qs⟩, hpair, heq⟩ := Finset.mem_image.mp hp
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hpair
      obtain ⟨rfl, htail⟩ := List.cons.inj heq
      have hh := (ih (fun i => labels i.succ) (fun i => p i.succ)).mp (htail ▸ hqs)
      intro i
      refine Fin.cases hq (fun j => hh j) i
    · intro hp
      apply Finset.mem_image.mpr
      refine ⟨(p 0, List.ofFn (fun i : Fin r => p i.succ)), ?_, rfl⟩
      exact Finset.mem_product.mpr ⟨hp 0, (ih _ _).mpr (fun i => hp i.succ)⟩

theorem finePrimeSet_log_iff {N cap p : ℕ} (hN : 1 < N) (w Z a b : ℝ) :
    p ∈ finePrimeSet N cap w Z a b ↔ p ∈ roughPrimeFinset N cap w Z ∧
      a ≤ Real.log (p : ℝ) / Real.log (N : ℝ) ∧ Real.log (p : ℝ) / Real.log (N : ℝ) < b := by
  have hn : (1 : ℝ) < N := by exact_mod_cast hN
  constructor
  · intro hp
    obtain ⟨hr, ha, hb⟩ := Finset.mem_filter.mp hp
    have hpos := (mem_roughPrimeFinset.mp hr).2.1.pos
    have hpow : (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = (p : ℝ) :=
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hpos) 0
    refine ⟨hr, ?_, ?_⟩
    · exact (Real.rpow_le_rpow_left_iff hn).mp (by simpa only [hpow] using ha)
    · exact (Real.rpow_lt_rpow_left_iff hn).mp (by simpa only [hpow] using hb)
  · rintro ⟨hr, ha, hb⟩
    have hpos := (mem_roughPrimeFinset.mp hr).2.1.pos
    have hpow : (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = (p : ℝ) :=
      actualPrimeTupleLog_rpow hN (fun _ : Fin 1 => p) (fun _ => hpos) 0
    apply Finset.mem_filter.mpr
    refine ⟨hr, ?_, ?_⟩
    · simpa only [hpow] using (Real.rpow_le_rpow_left_iff hn).mpr ha
    · simpa only [hpow] using (Real.rpow_lt_rpow_left_iff hn).mpr hb

/-- Exact logarithmic product-box dictionary for a literal original
fine-label word. Arithmetic prime and target predicates remain explicit. -/
theorem fine_box_log_dictionary {ι : Type*} {r N : ℕ} (hN : 1 < N) (cap : ℕ)
    (w Z : ℝ) (a b : ι → ℝ) (labels : Fin r → ι) (p : Fin r → ℕ) :
    List.ofFn p ∈ actualPrimeSlotBox (fun i => finePrimeSet N cap w Z (a i) (b i)) (List.ofFn labels) ↔
      (∀ i, p i ∈ roughPrimeFinset N cap w Z) ∧
        actualPrimeTupleLog N p ∈ logPrimeBox (fun i => a (labels i)) (fun i => b (labels i)) := by
  rw [mem_primeSlotBox_ofFn]
  simp only [finePrimeSet_log_iff hN, mem_logPrimeBox, actualPrimeTupleLog]
  constructor
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  · rintro ⟨hr, hl⟩ i
    exact ⟨hr i, hl i⟩

/-- Literal disjointness of the actual half-open prime labels, including
an equality between two adjacent endpoints. This feeds original per-label
factorial normalization without deleting arithmetic endpoint primes. -/
theorem finePrimeSet_disjoint {N cap : ℕ} (hN : 1 < N) (w Z a b c d : ℝ) (hbc : b ≤ c) :
    Disjoint (finePrimeSet N cap w Z a b) (finePrimeSet N cap w Z c d) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hb := (Finset.mem_filter.mp hp).2.2
  have hc := (Finset.mem_filter.mp hq).2.1
  have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.le_of_lt hN)) hbc
  exact (not_lt_of_ge (hpow.trans hc)) hb

/-- Full original upper-prefix admissibility on EVERY tuple of a fine
box, with one set of endpoint tests chosen before arithmetic. -/
theorem original_upper_on_fine_box {ι : Type*} {r N : ℕ} (hN : 1 < N) (cap : ℕ)
    (w Z ell : ℝ) (a b : ι → ℝ) (labels : Fin r → ι)
    (htotal : (∑ i : Fin r, b (labels i)) < ell)
    (hcubes : ∀ i : Fin r, Even i.val → cube (fun j => b (labels j)) i < ell)
    (hsep : ∀ i j : Fin r, i < j → b (labels j) ≤ a (labels i))
    (p : Fin r → ℕ)
    (hp : List.ofFn p ∈ actualPrimeSlotBox (fun i => finePrimeSet N cap w Z (a i) (b i)) (List.ofFn labels)) :
    StrictAnti p ∧ ordinaryRosserPrefixAdmissible false ((N : ℝ) ^ ell) (List.ofFn p).reverse := by
  obtain ⟨hr, hlog⟩ := (fine_box_log_dictionary hN cap w Z a b labels p).mp hp
  have hpos : ∀ i, 0 < p i := fun i => (mem_roughPrimeFinset.mp (hr i)).2.1.pos
  have hlogAnti : StrictAnti (actualPrimeTupleLog N p) := by
    intro i j hij
    exact (mem_logPrimeBox.mp hlog j).2.trans_le
      ((hsep i j hij).trans (mem_logPrimeBox.mp hlog i).1)
  have hanti := (actualPrimeTupleLog_strictAnti_iff hN p hpos).mp hlogAnti
  refine ⟨hanti, (original_upper_prefix_iff_log hN ell p hpos hanti).mpr ?_⟩
  exact fine_box_region ell (fun i => a (labels i)) (fun i => b (labels i)) htotal hcubes hlog

def groupIndices {r : ℕ} (groups : Fin r → Fin 3) (g : Fin 3) : Finset (Fin r) :=
  Finset.univ.filter (fun i => groups i = g)

/-- One assignment on the WHOLE atom preserves the complete product. -/
theorem fixed_group_product {r : ℕ} (groups : Fin r → Fin 3) (p : Fin r → ℕ) :
    (∏ i : Fin r, p i) = ∏ g : Fin 3, ∏ i ∈ groupIndices groups g, p i :=
  (Finset.prod_fiberwise Finset.univ groups p).symm

/-- The actual convolution group lengths are the SUMS of all assigned
upper endpoints. They are not individual-prime bounds or tuplewise bins. -/
theorem fixed_group_length {ι : Type*} {r N : ℕ} (hN : 1 < N) (cap : ℕ)
    (w Z : ℝ) (a b : ι → ℝ) (labels : Fin r → ι) (groups : Fin r → Fin 3)
    (p : Fin r → ℕ)
    (hp : List.ofFn p ∈ actualPrimeSlotBox (fun i => finePrimeSet N cap w Z (a i) (b i)) (List.ofFn labels))
    (g : Fin 3) :
    ((∏ i ∈ groupIndices groups g, p i : ℕ) : ℝ) ≤
      (N : ℝ) ^ (∑ i ∈ groupIndices groups g, b (labels i)) := by
  have hmem := (mem_primeSlotBox_ofFn _ labels p).mp hp
  rw [Nat.cast_prod, Real.rpow_sum_of_pos (by exact_mod_cast (zero_lt_one.trans hN))]
  apply Finset.prod_le_prod (fun i hi => Nat.cast_nonneg _)
  intro i hi
  exact (Finset.mem_filter.mp (hmem i)).2.2.le

end
end ImbalancedChen.P5Z.PresievedFineLabelPrimeBoxes
