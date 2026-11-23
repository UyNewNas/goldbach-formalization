import ImbalancedChen.ActualFrozenSelectedPairSlots

/-!
# Signed tuple coefficients for the same fixed whole-box slot partition

The box below is the original Cartesian product of the finite prime sets
attached to its labelled slots. Consing records every ordered coordinate,
so equal primes or overlapping slot intervals do not discard multiplicity.
Only the original whole box is reordered, using the already computed slot
partition. No decision fibre of a tuplewise greedy run is used as a box.

The original scalar, including any original repeated-label reciprocal
factorial and sign, is retained exactly once. Each of the three resulting
convolution coefficients is normalized by its own slot-count factorial,
with the three factorials restored once in that same scalar. These are
finite identities, not distribution or arithmetic mean estimates.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- The original ordered-coordinate box, with no value-level quotient. -/
def actualPrimeSlotBox {ι : Type*} (B : ι → Finset ℕ) : List ι → Finset (List ℕ)
  | [] => {[]}
  | i :: input => ((B i).product (actualPrimeSlotBox B input)).image
      (fun pq => pq.1 :: pq.2)

theorem actualPrimeSlotBox_sum_cons {ι : Type*} (B : ι → Finset ℕ)
    (i : ι) (input : List ι) (F : List ℕ → ℝ) :
    (∑ ps ∈ actualPrimeSlotBox B (i :: input), F ps) =
      ∑ q ∈ B i, ∑ ps ∈ actualPrimeSlotBox B input, F (q :: ps) := by
  rw [actualPrimeSlotBox, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro a _ b _ h
    apply Prod.ext
    · exact (List.cons.inj h).1
    · exact (List.cons.inj h).2

theorem actualPrimeSlotBox_length {ι : Type*} (B : ι → Finset ℕ) (input : List ι) :
    ∀ ps ∈ actualPrimeSlotBox B input, ps.length = input.length := by
  induction input with
  | nil => simp [actualPrimeSlotBox]
  | cons i input ih =>
      intro ps hps
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      have hqs := (Finset.mem_product.mp hmem).2
      simp only [List.length_cons, ih qs hqs]

theorem actualPrimeSlotBox_prime {ι : Type*} (B : ι → Finset ℕ) (input : List ι)
    (hprime : ∀ i ∈ input, ∀ q ∈ B i, Nat.Prime q) :
    ∀ ps ∈ actualPrimeSlotBox B input, ∀ q ∈ ps, Nat.Prime q := by
  induction input with
  | nil => simp [actualPrimeSlotBox]
  | cons i input ih =>
      intro ps hps
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hprime i (by simp) r hq
      · exact ih (fun j hj => hprime j (List.mem_cons_of_mem i hj)) qs hqs r hr

/-- Every ordered-coordinate tuple in the original group box has the
computed endpoint product bound, including repeated interval labels. -/
theorem actualPrimeSlotBox_prod_le_upper {ι : Type*} (B : ι → Finset ℕ)
    (upper : ι → ℕ) (input : List ι)
    (hsize : ∀ i ∈ input, ∀ q ∈ B i, q ≤ upper i) :
    ∀ ps ∈ actualPrimeSlotBox B input, ps.prod ≤ (input.map upper).prod := by
  induction input with
  | nil => simp [actualPrimeSlotBox]
  | cons i input ih =>
      intro ps hps
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      exact Nat.mul_le_mul (hsize i (by simp) q hq)
        (ih (fun j hj => hsize j (List.mem_cons_of_mem i hj)) qs hqs)

/-- Reordering labelled slots preserves the original Cartesian product
sum for every function of the full product. Overlapping prime sets are
allowed: this is an exact sum commutation, not an injectivity assumption. -/
theorem actualPrimeSlotBox_product_sum_perm {ι : Type*} (B : ι → Finset ℕ)
    {input₁ input₂ : List ι} (hperm : input₁.Perm input₂) (F : ℕ → ℝ) :
    (∑ ps ∈ actualPrimeSlotBox B input₁, F ps.prod) =
      ∑ ps ∈ actualPrimeSlotBox B input₂, F ps.prod := by
  induction hperm generalizing F with
  | nil => rfl
  | cons i hperm ih =>
      rw [actualPrimeSlotBox_sum_cons, actualPrimeSlotBox_sum_cons]
      apply Finset.sum_congr rfl
      intro q _
      simpa only [List.prod_cons] using ih (fun n => F (q * n))
  | swap i j input =>
      simp_rw [actualPrimeSlotBox_sum_cons, List.prod_cons]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro ps _
      congr 1
      ring
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ F).trans (ih₂ F)

/-- The two groups are the full Cartesian coordinate boxes on their
original fixed lists of slots. -/
theorem actualPrimeSlotBox_product_sum_append {ι : Type*} (B : ι → Finset ℕ)
    (left right : List ι) (F : ℕ → ℝ) :
    (∑ ps ∈ actualPrimeSlotBox B (left ++ right), F ps.prod) =
      ∑ ps ∈ actualPrimeSlotBox B left, ∑ qs ∈ actualPrimeSlotBox B right,
        F (ps.prod * qs.prod) := by
  induction left generalizing F with
  | nil => simp [actualPrimeSlotBox]
  | cons i left ih =>
      rw [List.cons_append, actualPrimeSlotBox_sum_cons, actualPrimeSlotBox_sum_cons]
      apply Finset.sum_congr rfl
      intro q _
      simpa only [List.prod_cons, mul_assoc] using ih (fun n => F (q * n))

/-- Grouping by a product counts its complete ordered-tuple fibre. -/
theorem actualPrimeTuple_sum_by_product (T : Finset (List ℕ)) (F : ℕ → ℝ) :
    (∑ ps ∈ T, F ps.prod) =
      ∑ n ∈ T.image List.prod, (actualPrimeTupleCoefficient T n : ℝ) * F n := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun ps hps => Finset.mem_image_of_mem List.prod hps) (fun ps => F ps.prod)]
  apply Finset.sum_congr rfl
  intro n _
  calc
    (∑ ps ∈ T.filter (fun ps => ps.prod = n), F ps.prod) =
        ∑ _ps ∈ T.filter (fun ps => ps.prod = n), F n := by
      apply Finset.sum_congr rfl
      intro ps hps
      rw [(Finset.mem_filter.mp hps).2]
    _ = (actualPrimeTupleCoefficient T n : ℝ) * F n := by
      simp only [actualPrimeTupleCoefficient, Finset.sum_const, nsmul_eq_mul]

/-- An exact three-group convolution identity with its single factorial
normalization. The arbitrary signed scalar c is never replaced by an
absolute value or by a fresh repeated-label normalization. -/
theorem actualPrimeTuple_threeGroup_sum_normalized
    (T₁ T₂ T₃ : Finset (List ℕ)) (m₁ m₂ m₃ : ℕ) (c : ℝ) (H : ℕ → ℝ) :
    (∑ ps ∈ T₁, ∑ qs ∈ T₂, ∑ rs ∈ T₃, c * H (ps.prod * qs.prod * rs.prod)) =
      ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod, ∑ d ∈ T₃.image List.prod,
        (c * (m₁.factorial : ℝ) * (m₂.factorial : ℝ) * (m₃.factorial : ℝ)) *
          actualNormalizedPrimeTupleCoefficient T₁ m₁ a *
          actualNormalizedPrimeTupleCoefficient T₂ m₂ b *
          actualNormalizedPrimeTupleCoefficient T₃ m₃ d * H (a * b * d) := by
  rw [actualPrimeTuple_sum_by_product T₁
    (fun a => ∑ qs ∈ T₂, ∑ rs ∈ T₃, c * H (a * qs.prod * rs.prod))]
  apply Finset.sum_congr rfl
  intro a _
  rw [actualPrimeTuple_sum_by_product T₂
    (fun b => ∑ rs ∈ T₃, c * H (a * b * rs.prod))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [actualPrimeTuple_sum_by_product T₃ (fun d => c * H (a * b * d))]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  calc
    _ = (c * (actualPrimeTupleCoefficient T₁ a : ℝ) *
        (actualPrimeTupleCoefficient T₂ b : ℝ) * (actualPrimeTupleCoefficient T₃ d : ℝ)) *
          H (a * b * d) := by ring
    _ = _ := by rw [actualPrimeTuple_threeGroup_scalar_identity c T₁ T₂ T₃ m₁ m₂ m₃ a b d]

/-- The original signed box sum is regrouped by the exact same three slot
lists that supply its upper endpoint targets. This is a permutation of a
whole original Cartesian box, never a claim about tuple decision fibres. -/
theorem actualFrozenSelectedPair_signed_regroup {ι : Type*}
    (D A : ℝ) (yz : Bool) (upper : ι → ℕ) (p : Fin 3 → ι) (tail : List ι)
    (B : ι → Finset ℕ) (c : ℝ) (H : ℕ → ℝ) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    let T₁ := actualPrimeSlotBox B slots.1
    let T₂ := actualPrimeSlotBox B slots.2.1
    let T₃ := actualPrimeSlotBox B slots.2.2
    (∑ ps ∈ actualPrimeSlotBox B (p 0 :: p 1 :: p 2 :: tail), c * H ps.prod) =
      ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod, ∑ d ∈ T₃.image List.prod,
        (c * (slots.1.length.factorial : ℝ) * (slots.2.1.length.factorial : ℝ) *
          (slots.2.2.length.factorial : ℝ)) *
          actualNormalizedPrimeTupleCoefficient T₁ slots.1.length a *
          actualNormalizedPrimeTupleCoefficient T₂ slots.2.1.length b *
          actualNormalizedPrimeTupleCoefficient T₃ slots.2.2.length d * H (a * b * d) := by
  dsimp only
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  rw [← actualPrimeSlotBox_product_sum_perm B
    (actualFrozenSelectedPairSlots_perm D A yz upper p tail) (fun n => c * H n)]
  rw [List.append_assoc]
  rw [actualPrimeSlotBox_product_sum_append B slots.1 (slots.2.1 ++ slots.2.2)
    (fun n => c * H n)]
  have hright (a : ℕ) := actualPrimeSlotBox_product_sum_append B slots.2.1 slots.2.2
    (fun n => c * H (a * n))
  simp_rw [hright]
  simpa only [mul_assoc] using actualPrimeTuple_threeGroup_sum_normalized
    (actualPrimeSlotBox B slots.1) (actualPrimeSlotBox B slots.2.1)
    (actualPrimeSlotBox B slots.2.2) slots.1.length slots.2.1.length slots.2.2.length c H

/-- The actual product carriers in that exact regrouping have the three
upper factors proved by the whole-cell endpoint consumer. Each product
fibre is counted inside its original group box, with no fibre-as-box claim. -/
theorem actualFrozenSelectedPair_group_support {ι : Type*}
    (D A : ℝ) (yz : Bool) (upper : ι → ℕ) (p : Fin 3 → ι) (tail : List ι)
    (B : ι → Finset ℕ)
    (hsize : ∀ i ∈ p 0 :: p 1 :: p 2 :: tail, ∀ q ∈ B i, q ≤ upper i) :
    let slots := actualFrozenSelectedPairSlots D A yz upper p tail
    let abc := actualFrozenSelectedPairFactors D A yz upper upper p tail
    (∀ a ∈ (actualPrimeSlotBox B slots.1).image List.prod, a ≤ abc.1) ∧
      (∀ b ∈ (actualPrimeSlotBox B slots.2.1).image List.prod, b ≤ abc.2.1) ∧
      (∀ d ∈ (actualPrimeSlotBox B slots.2.2).image List.prod, d ≤ abc.2.2) := by
  let slots := actualFrozenSelectedPairSlots D A yz upper p tail
  have hperm := actualFrozenSelectedPairSlots_perm D A yz upper p tail
  have hbound (l : List ι) (hmem : ∀ i ∈ l, i ∈ p 0 :: p 1 :: p 2 :: tail) :
      ∀ n ∈ (actualPrimeSlotBox B l).image List.prod, n ≤ (l.map upper).prod := by
    intro n hn
    obtain ⟨ps, hps, rfl⟩ := Finset.mem_image.mp hn
    exact actualPrimeSlotBox_prod_le_upper B upper l
      (fun i hi => hsize i (hmem i hi)) ps hps
  exact ⟨hbound slots.1 (fun i hi => hperm.mem_iff.mp (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hi))))),
    hbound slots.2.1 (fun i hi => hperm.mem_iff.mp
      (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hi))))),
    hbound slots.2.2 (fun i hi => hperm.mem_iff.mp
      (List.mem_append.mpr (Or.inr hi)))⟩

/-- Every resulting convolution coefficient has its proved one-bound on
all integers, even when different original interval labels overlap. -/
theorem actualPrimeSlotBox_normalized_abs_le_one {ι : Type*}
    (B : ι → Finset ℕ) (input : List ι)
    (hprime : ∀ i ∈ input, ∀ q ∈ B i, Nat.Prime q) (n : ℕ) :
    |actualNormalizedPrimeTupleCoefficient (actualPrimeSlotBox B input) input.length n| ≤ 1 := by
  exact actualNormalizedPrimeTupleCoefficient_abs_le_one _ _ n
    (actualPrimeSlotBox_length B input) (actualPrimeSlotBox_prime B input hprime)

end

end ImbalancedChen
