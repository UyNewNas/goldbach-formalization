import ImbalancedChen.ActualPrimeMultiLabelNormalization
import ImbalancedChen.RoughPrimeUniverse

/-!
# Unique full products for disjoint original prime-label blocks

Unique prime factorization and filtering by a label separate its block
product from all remaining block products. Thus the preceding explicit
product-vector sum is exactly a sum over its full product image when the
distinct label supports are disjoint. Repeated values inside a block
remain present; their literal Mobius coefficient still pays the diagonal.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

theorem actualPrimeSlotBox_mem_append {ι : Type*} (B : ι → Finset ℕ)
    (left right : List ι) (ps : List ℕ) :
    ps ∈ actualPrimeSlotBox B (left ++ right) ↔
      ∃ qs ∈ actualPrimeSlotBox B left, ∃ rs ∈ actualPrimeSlotBox B right,
        ps = qs ++ rs := by
  induction left generalizing ps with
  | nil => simp [actualPrimeSlotBox]
  | cons i left ih =>
      constructor
      · intro hps
        rw [List.cons_append, actualPrimeSlotBox] at hps
        obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
        obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
        obtain ⟨as, has, bs, hbs, rfl⟩ := (ih qs).mp hqs
        refine ⟨q :: as, ?_, bs, hbs, rfl⟩
        exact Finset.mem_image.mpr ⟨(q, as), Finset.mem_product.mpr ⟨hq, has⟩, rfl⟩
      · rintro ⟨as, has, bs, hbs, rfl⟩
        obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp has
        obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
        rw [List.cons_append, actualPrimeSlotBox]
        exact Finset.mem_image.mpr ⟨(q, qs ++ bs), Finset.mem_product.mpr
          ⟨hq, (ih _).mpr ⟨qs, hqs, bs, hbs, rfl⟩⟩, rfl⟩

theorem actualPrimeSlotBox_product_image_append {ι : Type*} (B : ι → Finset ℕ)
    (left right : List ι) :
    (actualPrimeSlotBox B (left ++ right)).image List.prod =
      (((actualPrimeSlotBox B left).image List.prod).product
        ((actualPrimeSlotBox B right).image List.prod)).image (fun p => p.1 * p.2) := by
  ext n
  constructor
  · intro hn
    obtain ⟨ps, hps, hprod⟩ := Finset.mem_image.mp hn
    obtain ⟨qs, hqs, rs, hrs, rfl⟩ := (actualPrimeSlotBox_mem_append B left right ps).mp hps
    refine Finset.mem_image.mpr ⟨(qs.prod, rs.prod), Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hqs, Finset.mem_image_of_mem _ hrs⟩, ?_⟩
    simpa only [List.prod_append] using hprod
  · intro hn
    obtain ⟨⟨a, b⟩, hab, hprod⟩ := Finset.mem_image.mp hn
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨qs, hqs, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hb
    refine Finset.mem_image.mpr ⟨qs ++ rs,
      (actualPrimeSlotBox_mem_append B left right _).mpr ⟨qs, hqs, rs, hrs, rfl⟩, ?_⟩
    simpa only [List.prod_append] using hprod

theorem actualPrimeSlotBox_forall {ι : Type*} (B : ι → Finset ℕ) (input : List ι)
    (P : ℕ → Prop) (hP : ∀ i ∈ input, ∀ q ∈ B i, P q) :
    ∀ ps ∈ actualPrimeSlotBox B input, ∀ q ∈ ps, P q := by
  induction input with
  | nil => simp [actualPrimeSlotBox]
  | cons i input ih =>
      intro ps hps
      obtain ⟨⟨q, qs⟩, hmem, rfl⟩ := Finset.mem_image.mp hps
      obtain ⟨hq, hqs⟩ := Finset.mem_product.mp hmem
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hP i (by simp) q hq
      · exact ih (fun j hj => hP j (List.mem_cons_of_mem i hj)) qs hqs r hr

theorem actualPrimeLabelBlocksWord_mem {ι : Type*} {blocks : List (ι × ℕ)} {i : ι}
    (hi : i ∈ actualPrimeLabelBlocksWord blocks) : ∃ b ∈ blocks, i = b.1 := by
  obtain ⟨b, hb, hi⟩ := List.mem_flatMap.mp hi
  exact ⟨b, hb, (List.mem_replicate.mp hi).2⟩

/-- The equality of full prime products separates the two original label
supports. The conclusion holds even before a squarefree restriction. -/
theorem actualPrimeVector_split_product_eq (C : Finset ℕ)
    (as bs cs ds : List ℕ)
    (hprime₁ : ∀ q ∈ as ++ bs, Nat.Prime q)
    (hprime₂ : ∀ q ∈ cs ++ ds, Nat.Prime q)
    (ha : ∀ q ∈ as, q ∈ C) (hb : ∀ q ∈ bs, q ∉ C)
    (hc : ∀ q ∈ cs, q ∈ C) (hd : ∀ q ∈ ds, q ∉ C)
    (hprod : as.prod * bs.prod = cs.prod * ds.prod) :
    as.prod = cs.prod ∧ bs.prod = ds.prod := by
  have hfull : (as ++ bs).prod = (cs ++ ds).prod := by
    simpa only [List.prod_append] using hprod
  have hperm := (Nat.primeFactorsList_unique hfull hprime₁).trans
    (Nat.primeFactorsList_unique (rfl : (cs ++ ds).prod = (cs ++ ds).prod) hprime₂).symm
  have hkeep (P : ℕ → Prop) (l : List ℕ) (h : ∀ q ∈ l, P q) :
      l.filter (fun q => decide (P q)) = l :=
    List.filter_eq_self.mpr (fun q hq => by simpa using h q hq)
  have hdrop (P : ℕ → Prop) (l : List ℕ) (h : ∀ q ∈ l, ¬P q) :
      l.filter (fun q => decide (P q)) = [] :=
    List.filter_eq_nil_iff.mpr (fun q hq => by simpa using h q hq)
  have hhead : as.Perm cs := by
    simpa only [List.filter_append, hkeep _ as ha, hdrop _ bs hb,
      hkeep _ cs hc, hdrop _ ds hd, List.append_nil] using
        List.Perm.filter (fun q => decide (q ∈ C)) hperm
  have htail : bs.Perm ds := by
    simpa only [List.filter_append,
      hdrop _ as (fun q hq hn => hn (ha q hq)), hkeep _ bs hb,
      hdrop _ cs (fun q hq hn => hn (hc q hq)), hkeep _ ds hd,
      List.nil_append] using List.Perm.filter (fun q => decide (q ∉ C)) hperm
  exact ⟨hhead.prod_eq, htail.prod_eq⟩

theorem actualPrimeTuple_product_injective_of_disjoint (C : Finset ℕ)
    (T U : Finset (List ℕ))
    (hTprime : ∀ ps ∈ T, ∀ q ∈ ps, Nat.Prime q)
    (hUprime : ∀ ps ∈ U, ∀ q ∈ ps, Nat.Prime q)
    (hTin : ∀ ps ∈ T, ∀ q ∈ ps, q ∈ C)
    (hUout : ∀ ps ∈ U, ∀ q ∈ ps, q ∉ C) :
    ∀ a ∈ (T.image List.prod).product (U.image List.prod),
      ∀ b ∈ (T.image List.prod).product (U.image List.prod),
        a.1 * a.2 = b.1 * b.2 → a = b := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd hprod
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
  obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
  obtain ⟨as, has, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨bs, hbs, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨cs, hcs, rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨ds, hds, rfl⟩ := Finset.mem_image.mp hd
  have hsplit := actualPrimeVector_split_product_eq C as bs cs ds
    (fun q hq => (List.mem_append.mp hq).elim (hTprime as has q) (hUprime bs hbs q))
    (fun q hq => (List.mem_append.mp hq).elim (hTprime cs hcs q) (hUprime ds hds q))
    (hTin as has) (hUout bs hbs) (hTin cs hcs) (hUout ds hds) hprod
  exact Prod.ext hsplit.1 hsplit.2

/-- Disjoint distinct label supports make the full product-vector map
injective. This is proved from actual prime factorization, not supplied as
a coefficient or fibre-uniqueness premise. -/
theorem actualPrimeLabelBlockProductSum_eq_product_sum {ι : Type*} (B : ι → Finset ℕ) :
    ∀ (blocks : List (ι × ℕ)) (H : ℕ → ℝ),
      (∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q) →
      blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1)) →
      actualPrimeLabelBlockProductSum B blocks H =
        ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).image List.prod, H n := by
  intro blocks
  induction blocks with
  | nil =>
      intro H _hprime _hdisjoint
      simp [actualPrimeLabelBlockProductSum, actualPrimeLabelBlocksWord, actualPrimeSlotBox]
  | cons b blocks ih =>
      rcases b with ⟨i, m⟩
      intro H hprime hdisjoint
      have hhead := hprime (i, m) (by simp)
      have htail : ∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q :=
        fun b hb => hprime b (List.mem_cons_of_mem (i, m) hb)
      obtain ⟨hcross, hdisjointTail⟩ := List.pairwise_cons.mp hdisjoint
      let T := actualPrimeSlotBox B (List.replicate m i)
      let U := actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)
      have hTin : ∀ ps ∈ T, ∀ q ∈ ps, q ∈ B i := by
        intro ps hps
        have hps' := (actualPrimeSlotBox_replicate_label_eq B i m) ▸ hps
        exact ((mem_actualPrimeSlotBox_replicate (B i) m ps).mp hps').2
      have hUprime : ∀ ps ∈ U, ∀ q ∈ ps, Nat.Prime q :=
        actualPrimeSlotBox_prime B _ (fun j hj => by
          obtain ⟨b, hb, rfl⟩ := actualPrimeLabelBlocksWord_mem hj
          exact htail b hb)
      have hUout : ∀ ps ∈ U, ∀ q ∈ ps, q ∉ B i :=
        actualPrimeSlotBox_forall B _ (fun q => q ∉ B i) (by
          intro j hj q hq hqi
          obtain ⟨b, hb, rfl⟩ := actualPrimeLabelBlocksWord_mem hj
          exact Finset.disjoint_left.mp (hcross b hb) hqi hq)
      have hinj := actualPrimeTuple_product_injective_of_disjoint (B i) T U
        (fun ps hps q hq => hhead q (hTin ps hps q hq)) hUprime hTin hUout
      have himage :
          (actualPrimeSlotBox B (actualPrimeLabelBlocksWord ((i, m) :: blocks))).image List.prod =
            ((T.image List.prod).product (U.image List.prod)).image (fun p => p.1 * p.2) :=
        actualPrimeSlotBox_product_image_append B (List.replicate m i)
          (actualPrimeLabelBlocksWord blocks)
      calc
        _ = ∑ a ∈ T.image List.prod,
            actualPrimeLabelBlockProductSum B blocks (fun b => H (a * b)) := rfl
        _ = ∑ a ∈ T.image List.prod, ∑ b ∈ U.image List.prod, H (a * b) := by
          apply Finset.sum_congr rfl
          intro a _
          exact ih (fun b => H (a * b)) htail hdisjointTail
        _ = ∑ p ∈ (T.image List.prod).product (U.image List.prod), H (p.1 * p.2) :=
          (Finset.sum_product _ _ _).symm
        _ = ∑ n ∈ ((T.image List.prod).product (U.image List.prod)).image
              (fun p => p.1 * p.2), H n := by
          rw [Finset.sum_image]
          exact hinj
        _ = _ := by rw [← himage]

theorem actualPrimeLabelBlocks_moebius_sum_disjoint {ι : Type*}
    (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (r : ℕ) (H : ℕ → ℝ)
    (hprime : ∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q)
    (hdisjoint : blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1))) :
    (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
        (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      ∑ n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).image List.prod,
        (ArithmeticFunction.moebius (r * n) : ℝ) * H n := by
  rw [actualPrimeLabelBlocks_moebius_sum_normalized B blocks r H hprime]
  exact actualPrimeLabelBlockProductSum_eq_product_sum B blocks _ hprime hdisjoint

theorem actualPrimeLabelBlocks_moebius_fibre_disjoint {ι : Type*}
    (B : ι → Finset ℕ) (blocks : List (ι × ℕ)) (r n : ℕ)
    (hprime : ∀ b ∈ blocks, ∀ q ∈ B b.1, Nat.Prime q)
    (hdisjoint : blocks.Pairwise (fun b c => Disjoint (B b.1) (B c.1))) :
    ((ArithmeticFunction.moebius (r * n) : ℝ) * actualPrimeTupleCoefficient
        (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)) n) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      if n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).image List.prod
        then (ArithmeticFunction.moebius (r * n) : ℝ) else 0 := by
  rw [actualPrimeLabelBlocks_moebius_fibre_normalized B blocks r n hprime,
    actualPrimeLabelBlockProductSum_eq_product_sum B blocks _ hprime hdisjoint]
  by_cases hn : n ∈ (actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks)).image List.prod
  · simp [hn]
  · simp [hn]

/-- The original half-open fine interval, with exclusion of divisors of
the same target. The ceiling only enumerates the finite set: membership
below removes it and retains the literal real endpoints. -/
def actualPrimeFineLabelFinset (N : ℕ) (τ : ℝ) (j : ℕ) : Finset ℕ :=
  roughPrimeFinset N (Nat.ceil ((N : ℝ) ^ (τ * ((j : ℝ) + 1))))
    ((N : ℝ) ^ (τ * j)) ((N : ℝ) ^ (τ * ((j : ℝ) + 1)))

theorem mem_actualPrimeFineLabelFinset {N j p : ℕ} {τ : ℝ} :
    p ∈ actualPrimeFineLabelFinset N τ j ↔
      p.Prime ∧ ¬p ∣ N ∧ (N : ℝ) ^ (τ * j) ≤ (p : ℝ) ∧
        (p : ℝ) < (N : ℝ) ^ (τ * ((j : ℝ) + 1)) := by
  exact mem_roughPrimeFinset_iff_of_cutoff_le_cap (Nat.le_ceil _)

theorem actualPrimeFineLabelFinset_disjoint {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (actualPrimeFineLabelFinset N τ i) (actualPrimeFineLabelFinset N τ j) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsep {i j : ℕ} (h : i < j) :
      (N : ℝ) ^ (τ * ((i : ℝ) + 1)) ≤ (N : ℝ) ^ (τ * j) := by
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt h
    exact Real.rpow_le_rpow_of_exponent_le hNreal (mul_le_mul_of_nonneg_left hcast hτ)
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hp' := mem_actualPrimeFineLabelFinset.mp hp
  have hq' := mem_actualPrimeFineLabelFinset.mp hq
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact (not_lt_of_ge ((hsep hij).trans hq'.2.2.1)) hp'.2.2.2
  · exact (not_lt_of_ge ((hsep hji).trans hp'.2.2.1)) hq'.2.2.2

/-- The actual fine-interval geometry supplies disjointness. There is no
caller premise asserting fibre uniqueness or an assigned coefficient. -/
theorem actualPrimeFineLabelBlocks_moebius_sum {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ)) (r : ℕ) (H : ℕ → ℝ)
    (hlabels : blocks.Pairwise (fun b c => b.1 ≠ c.1)) :
    (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks),
        (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      ∑ n ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks)).image List.prod,
        (ArithmeticFunction.moebius (r * n) : ℝ) * H n := by
  apply actualPrimeLabelBlocks_moebius_sum_disjoint
  · intro b _hb p hp
    exact (mem_actualPrimeFineLabelFinset.mp hp).1
  · exact hlabels.imp (fun h => actualPrimeFineLabelFinset_disjoint hN hτ h)

theorem actualPrimeFineLabelBlocks_moebius_fibre {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ)) (r n : ℕ)
    (hlabels : blocks.Pairwise (fun b c => b.1 ≠ c.1)) :
    ((ArithmeticFunction.moebius (r * n) : ℝ) * actualPrimeTupleCoefficient
        (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (actualPrimeLabelBlocksWord blocks)) n) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ) =
      if n ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks)).image List.prod
        then (ArithmeticFunction.moebius (r * n) : ℝ) else 0 := by
  apply actualPrimeLabelBlocks_moebius_fibre_disjoint
  · intro b _hb p hp
    exact (mem_actualPrimeFineLabelFinset.mp hp).1
  · exact hlabels.imp (fun h => actualPrimeFineLabelFinset_disjoint hN hτ h)

/-- The original fixed signed scalar is restored once, along with the
literal product of repeated-label factorials. No later group factorial is
inserted into this fine-label identity. -/
theorem actualPrimeFineLabelBlocks_original_scalar {N : ℕ} (hN : 1 ≤ N)
    {τ : ℝ} (hτ : 0 ≤ τ) (blocks : List (ℕ × ℕ)) (r : ℕ)
    (c : ℝ) (H : ℕ → ℝ) (hlabels : blocks.Pairwise (fun b c => b.1 ≠ c.1)) :
    (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
        (∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
          (actualPrimeLabelBlocksWord blocks),
          (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) =
      c * ∑ n ∈ (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks)).image List.prod,
        (ArithmeticFunction.moebius (r * n) : ℝ) * H n := by
  calc
    _ = c * ((∑ ps ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ)
        (actualPrimeLabelBlocksWord blocks),
        (ArithmeticFunction.moebius (r * ps.prod) : ℝ) * H ps.prod) /
        (actualPrimeLabelBlocksFactorial blocks : ℝ)) := by ring
    _ = _ := by rw [actualPrimeFineLabelBlocks_moebius_sum hN hτ blocks r H hlabels]

end

end ImbalancedChen
