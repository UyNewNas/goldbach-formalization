import ImbalancedChen.P5zUpsilon9SwitchedMultiplicity
import ImbalancedChen.CurrentChenUpsilon9TrueLiMass

/-!
# Exact ordered branches of the actual marked ninth PP source

SOURCE ONLY / UNCOMPILED. The first import is the sibling candidate
P5zUpsilon9SwitchedMultiplicity.lean.txt, not an installed accepted module.

The finite source retains the actual selector, original sqrt(N/(p₁*p₂)),
receiver centre-coprimality, and every original label.  Its three branches
own q<p₁, p₁<=q<p₂, and p₂<=q, respectively. Repeated terminal primes are
kept. Sorting a branch only represents the same physical prime product;
no product image is substituted for the original labelled sum.
-/

namespace ImbalancedChen

noncomputable section

open scoped BigOperators
open Classical

/-- Three literal order gates on the actual original labelled source. -/
def p5z_u9_orderGate (j : Fin 3) (t : P5zU9Triple) : Prop :=
  ![t.2 < t.1.1, t.1.1 ≤ t.2 ∧ t.2 < t.1.2, t.1.2 ≤ t.2] j

def p5z_u9_orderBranch (j : Fin 3) (N : ℕ) : Finset P5zU9Triple :=
  (p5z_u9_switchedLabels N).filter (p5z_u9_orderGate j)

/-- The source data have no additive-prime condition on the receiver. -/
theorem p5z_u9_order_source_data {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) :
    t.1 ∈ chenY9PrimeSelector N ((N : ℝ) ^ (19 / 125 : ℝ))
      ((N : ℝ) ^ (59 / 250 : ℝ)) ∧
      t.2 < N + 1 ∧ Nat.Prime t.2 ∧ p5z_u9_product t < N ∧
      Real.sqrt ((N : ℝ) / ((t.1.1 : ℝ) * (t.1.2 : ℝ))) ≤ (t.2 : ℝ) ∧
      Nat.Coprime (N - p5z_u9_product t) N := by
  rcases t with ⟨⟨p₁, p₂⟩, q⟩
  exact mem_p5z_u9_switchedLabels_iff.mp ht

/-- Centre-coprimality transfers to the physical prime product itself. -/
theorem p5z_u9_order_product_coprime {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) : Nat.Coprime (p5z_u9_product t) N := by
  have hd := p5z_u9_order_source_data ht
  exact (Nat.coprime_self_sub_left hd.2.2.2.1.le).mp hd.2.2.2.2.2

theorem p5z_u9_order_pair_product_mem {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) :
    t.1.1 * t.1.2 ∈ currentChenUpsilon9PrefixProducts N := by
  exact Finset.mem_image.mpr ⟨t.1, (p5z_u9_order_source_data ht).1, rfl⟩

/-- Every original label lies in exactly one order branch, including the
equality owners q=p₁ in branch 1 and q=p₂ in branch 2. -/
theorem p5z_u9_orderBranches_union (N : ℕ) :
    (p5z_u9_orderBranch 0 N ∪ p5z_u9_orderBranch 1 N) ∪ p5z_u9_orderBranch 2 N =
      p5z_u9_switchedLabels N := by
  ext t
  constructor
  · intro ht
    rcases Finset.mem_union.mp ht with ht | ht
    · rcases Finset.mem_union.mp ht with ht | ht <;>
        exact (Finset.mem_filter.mp ht).1
    · exact (Finset.mem_filter.mp ht).1
  · intro ht
    by_cases hq₁ : t.2 < t.1.1
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨ht, by simpa [p5z_u9_orderGate] using hq₁⟩))))
    · by_cases hq₂ : t.2 < t.1.2
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr
            ⟨ht, by simpa [p5z_u9_orderGate] using And.intro (Nat.le_of_not_gt hq₁) hq₂⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨ht, by simpa [p5z_u9_orderGate] using Nat.le_of_not_gt hq₂⟩))

theorem p5z_u9_orderBranches_disjoint (N : ℕ) {j k : Fin 3} (hjk : j ≠ k) :
    Disjoint (p5z_u9_orderBranch j N) (p5z_u9_orderBranch k N) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  obtain ⟨htsource, hjt⟩ := Finset.mem_filter.mp ht
  have hkt := (Finset.mem_filter.mp hu).2
  have hp := (chenY9PrimeSelector_ordered_prime_data
    (p5z_u9_order_source_data htsource).1).2.2
  fin_cases j <;> fin_cases k <;> simp [p5z_u9_orderGate] at hjt hkt hjk <;> omega

/-- Exact splitting for every real test, before any signed PP modulus
sum or absolute value is taken. -/
theorem p5z_u9_orderBranches_sum (N : ℕ) (G : P5zU9Triple → ℝ) :
    (∑ t ∈ p5z_u9_switchedLabels N, G t) =
      (∑ t ∈ p5z_u9_orderBranch 0 N, G t) +
      (∑ t ∈ p5z_u9_orderBranch 1 N, G t) +
      (∑ t ∈ p5z_u9_orderBranch 2 N, G t) := by
  rw [← p5z_u9_orderBranches_union N,
    Finset.sum_union (Finset.disjoint_union_left.mpr
      ⟨p5z_u9_orderBranches_disjoint N (by decide : (0 : Fin 3) ≠ 2),
        p5z_u9_orderBranches_disjoint N (by decide : (1 : Fin 3) ≠ 2)⟩),
    Finset.sum_union (p5z_u9_orderBranches_disjoint N (by decide : (0 : Fin 3) ≠ 1))]

theorem p5z_u9_orderBranches_congruenceMass (N ell : ℕ) :
    p5z_labelledCongruenceMass (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) N ell =
      p5z_labelledCongruenceMass (p5z_u9_orderBranch 0 N) p5z_u9_product (fun _ => 1) N ell +
      p5z_labelledCongruenceMass (p5z_u9_orderBranch 1 N) p5z_u9_product (fun _ => 1) N ell +
      p5z_labelledCongruenceMass (p5z_u9_orderBranch 2 N) p5z_u9_product (fun _ => 1) N ell := by
  exact p5z_u9_orderBranches_sum N
    (fun t => if Nat.ModEq ell (p5z_u9_product t) N then 1 else 0)

theorem p5z_u9_orderBranches_coprimeMass (N ell : ℕ) :
    p5z_labelledCoprimeMass (p5z_u9_switchedLabels N) p5z_u9_product (fun _ => 1) ell =
      p5z_labelledCoprimeMass (p5z_u9_orderBranch 0 N) p5z_u9_product (fun _ => 1) ell +
      p5z_labelledCoprimeMass (p5z_u9_orderBranch 1 N) p5z_u9_product (fun _ => 1) ell +
      p5z_labelledCoprimeMass (p5z_u9_orderBranch 2 N) p5z_u9_product (fun _ => 1) ell := by
  exact p5z_u9_orderBranches_sum N
    (fun t => if Nat.Coprime (p5z_u9_product t) ell then 1 else 0)

/-- Exact same-rho physical PP splitting. No norm, sign assumption or
branch-dependent modulus weight is inserted in the original signed sum. -/
theorem p5z_u9_orderBranches_distribution (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5z_u9_switchedLabels N) p5z_u9_product
        (fun _ => 1) N Q rho =
      p5z_labelledDistributionError (p5z_u9_orderBranch 0 N) p5z_u9_product (fun _ => 1) N Q rho +
      p5z_labelledDistributionError (p5z_u9_orderBranch 1 N) p5z_u9_product (fun _ => 1) N Q rho +
      p5z_labelledDistributionError (p5z_u9_orderBranch 2 N) p5z_u9_product (fun _ => 1) N Q rho := by
  unfold p5z_labelledDistributionError
  simp_rw [p5z_u9_orderBranches_congruenceMass, p5z_u9_orderBranches_coprimeMass]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _hell
  ring

/-- Restoring the receiver primality filter in each branch recovers
precisely the installed actual prime triples. -/
def p5z_u9_primeOrderBranch (j : Fin 3) (N : ℕ) : Finset P5zU9Triple :=
  (p5z_u9_orderBranch j N).filter
    (fun t => p5z_u9_product t < N ∧ Nat.Prime (N - p5z_u9_product t))

theorem p5z_u9_primeOrderBranches_disjoint (N : ℕ) {j k : Fin 3} (hjk : j ≠ k) :
    Disjoint (p5z_u9_primeOrderBranch j N) (p5z_u9_primeOrderBranch k N) := by
  apply Finset.disjoint_left.mpr
  intro t ht hu
  exact Finset.disjoint_left.mp (p5z_u9_orderBranches_disjoint N hjk)
    (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp hu).1

theorem p5z_u9_primeOrderBranches_union (N : ℕ) :
    (p5z_u9_primeOrderBranch 0 N ∪ p5z_u9_primeOrderBranch 1 N) ∪
        p5z_u9_primeOrderBranch 2 N = currentChenUpsilon9PrimeTriples N := by
  rw [← p5z_u9_switchedLabels_filter_eq_primeTriples N,
    ← p5z_u9_orderBranches_union N]
  simp only [Finset.filter_union, p5z_u9_primeOrderBranch]

theorem p5z_u9_primeOrderBranches_sum (N : ℕ) (G : P5zU9Triple → ℝ) :
    (∑ t ∈ currentChenUpsilon9PrimeTriples N, G t) =
      (∑ t ∈ p5z_u9_primeOrderBranch 0 N, G t) +
      (∑ t ∈ p5z_u9_primeOrderBranch 1 N, G t) +
      (∑ t ∈ p5z_u9_primeOrderBranch 2 N, G t) := by
  have h := p5z_u9_orderBranches_sum N (fun t =>
    if p5z_u9_product t < N ∧ Nat.Prime (N - p5z_u9_product t) then G t else 0)
  simpa only [← Finset.sum_filter, p5z_u9_switchedLabels_filter_eq_primeTriples,
    p5z_u9_primeOrderBranch] using h

/-- Exact original U9 count, with all three ordered prime branches and
the original actual unit fibres still present. -/
theorem p5z_u9_eq_ordered_primeBranches_add_units (N : ℕ) :
    currentChenUpsilon9 N =
      ((p5z_u9_primeOrderBranch 0 N).card : ℝ) +
      ((p5z_u9_primeOrderBranch 1 N).card : ℝ) +
      ((p5z_u9_primeOrderBranch 2 N).card : ℝ) +
      ((currentChenUpsilon9UnitFibres N).card : ℝ) := by
  have h := p5z_u9_primeOrderBranches_sum N (fun _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  rw [currentChenUpsilon9_eq_primeTriples_add_unitFibres, h]

/-- The physical prime tuple in each branch, still with all three slots
and repeated primes. This map alone does not discard any original label. -/
def p5z_u9_orderedNat (j : Fin 3) (t : P5zU9Triple) : Fin 3 → ℕ :=
  ![![t.2, t.1.1, t.1.2], ![t.1.1, t.2, t.1.2], ![t.1.1, t.1.2, t.2]] j

theorem p5z_u9_orderedNat_product (j : Fin 3) (t : P5zU9Triple) :
    (∏ i : Fin 3, p5z_u9_orderedNat j t i) = p5z_u9_product t := by
  fin_cases j <;>
    simp [p5z_u9_orderedNat, Fin.prod_univ_three, p5z_u9_product,
      mul_comm, mul_left_comm, mul_assoc]

/-- Sorting within a fixed branch is only a permutation of the original
three labels. The branch label must still be retained across branches. -/
theorem p5z_u9_orderedNat_injective (j : Fin 3) :
    Function.Injective (p5z_u9_orderedNat j) := by
  intro t u heq
  have h0 := congrFun heq (0 : Fin 3)
  have h1 := congrFun heq (1 : Fin 3)
  have h2 := congrFun heq (2 : Fin 3)
  have hp₁ : t.1.1 = u.1.1 := by
    fin_cases j <;> simp [p5z_u9_orderedNat] at h0 h1 h2 <;> omega
  have hp₂ : t.1.2 = u.1.2 := by
    fin_cases j <;> simp [p5z_u9_orderedNat] at h0 h1 h2 <;> omega
  have hq : t.2 = u.2 := by
    fin_cases j <;> simp [p5z_u9_orderedNat] at h0 h1 h2 <;> omega
  apply Sigma.ext (Prod.ext hp₁ hp₂)
  exact heq_of_eq hq

/-- Every sorted coordinate is an actual centre-coprime prime at the
same physical cap N, even when two coordinates are equal. -/
theorem p5z_u9_orderedNat_prime_coprime_cap (j : Fin 3) {N : ℕ} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_switchedLabels N) :
    ∀ i : Fin 3, Nat.Prime (p5z_u9_orderedNat j t i) ∧
      Nat.Coprime (p5z_u9_orderedNat j t i) N ∧ p5z_u9_orderedNat j t i ≤ N := by
  have hd := p5z_u9_order_source_data ht
  obtain ⟨hc₁, hc₂⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hd.1).1
  have hp₁ := mem_chenAdditivePrimeCarrier.mp hc₁
  have hp₂ := mem_chenAdditivePrimeCarrier.mp hc₂
  have hqcop : Nat.Coprime t.2 N :=
    (Nat.coprime_mul_iff_left.mp (p5z_u9_order_product_coprime ht)).2
  have hqcap : t.2 ≤ N := Nat.le_of_lt_succ hd.2.1
  intro i
  fin_cases j <;> fin_cases i <;> simp only [p5z_u9_orderedNat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals first
    | exact ⟨hp₁.2.1, hp₁.2.2, hp₁.1.le⟩
    | exact ⟨hp₂.2.1, hp₂.2.2, hp₂.1.le⟩
    | exact ⟨hd.2.2.1, hqcop, hqcap⟩

theorem p5z_u9_orderedNat_sorted {N : ℕ} {j : Fin 3} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_orderBranch j N) :
    p5z_u9_orderedNat j t 0 ≤ p5z_u9_orderedNat j t 1 ∧
      p5z_u9_orderedNat j t 1 ≤ p5z_u9_orderedNat j t 2 := by
  obtain ⟨htsource, hgate⟩ := Finset.mem_filter.mp ht
  have hp := (chenY9PrimeSelector_ordered_prime_data
    (p5z_u9_order_source_data htsource).1).2.2
  fin_cases j <;> simp [p5z_u9_orderGate, p5z_u9_orderedNat] at hgate ⊢ <;> omega

/-- A branch has a literal representation in Part3's physical labelled
three-prime carrier. Only source support and ordering are licensed here;
no missing distribution estimate is inferred from carrier membership. -/
theorem p5z_u9_orderBranch_physical_representation {N : ℕ} {j : Fin 3} {t : P5zU9Triple}
    (ht : t ∈ p5z_u9_orderBranch j N) :
    ∃ u ∈ Part3.labelledPrimeTuples 3 N,
      (∀ i, (u i).val = p5z_u9_orderedNat j t i) ∧
      (u 0).val ≤ (u 1).val ∧ (u 1).val ≤ (u 2).val ∧
      Part3.labelledProduct u = p5z_u9_product t ∧
      Nat.Coprime (Part3.labelledProduct u) N ∧ Part3.labelledProduct u < N ∧
      Nat.Coprime (N - Part3.labelledProduct u) N := by
  have hs := (Finset.mem_filter.mp ht).1
  have hc := p5z_u9_orderedNat_prime_coprime_cap j hs
  let u : Fin 3 → Fin (N + 1) := fun i =>
    ⟨p5z_u9_orderedNat j t i, Nat.lt_succ_of_le (hc i).2.2⟩
  have hu : u ∈ Part3.labelledPrimeTuples 3 N := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, fun i => (hc i).1⟩
  have hp : Part3.labelledProduct u = p5z_u9_product t :=
    p5z_u9_orderedNat_product j t
  have hsorted := p5z_u9_orderedNat_sorted ht
  refine ⟨u, hu, (fun _ => rfl), hsorted.1, hsorted.2, hp, ?_, ?_, ?_⟩
  · rw [hp]
    exact p5z_u9_order_product_coprime hs
  · rw [hp]
    exact p5z_u9_switchedLabels_product_lt hs
  · rw [hp]
    exact (p5z_u9_order_source_data hs).2.2.2.2.2

/-- Original outer product and coordinate powers remain attached to the
marked labels. In particular the terminal prime is not an unconstrained
free prime introduced by sorting. -/
theorem p5z_u9_order_source_power_support {N : ℕ} {t : P5zU9Triple}
    (hN : (1 : ℝ) ≤ N) (ht : t ∈ p5z_u9_switchedLabels N) :
    (N : ℝ) ^ (19 / 125 : ℝ) ≤ (t.1.1 : ℝ) ∧
      (t.1.1 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ) ∧
      (N : ℝ) ^ (59 / 250 : ℝ) ≤ (t.1.2 : ℝ) ∧
      (t.1.2 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) ∧
      (N : ℝ) ^ (191 / 1000 : ℝ) ≤ (t.2 : ℝ) ∧
      (t.2 : ℝ) < (N : ℝ) ^ (153 / 250 : ℝ) ∧
      (N : ℝ) ^ (97 / 250 : ℝ) ≤ ((t.1.1 * t.1.2 : ℕ) : ℝ) ∧
      ((t.1.1 * t.1.2 : ℕ) : ℝ) < (N : ℝ) ^ (309 / 500 : ℝ) := by
  have hd := p5z_u9_order_source_data ht
  have hpdata := chenY9PrimeSelector_ordered_prime_data hd.1
  obtain ⟨_hc, hfirstlo, hfirsthi, hsecondlo, hsecondhi⟩ := Finset.mem_filter.mp hd.1
  have hNp : (0 : ℝ) < N := zero_lt_one.trans_le hN
  have hap : (0 : ℝ) < ((t.1.1 * t.1.2 : ℕ) : ℝ) := by
    exact_mod_cast mul_pos hpdata.1.pos hpdata.2.1.pos
  have hfirstone : (1 : ℝ) ≤ (t.1.1 : ℝ) := by exact_mod_cast hpdata.1.one_le
  have hsecondcap : (t.1.2 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := by
    apply hsecondhi.trans_le
    simpa only [Real.sqrt_eq_rpow] using
      Real.sqrt_le_sqrt (div_le_self hNp.le hfirstone)
  have ha := p5z_u9_order_pair_product_mem ht
  have hb := currentChenUpsilon9PrefixProducts_power_bounds hN ha
  have hquotlo := currentChenUpsilon9_li_argument_power_lower hN ha
  have hrootlo : (N : ℝ) ^ (191 / 1000 : ℝ) ≤
      Real.sqrt ((N : ℝ) / ((t.1.1 * t.1.2 : ℕ) : ℝ)) := by
    apply (sq_le_sq₀ (Real.rpow_nonneg hNp.le _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (div_nonneg hNp.le hap.le),
      ← Real.rpow_mul_natCast hNp.le (191 / 1000 : ℝ) 2,
      show (191 / 1000 : ℝ) * ((2 : ℕ) : ℝ) = 191 / 500 by norm_num]
    exact hquotlo
  have hcut : Real.sqrt ((N : ℝ) / ((t.1.1 * t.1.2 : ℕ) : ℝ)) ≤ (t.2 : ℝ) := by
    simpa only [Nat.cast_mul] using hd.2.2.2.2.1
  have hquothi : (N : ℝ) / ((t.1.1 * t.1.2 : ℕ) : ℝ) ≤
      (N : ℝ) ^ (153 / 250 : ℝ) := by
    apply (div_le_iff₀ hap).mpr
    calc
      (N : ℝ) = (N : ℝ) ^ (153 / 250 : ℝ) * (N : ℝ) ^ (97 / 250 : ℝ) := by
        rw [← Real.rpow_add hNp,
          show (153 / 250 : ℝ) + 97 / 250 = 1 by norm_num, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb.1 (Real.rpow_nonneg hNp.le _)
  have hqquot : (t.2 : ℝ) < (N : ℝ) / ((t.1.1 * t.1.2 : ℕ) : ℝ) := by
    apply (lt_div_iff₀ hap).mpr
    have hmul : (((t.1.1 * t.1.2 : ℕ) : ℝ) * (t.2 : ℝ)) < (N : ℝ) := by
      exact_mod_cast hd.2.2.2.1
    simpa only [mul_comm] using hmul
  exact ⟨hfirstlo, hfirsthi, hsecondlo, hsecondcap,
    hrootlo.trans hcut, hqquot.trans_le hquothi, hb.1, hb.2⟩

/-- Every prime coordinate of a sorted representation lies above the
same original fixed positive power gate, uniformly in the three branches. -/
theorem p5z_u9_orderedNat_lower_power (j : Fin 3) {N : ℕ} {t : P5zU9Triple}
    (hN : (1 : ℝ) ≤ N) (ht : t ∈ p5z_u9_switchedLabels N) :
    ∀ i : Fin 3, (N : ℝ) ^ (19 / 125 : ℝ) ≤ (p5z_u9_orderedNat j t i : ℝ) := by
  have hp := p5z_u9_order_source_power_support hN ht
  have hp₂ : (N : ℝ) ^ (19 / 125 : ℝ) ≤ (t.1.2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (19 / 125 : ℝ) ≤ 59 / 250)).trans
      hp.2.2.1
  have hq : (N : ℝ) ^ (19 / 125 : ℝ) ≤ (t.2 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (19 / 125 : ℝ) ≤ 191 / 1000)).trans
      hp.2.2.2.2.1
  intro i
  fin_cases j <;> fin_cases i <;> simp only [p5z_u9_orderedNat,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  all_goals first | exact hp.1 | exact hp₂ | exact hq

end

end ImbalancedChen
