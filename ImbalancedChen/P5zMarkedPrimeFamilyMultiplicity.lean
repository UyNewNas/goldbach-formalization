import ImbalancedChen.P5zPositiveFamilyBudget
import ImbalancedChen.PowerErrorBudget
import Mathlib.Data.Fintype.BigOperators

/-! SOURCE ONLY / UNCOMPILED. Literal marked prime-tuples retain every slot
label and product multiplicity. No source-mass or U* estimate is asserted.
The rank is fixed; the source may be an arbitrary marked subfamily. -/
namespace ImbalancedChen
noncomputable section
open scoped BigOperators
open Filter
open Classical

private theorem p5z_prime_dvd_tuple_exists {rank P : ℕ}
    (u : Fin rank → Fin (P + 1)) (hu : ∀ i, Nat.Prime (u i).val)
    {p : ℕ} (hp : Nat.Prime p) (hd : p ∣ Part3.labelledProduct u) :
    ∃ i : Fin rank, p = (u i).val := by
  have haux (s : Finset (Fin rank)) :
      p ∣ ∏ i ∈ s, (u i).val → ∃ i ∈ s, p = (u i).val := by
    induction s using Finset.induction_on with
    | empty =>
        intro h
        simp only [Finset.prod_empty] at h
        exact (hp.ne_one (Nat.dvd_one.mp h)).elim
    | @insert i s hi ih =>
        intro h
        rw [Finset.prod_insert hi] at h
        rcases hp.dvd_mul.mp h with hpi | hrest
        · exact ⟨i, Finset.mem_insert_self _ _, (Nat.prime_dvd_prime_iff_eq hp (hu i)).mp hpi⟩
        · obtain ⟨j, hj, heq⟩ := ih hrest
          exact ⟨j, Finset.mem_insert_of_mem hj, heq⟩
  obtain ⟨i, _, heq⟩ := haux Finset.univ hd
  exact ⟨i, heq⟩

/-- No injection of the product map is asserted. A fibre has at most
rank^rank tuples, since every prime slot equals one of a witness's rank
prime values. The proof also works when primes repeat. -/
theorem p5z_marked_prime_product_fibre_card_le {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (m : ℕ) : (S.filter (fun t => Part3.labelledProduct t = m)).card ≤ rank ^ rank := by
  let F := S.filter (fun t => Part3.labelledProduct t = m)
  change F.card ≤ rank ^ rank
  by_cases hF : F = ∅
  · simp only [hF, Finset.card_empty]
    exact Nat.zero_le _
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr hF
  have huS := (Finset.mem_filter.mp hu).1
  have hup : ∀ i, Nat.Prime (u i).val := (Finset.mem_filter.mp (hS huS)).2
  let T := Finset.univ.image (fun i : Fin rank => (u i).val)
  have hT : T.card ≤ rank := (Finset.card_image_le).trans (by simp)
  have hchoice (v : F) (i : Fin rank) : (v.val i).val ∈ T := by
    have hvS := (Finset.mem_filter.mp v.property).1
    have hvp : Nat.Prime (v.val i).val := (Finset.mem_filter.mp (hS hvS)).2 i
    have hprod : Part3.labelledProduct v.val = Part3.labelledProduct u :=
      (Finset.mem_filter.mp v.property).2.trans (Finset.mem_filter.mp hu).2.symm
    have hd : (v.val i).val ∣ Part3.labelledProduct u := by
      rw [← hprod]
      exact Finset.dvd_prod_of_mem (fun j => (v.val j).val) (Finset.mem_univ i)
    obtain ⟨j, heq⟩ := p5z_prime_dvd_tuple_exists u hup hvp hd
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, heq.symm⟩
  let encode : F → (Fin rank → T) := fun v i => ⟨(v.val i).val, hchoice v i⟩
  have hinj : Function.Injective encode := by
    intro v w hvw
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrArg (fun g : Fin rank → T => (g i).val) hvw
  have hcard := Fintype.card_le_of_injective encode hinj
  have hbound : F.card ≤ T.card ^ rank := by
    simpa only [Fintype.card_pi_const, Fintype.card_coe] using hcard
  exact hbound.trans (pow_le_pow_left₀ (Nat.zero_le _) hT rank)

/-- The true weighted pushforward, rather than an unweighted image. -/
def p5z_markedProductWeight {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (W : (Fin rank → Fin (N + 1)) → ℝ) (m : ℕ) : ℝ :=
  ∑ t ∈ S.filter (fun t => Part3.labelledProduct t = m), W t

theorem p5z_markedProductWeight_nonneg {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (W : (Fin rank → Fin (N + 1)) → ℝ)
    (hW : ∀ t ∈ S, 0 ≤ W t) (m : ℕ) : 0 ≤ p5z_markedProductWeight S W m :=
  Finset.sum_nonneg (fun t ht => hW t (Finset.mem_filter.mp ht).1)

theorem p5z_markedProductWeight_le {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ t ∈ S, W t ≤ B) (m : ℕ) :
    p5z_markedProductWeight S W m ≤ B * (rank ^ rank : ℕ) := by
  have hc : ((S.filter (fun t => Part3.labelledProduct t = m)).card : ℝ) ≤
      (rank ^ rank : ℕ) := by exact_mod_cast p5z_marked_prime_product_fibre_card_le S hS m
  calc
    _ ≤ ∑ _t ∈ S.filter (fun t => Part3.labelledProduct t = m), B :=
      Finset.sum_le_sum (fun t ht => hW t (Finset.mem_filter.mp ht).1)
    _ = B * ((S.filter (fun t => Part3.labelledProduct t = m)).card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hB

/-- Exact weighted finite Fubini, valid for signed test G before any norm. -/
theorem p5z_markedProductWeight_sum {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (W : (Fin rank → Fin (N + 1)) → ℝ)
    (hcap : ∀ t ∈ S, Part3.labelledProduct t ≤ N) (G : ℕ → ℝ) :
    (∑ m ∈ Finset.range (N + 1), p5z_markedProductWeight S W m * G m) =
      ∑ t ∈ S, W t * G (Part3.labelledProduct t) := by
  have hf := Finset.sum_fiberwise_of_maps_to (s := S) (t := Finset.range (N + 1))
    (g := Part3.labelledProduct) (fun t ht => Finset.mem_range.mpr (Nat.lt_succ_of_le (hcap t ht)))
    (fun t => W t * G (Part3.labelledProduct t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  unfold p5z_markedProductWeight
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [(Finset.mem_filter.mp ht).2]

/-- Weighted finite small-prime payment for every marked prime family.
The constant is B*rank^rank and ALL original tuple labels are retained. -/
theorem p5z_markedSmallPrimeMass_le {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hW : ∀ t ∈ S, W t ≤ B) (hcap : ∀ t ∈ S, Part3.labelledProduct t ≤ N) (z : ℕ) :
    p5z_labelledSmallPrimeMass S Part3.labelledProduct W N z ≤ B * (rank ^ rank : ℕ) * (z : ℝ) := by
  let V := p5z_markedProductWeight S W
  let F := (Finset.range (N + 1)).filter
    (fun m => m < N ∧ Nat.Prime (N - m) ∧ N - m < z)
  have hF : F.card ≤ z := by
    calc
      F.card ≤ (Finset.range z).card := by
        apply Finset.card_le_card_of_injOn (fun m : ℕ => N - m)
        · intro m hm
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2.2.2
        · intro m hm r hr heq
          have hmN := (Finset.mem_filter.mp hm).2.1
          have hrN := (Finset.mem_filter.mp hr).2.1
          omega
      _ = z := Finset.card_range z
  have hFreal : (F.card : ℝ) ≤ (z : ℝ) := by exact_mod_cast hF
  have heq := p5z_markedProductWeight_sum S W hcap
    (fun m => if m < N ∧ Nat.Prime (N - m) ∧ N - m < z then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at heq
  change _ = p5z_labelledSmallPrimeMass S Part3.labelledProduct W N z at heq
  rw [← heq, ← Finset.sum_filter]
  change (∑ m ∈ F, V m) ≤ _
  calc
    _ ≤ ∑ _m ∈ F, B * (rank ^ rank : ℕ) :=
      Finset.sum_le_sum (fun m _ => p5z_markedProductWeight_le S hS W B hB hW m)
    _ = B * (rank ^ rank : ℕ) * (F.card : ℝ) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hFreal (mul_nonneg hB (Nat.cast_nonneg _))

/-- Concrete marked coefficient for the actual Part3 PP source. -/
def p5z_markedPhysicalWeight {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (W : (Fin rank → Fin (N + 1)) → ℝ)
    (t : Fin rank → Fin (N + 1)) : ℝ := if t ∈ S then W t else 0

theorem p5z_markedPhysicalWeight_test_sum {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (G : (Fin rank → Fin (N + 1)) → ℝ) :
    (∑ t ∈ Part3.labelledPrimeTuples rank N, p5z_markedPhysicalWeight S W t * G t) =
      ∑ t ∈ S, W t * G t := by
  unfold p5z_markedPhysicalWeight
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext t
  simp only [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨hS h, h⟩⟩

/-- The PP input is the actual modulus-independent marked coefficient. -/
theorem p5z_markedDistribution_eq_physicalPP {rank N : ℕ}
    (S : Finset (Fin rank → Fin (N + 1))) (hS : S ⊆ Part3.labelledPrimeTuples rank N)
    (W : (Fin rank → Fin (N + 1)) → ℝ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError S Part3.labelledProduct W N D rho =
      Part3.primeProductSignedError rank N N D rho (p5z_markedPhysicalWeight S W) := by
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass
    Part3.primeProductSignedError
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  rw [p5z_markedPhysicalWeight_test_sum S hS W]
  simp_rw [mul_sub, ← mul_div_assoc, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_div]

end
end ImbalancedChen
