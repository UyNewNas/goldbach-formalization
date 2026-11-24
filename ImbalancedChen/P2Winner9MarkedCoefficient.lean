import ImbalancedChen.P2Winner9HomogeneousRecurrence
import ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.RingTheory.PowerSeries.Basic

/-!
Formal power series express the signed generating-function coefficients.
A quadratic polynomial records the first three coefficients of the
marked vertex product. These identities apply in every degree.
-/

namespace ImbalancedChen.P2Winner9MarkedCoefficient

noncomputable section

open scoped BigOperators Polynomial
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9HomogeneousRecurrence
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

private theorem coeff_mul_range {R : Type*} [Semiring R]
    (k : ℕ) (p q : PowerSeries R) :
    PowerSeries.coeff k (p * q) =
      ∑ i ∈ Finset.range (k + 1), PowerSeries.coeff i p * PowerSeries.coeff (k - i) q := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- The formal geometric series with ratio `a X`. -/
def geometric {R : Type*} [Semiring R] (a : R) : PowerSeries R :=
  PowerSeries.mk (fun k => a ^ k)

@[simp] theorem coeff_geometric {R : Type*} [Semiring R] (a : R) (k : ℕ) :
    PowerSeries.coeff k (geometric a) = a ^ k := by
  simp [geometric]

/-- All coefficients of a positive power of the geometric series. -/
theorem coeff_geometric_pow {R : Type*} [Semiring R] (a : R) (m k : ℕ) :
    PowerSeries.coeff k (geometric a ^ (m + 1)) = ((k + m).choose m : R) * a ^ k := by
  induction m generalizing k with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, coeff_mul_range]
    calc
      _ = ∑ i ∈ Finset.range (k + 1), ((i + m).choose m : R) * a ^ k := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [ih, coeff_geometric, mul_assoc, ← pow_add,
          Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
      _ = _ := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_add_choose]
        rfl

/-- The product of the unmarked geometric series has exactly the verified
bounded complete-homogeneous coefficients. -/
theorem coeff_product_geometric {R : Type*} [CommSemiring R] {n bound k : ℕ}
    (y : Fin n → ℕ) (hk : k ≤ bound) :
    PowerSeries.coeff k (∏ i : Fin n, geometric (y i : R)) =
      (boundedHomogeneous y bound k : R) := by
  induction n generalizing k with
  | zero =>
    classical
    have h : boundedHomogeneous y bound k = if k = 0 then 1 else 0 := by
      unfold boundedHomogeneous
      rw [Finset.sum_eq_single (Fin.elim0 : Fin 0 → Fin (bound + 1))]
      · simp [eq_comm]
      · intro a _ ha
        exact (ha (funext fun i => i.elim0)).elim
      · intro h
        exact (h (Finset.mem_univ _)).elim
    simp [h]
  | succ n ih =>
    rw [Fin.prod_univ_succ, coeff_mul_range, split_coefficient y hk, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [coeff_geometric, ih (fun j => y j.succ) (Nat.le_trans (Nat.sub_le k i) hk)]
    simp

private def quadratic {R : Type*} [Semiring R] (a b c : R) : R[X] :=
  Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2

@[simp] private theorem coeff_quadratic_zero {R : Type*} [Semiring R] (a b c : R) :
    (quadratic a b c).coeff 0 = a := by
  simp [quadratic]

@[simp] private theorem coeff_quadratic_one {R : Type*} [Semiring R] (a b c : R) :
    (quadratic a b c).coeff 1 = b := by
  simp [quadratic]

@[simp] private theorem coeff_quadratic_two {R : Type*} [Semiring R] (a b c : R) :
    (quadratic a b c).coeff 2 = c := by
  simp [quadratic]

private theorem mul_coeff_two {R : Type*} [Semiring R] (p q : R[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

private theorem low_coeff_product {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (b : ι → R) :
    let p := ∏ i ∈ s, quadratic 1 (b i) (b i ^ 2)
    p.coeff 0 = 1 ∧ p.coeff 1 = (∑ i ∈ s, b i) ∧
      2 * p.coeff 2 = (∑ i ∈ s, b i)^2 + ∑ i ∈ s, b i ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | insert i s hi ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    simp only [Finset.prod_insert hi, Finset.sum_insert hi, Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one, mul_coeff_two, coeff_quadratic_zero, coeff_quadratic_one,
      coeff_quadratic_two, h0, h1, one_mul, mul_one]
    refine ⟨trivial, ?_, ?_⟩
    · exact add_comm _ _
    · calc
        _ = 2 * (∏ j ∈ s, quadratic 1 (b j) (b j ^ 2)).coeff 2 +
            2 * (b i * ∑ j ∈ s, b j) + 2 * b i ^ 2 := by ring
        _ = _ := by rw [h2]; ring

def markProduct {R ι : Type*} [CommSemiring R] (s : Finset ι) (b : ι → R) : R[X] :=
  ∏ i ∈ s, quadratic 1 (b i) (b i ^ 2)

def markWeight {R ι : Type*} [CommSemiring R] (s : Finset ι) (a b : ι → R) : R[X] :=
  ∑ i ∈ s, quadratic (a i) (a i * b i) (a i * b i ^ 2)

/-- The marked quadratic term of the product and its weighted factor.
The factor 2 is kept in the coefficient ring. -/
theorem double_coeff_weighted_mark {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a b : ι → R) :
    2 * (markProduct s b * markWeight s a b).coeff 2 =
      2 * (∑ i ∈ s, a i * b i ^ 2) +
      2 * ((∑ i ∈ s, b i) * ∑ i ∈ s, a i * b i) +
      ((∑ i ∈ s, b i)^2 + ∑ i ∈ s, b i ^ 2) * ∑ i ∈ s, a i := by
  obtain ⟨h0, h1, h2⟩ := low_coeff_product s b
  unfold markProduct markWeight
  rw [mul_coeff_two, h0, h1, one_mul]
  simp only [Polynomial.finsetSum_coeff, coeff_quadratic_zero, coeff_quadratic_one,
    coeff_quadratic_two]
  simp only [mul_add, ← mul_assoc, h2]

private theorem coeff_leftScaled {R : Type*} [CommSemiring R]
    (a b c : R) (m k : ℕ) :
    PowerSeries.coeff k
      ((PowerSeries.C a * geometric c) * (PowerSeries.C b * geometric c)^m) =
      (a * b^m) * (((k + m).choose m : R) * c^k) := by
  rw [mul_pow, ← (PowerSeries.C (R := R)).map_pow, mul_mul_mul_comm,
    ← (PowerSeries.C (R := R)).map_mul, ← pow_succ', PowerSeries.coeff_C_mul,
    coeff_geometric_pow]

private theorem coeff_mul_conv (p q : PowerSeries ℤ) (k : ℕ) :
    PowerSeries.coeff k (p * q) =
      conv (fun i => PowerSeries.coeff i p) (fun i => PowerSeries.coeff i q) k := by
  rw [coeff_mul_range, conv]

private theorem coeff_two_mul (p : PowerSeries ℤ) (k : ℕ) :
    PowerSeries.coeff k (2 * p) = 2 * PowerSeries.coeff k p := by
  rw [show (2 : PowerSeries ℤ) = PowerSeries.C 2 by simp, PowerSeries.coeff_C_mul]

/-- The signed source convolution is the quadratic marked coefficient of
the unweighted geometric product times the linear gap contribution. -/
theorem mixedNumerator_eq_marked_coefficient (d : SimplexData) (j : Fin 10) (k : ℕ) :
    let G := fun i => geometric (d.y i : ℤ)
    let a := fun i => PowerSeries.C (d.gaps i : ℤ) * G i
    let b := fun i => PowerSeries.C (d.deviations j i) * G i
    PowerSeries.coeff k ((∏ i, G i) *
      (2 * (markProduct Finset.univ b * markWeight Finset.univ a b).coeff 2)) =
      mixedNumerator d j k := by
  let G := fun i => geometric (d.y i : ℤ)
  let a := fun i => PowerSeries.C (d.gaps i : ℤ) * G i
  let b := fun i => PowerSeries.C (d.deviations j i) * G i
  change PowerSeries.coeff k ((∏ i, G i) *
    (2 * (markProduct Finset.univ b * markWeight Finset.univ a b).coeff 2)) = _
  have hH (n : ℕ) : PowerSeries.coeff n (∏ i, G i) = (homogeneous d.y n : ℤ) :=
    coeff_product_geometric d.y (Nat.le_refl n)
  have hB1 (n : ℕ) : PowerSeries.coeff n (∑ i, b i) = B1 d j n := by
    simp only [b, G, B1, map_sum, PowerSeries.coeff_C_mul, coeff_geometric]
  have hB2 (n : ℕ) : PowerSeries.coeff n (∑ i, b i ^ 2) = B2 d j n := by
    rw [map_sum, B2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [b, G]
    rw [pow_two]
    have h := coeff_leftScaled (d.deviations j i) (d.deviations j i) (d.y i : ℤ) 1 n
    simpa only [pow_one, Nat.choose_one_right, Nat.cast_add, Nat.cast_one, pow_two,
      mul_left_comm] using h
  have hW0 (n : ℕ) : PowerSeries.coeff n (∑ i, a i) = W0 d n := by
    simp only [a, G, W0, map_sum, PowerSeries.coeff_C_mul, coeff_geometric]
  have hW1 (n : ℕ) : PowerSeries.coeff n (∑ i, a i * b i) = W1 d j n := by
    rw [map_sum, W1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := coeff_leftScaled (d.gaps i : ℤ) (d.deviations j i) (d.y i : ℤ) 1 n
    simpa only [a, b, G, pow_one, Nat.choose_one_right, Nat.cast_add,
      Nat.cast_one, mul_left_comm] using h
  have hW2 (n : ℕ) : PowerSeries.coeff n (∑ i, a i * b i ^ 2) = W2 d j n := by
    rw [map_sum, W2, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h := coeff_leftScaled (d.gaps i : ℤ) (d.deviations j i) (d.y i : ℤ) 2 n
    simpa only [a, b, G, mul_left_comm] using h
  rw [double_coeff_weighted_mark, coeff_mul_conv, mixedNumerator]
  unfold doubled
  simp only [map_add, coeff_two_mul]
  simp only [hH, pow_two (∑ i, b i), coeff_mul_conv, hB1, hW0, hW1, hW2]
  simp only [map_add, coeff_mul_conv, hB1, hB2]

private def delta {ι R : Type*} [DecidableEq ι] [Zero R] [One R] (i j : ι) : R :=
  if i = j then 1 else 0

/-- The factorial weights for three labelled insertions, expressed by their
equality partition. -/
def tripleKernel {ι R : Type*} [DecidableEq ι] [Semiring R] (i j l : ι) : R :=
  (1 + delta i j) + (1 + 2 * delta i j) * delta i l + delta j l

private theorem sum_mul_delta {ι R : Type*} [DecidableEq ι] [Fintype ι]
    [Semiring R] (b : ι → R) (i : ι) : (∑ j, b j * delta i j) = b i := by
  simp [delta, mul_ite]

/-- Expand the marked coefficient as the three labelled insertions. -/
theorem triple_sum_eq_marked {ι R : Type*} [DecidableEq ι] [Fintype ι]
    [CommSemiring R] (a b : ι → R) :
    (∑ i, ∑ j, ∑ l, a i * b j * b l * tripleKernel i j l) =
      2 * (markProduct Finset.univ b * markWeight Finset.univ a b).coeff 2 := by
  let S := ∑ i, b i
  let Q := ∑ i, b i ^ 2
  have inner (i j : ι) :
      (∑ l, a i * b j * b l * tripleKernel i j l) =
        a i * b j * ((1 + delta i j) * S + (1 + 2 * delta i j) * b i + b j) := by
    calc
      _ = a i * b j * (∑ l, (b l * (1 + delta i j) +
            (b l * delta i l) * (1 + 2 * delta i j) + b l * delta j l)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold tripleKernel
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, sum_mul_delta, S]
        ring
  have middle (i : ι) :
      (∑ j, a i * b j * ((1 + delta i j) * S + (1 + 2 * delta i j) * b i + b j)) =
        2 * (a i * b i ^ 2) + 2 * (S * (a i * b i)) + (S^2 + Q) * a i := by
    calc
      _ = a i * (∑ j, (b j * (S + b i) + (b j * delta i j) * (S + 2 * b i) + b j ^ 2)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.sum_mul, sum_mul_delta, S, Q]
        ring
  rw [double_coeff_weighted_mark]
  simp only [inner, middle, Finset.sum_add_distrib, ← Finset.mul_sum, S, Q]

/-- The coefficient of a product with arbitrary multiplicities is its
finite sum over exponent compositions. -/
theorem coeff_product_powers {R : Type*} [CommSemiring R]
    (y : Fin 9 → R) (m : Fin 9 → ℕ) (k : ℕ) :
    PowerSeries.coeff k (∏ i, geometric (y i) ^ (m i + 1)) =
      ∑ e ∈ Finset.piAntidiag Finset.univ k,
        ∏ i, ((e i + m i).choose (m i) : R) * (y i)^(e i) := by
  rw [PowerSeries.coeff_prod]
  refine Finset.sum_bij' (fun e _ => (e : Fin 9 → ℕ))
    (fun e _ => Finsupp.equivFunOnFinite.symm e) ?_ ?_ ?_ ?_ ?_
  · intro e he
    simpa using (Finset.mem_finsuppAntidiag.mp he).1
  · intro e he
    simpa using (Finset.mem_piAntidiag.mp he).1
  · intro e _
    exact Finsupp.equivFunOnFinite.symm_apply_apply e
  · intro e _
    exact Finsupp.equivFunOnFinite.apply_symm_apply e
  · intro e _
    simp only [coeff_geometric_pow]

/-- Multiplicities of the three marked vertices in a simplex monomial. -/
def insertionCount (a c r i : Fin 9) : ℕ :=
  delta i a + delta i c + delta i r

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
private theorem factorial_triple_list : ∀ a c r : Fin 9,
    ((List.ofFn (insertionCount a c r)).map Nat.factorial).prod =
      tripleKernel (R := ℕ) a c r := by
  decide +kernel

theorem factorial_triple_product (a c r : Fin 9) :
    (∏ i, (insertionCount a c r i).factorial) = tripleKernel (R := ℕ) a c r := by
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply] using factorial_triple_list a c r

private theorem prod_pow_delta {R : Type*} [CommMonoid R] (G : Fin 9 → R) (a : Fin 9) :
    (∏ i, G i ^ (delta i a : ℕ)) = G a := by
  refine (Fintype.prod_eq_single a (fun i h => ?_)).trans ?_
  · simp [delta, h]
  · simp [delta]

private theorem prod_pow_insertions {R : Type*} [CommMonoid R]
    (G : Fin 9 → R) (a c r : Fin 9) :
    (∏ i, G i ^ (insertionCount a c r i + 1)) =
      (∏ i, G i) * G a * G c * G r := by
  simp only [insertionCount, pow_add, Finset.prod_mul_distrib, prod_pow_delta, pow_one]
  ac_rfl

/-- The source convolution equals the factorial-weighted multinomial
composition sum of the three labelled vertex insertions, in every degree. -/
theorem triple_compositions_eq_mixedNumerator (d : SimplexData) (j : Fin 10) (k : ℕ) :
    (∑ a : Fin 9, ∑ c : Fin 9, ∑ r : Fin 9,
      (d.gaps a : ℤ) * d.deviations j c * d.deviations j r *
      ((∏ i, (insertionCount a c r i).factorial : ℕ) : ℤ) *
      (∑ e ∈ Finset.piAntidiag Finset.univ k,
        ∏ i, ((e i + insertionCount a c r i).choose (insertionCount a c r i) : ℤ) *
          (d.y i : ℤ)^(e i))) = mixedNumerator d j k := by
  let G := fun i => geometric (d.y i : ℤ)
  let a := fun i => PowerSeries.C (d.gaps i : ℤ) * G i
  let b := fun i => PowerSeries.C (d.deviations j i) * G i
  have hm : PowerSeries.coeff k ((∏ i, G i) *
      (2 * (markProduct Finset.univ b * markWeight Finset.univ a b).coeff 2)) =
      mixedNumerator d j k := mixedNumerator_eq_marked_coefficient d j k
  rw [← triple_sum_eq_marked] at hm
  simp only [Finset.mul_sum, map_sum] at hm
  refine Eq.trans ?_ hm
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun c _ =>
    Finset.sum_congr rfl (fun r _ => ?_)))
  rw [← coeff_product_powers (fun q => (d.y q : ℤ)) (insertionCount i c r) k,
    ← PowerSeries.coeff_C_mul]
  change PowerSeries.coeff k (PowerSeries.C _ * (∏ q, G q ^ (insertionCount i c r q + 1))) = _
  have hK : PowerSeries.C (((∏ q, (insertionCount i c r q).factorial : ℕ) : ℤ)) =
      tripleKernel (R := PowerSeries ℤ) i c r := by
    rw [factorial_triple_product]
    unfold tripleKernel delta
    split_ifs <;> norm_num
  rw [prod_pow_insertions]
  congr 1
  simp only [map_mul, hK, a, b]
  ring

end

end ImbalancedChen.P2Winner9MarkedCoefficient
