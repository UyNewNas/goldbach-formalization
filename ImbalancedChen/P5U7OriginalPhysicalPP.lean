import ImbalancedChen.P5U7OriginalArithmeticFamily
import ImbalancedChen.P5zPositiveFamilyBudget

/-!
# Original U7 arithmetic prime and semiprime branches as native Part3 families

The two concrete marked coefficients have ranks three and four and take
only the values zero and one. Their inverse slot maps retain the original
outer pair and all terminal labels, including p₂=q, p₂=r and r=s. Source
membership, original square-root walls and complete centre-coprimality are
unchanged. There is no prime test on N minus the physical product.

The total product-weight source error is PP3+PP4 as one SIGNED sum; its
norm is taken only afterwards. No separate J3/J4 or sharpK mean is assumed.
SOURCE-WRITTEN, UNCOMPILED. Earlier candidates remain frozen.
-/

namespace ImbalancedChen.P5U7OriginalPhysicalPP

noncomputable section
open scoped BigOperators
open Classical

def coords3 (x : P5U7ThreeLabel) : Fin 3 → ℕ := ![x.1.1,x.1.2,x.2]
def coords4 (x : P5U7FourLabel) : Fin 4 → ℕ := ![x.1.1,x.1.2,x.2.1,x.2.2]

def inverse3 {N : ℕ} (u : Fin 3 → Fin (N+1)) : P5U7ThreeLabel :=
  ⟨((u 0).val,(u 1).val),(u 2).val⟩
def inverse4 {N : ℕ} (u : Fin 4 → Fin (N+1)) : P5U7FourLabel :=
  ⟨((u 0).val,(u 1).val),((u 2).val,(u 3).val)⟩

theorem coords3_inverse {N : ℕ} (u : Fin 3 → Fin (N+1)) (i : Fin 3) :
    coords3 (inverse3 u) i = (u i).val := by
  fin_cases i <;> simp [coords3,inverse3]

theorem coords4_inverse {N : ℕ} (u : Fin 4 → Fin (N+1)) (i : Fin 4) :
    coords4 (inverse4 u) i = (u i).val := by
  fin_cases i <;> simp [coords4,inverse4]

theorem coords3_injective : Function.Injective coords3 := by
  intro x y h
  rcases x with ⟨⟨p1,p2⟩,q⟩
  rcases y with ⟨⟨v1,v2⟩,w⟩
  have h0 : p1=v1 := by simpa [coords3] using congrFun h (0 : Fin 3)
  have h1 : p2=v2 := by simpa [coords3] using congrFun h (1 : Fin 3)
  have h2 : q=w := by simpa [coords3] using congrFun h (2 : Fin 3)
  subst v1; subst v2; subst w
  rfl

theorem coords4_injective : Function.Injective coords4 := by
  intro x y h
  rcases x with ⟨⟨p1,p2⟩,⟨r,s⟩⟩
  rcases y with ⟨⟨v1,v2⟩,⟨w,z⟩⟩
  have h0 : p1=v1 := by simpa [coords4] using congrFun h (0 : Fin 4)
  have h1 : p2=v2 := by simpa [coords4] using congrFun h (1 : Fin 4)
  have h2 : r=w := by simpa [coords4] using congrFun h (2 : Fin 4)
  have h3 : s=z := by simpa [coords4] using congrFun h (3 : Fin 4)
  subst v1; subst v2; subst w; subst z
  rfl

theorem coords3_product (x : P5U7ThreeLabel) :
    (∏ i : Fin 3, coords3 x i) = p5U7ThreeProduct x := by
  simp [coords3,Fin.prod_univ_three,p5U7ThreeProduct,mul_assoc]

theorem coords4_product (x : P5U7FourLabel) :
    (∏ i : Fin 4, coords4 x i) = p5U7FourProduct x := by
  simp [coords4,Fin.prod_univ_four,p5U7FourProduct,mul_assoc]

theorem coords3_prime_cap {N : ℕ} {x : P5U7ThreeLabel}
    (hx : x ∈ p5U7ArithmeticThree N) (i : Fin 3) :
    Nat.Prime (coords3 x i) ∧ coords3 x i ≤ N := by
  obtain ⟨ht,hq⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hc,_,_,_⟩ := Finset.mem_filter.mp ht
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
  have h3 := (Finset.mem_filter.mp hq).1
  have hdata : ∀ {p : ℕ}, p ∈ chenAdditivePrimeCarrier N → Nat.Prime p ∧ p ≤ N := by
    intro p hp
    exact ⟨(mem_chenAdditivePrimeCarrier.mp hp).2.1,(mem_chenAdditivePrimeCarrier.mp hp).1.le⟩
  fin_cases i
  · simpa [coords3] using hdata h1
  · simpa [coords3] using hdata h2
  · simpa [coords3] using hdata h3

theorem coords4_prime_cap {N : ℕ} {x : P5U7FourLabel}
    (hx : x ∈ p5U7ArithmeticFour N) (i : Fin 4) :
    Nat.Prime (coords4 x i) ∧ coords4 x i ≤ N := by
  obtain ⟨ht,hrs⟩ := Finset.mem_sigma.mp hx
  obtain ⟨hc,_,_,_⟩ := Finset.mem_filter.mp ht
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
  obtain ⟨h3,h4⟩ := Finset.mem_product.mp (Finset.mem_filter.mp hrs).1
  have hdata : ∀ {p : ℕ}, p ∈ chenAdditivePrimeCarrier N → Nat.Prime p ∧ p ≤ N := by
    intro p hp
    exact ⟨(mem_chenAdditivePrimeCarrier.mp hp).2.1,(mem_chenAdditivePrimeCarrier.mp hp).1.le⟩
  fin_cases i
  · simpa [coords4] using hdata h1
  · simpa [coords4] using hdata h2
  · simpa [coords4] using hdata h3
  · simpa [coords4] using hdata h4

/-- A generic finite bijection theorem, instantiated below at both
actual original branches. Its hypotheses concern only finite slot maps. -/
theorem finite_marked_reindex {A : Type*} [DecidableEq A] (k N : ℕ) (S : Finset A)
    (coord : A → Fin k → ℕ) (inv : (Fin k → Fin (N+1)) → A) (prod : A → ℕ)
    (hinj : Function.Injective coord)
    (hcoord : ∀ u i, coord (inv u) i = (u i).val)
    (hprime : ∀ x ∈ S, ∀ i, Nat.Prime (coord x i) ∧ coord x i ≤ N)
    (hprod : ∀ x, (∏ i, coord x i) = prod x) (F : ℕ → ℝ) :
    (∑ x ∈ S, F (prod x)) =
      ∑ u ∈ Part3.labelledPrimeTuples k N,
        (if inv u ∈ S then (1 : ℝ) else 0) * F (Part3.labelledProduct u) := by
  let encode : (x : A) → x ∈ S → (Fin k → Fin (N+1)) :=
    fun x hx i => ⟨coord x i,Nat.lt_succ_of_le (hprime x hx i).2⟩
  have hinverse (x : A) (hx : x ∈ S) : inv (encode x hx) = x := by
    apply hinj
    funext i
    exact hcoord (encode x hx) i
  let T := (Part3.labelledPrimeTuples k N).filter (fun u => inv u ∈ S)
  have hbij : (∑ x ∈ S, F (prod x)) = ∑ u ∈ T, F (Part3.labelledProduct u) := by
    refine Finset.sum_bij encode ?_ ?_ ?_ ?_
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,fun i => (hprime x hx i).1⟩,by rw [hinverse x hx]; exact hx⟩
    · intro x hx y hy heq
      apply hinj
      funext i
      exact congrArg (fun u : Fin k → Fin (N+1) => (u i).val) heq
    · intro u hu
      have hi := (Finset.mem_filter.mp hu).2
      refine ⟨inv u,hi,?_⟩
      funext i
      apply Fin.ext
      exact hcoord u i
    · intro x hx
      have hp : Part3.labelledProduct (encode x hx) = prod x := hprod x
      exact congrArg F hp.symm
  calc
    _ = ∑ u ∈ T, F (Part3.labelledProduct u) := hbij
    _ = _ := by
      dsimp only [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases hu : inv u ∈ S <;> simp only [hu,if_true,if_false,one_mul,zero_mul]

def weight3 (N : ℕ) (u : Fin 3 → Fin (N+1)) : ℝ :=
  if inverse3 u ∈ p5U7ArithmeticThree N then 1 else 0
def weight4 (N : ℕ) (u : Fin 4 → Fin (N+1)) : ℝ :=
  if inverse4 u ∈ p5U7ArithmeticFour N then 1 else 0

theorem weight3_zero_or_one (N : ℕ) (u : Fin 3 → Fin (N+1)) :
    weight3 N u = 0 ∨ weight3 N u = 1 := by
  unfold weight3
  split_ifs <;> simp
theorem weight4_zero_or_one (N : ℕ) (u : Fin 4 → Fin (N+1)) :
    weight4 N u = 0 ∨ weight4 N u = 1 := by
  unfold weight4
  split_ifs <;> simp

theorem weight3_abs_le_one (N : ℕ) (u : Fin 3 → Fin (N+1)) : |weight3 N u| ≤ 1 := by
  unfold weight3
  split_ifs <;> norm_num
theorem weight4_abs_le_one (N : ℕ) (u : Fin 4 → Fin (N+1)) : |weight4 N u| ≤ 1 := by
  unfold weight4
  split_ifs <;> norm_num

theorem weight3_sum (N : ℕ) (F : ℕ → ℝ) :
    (∑ x ∈ p5U7ArithmeticThree N, F (p5U7ThreeProduct x)) =
      ∑ u ∈ Part3.labelledPrimeTuples 3 N, weight3 N u * F (Part3.labelledProduct u) := by
  exact finite_marked_reindex 3 N (p5U7ArithmeticThree N) coords3 inverse3 p5U7ThreeProduct
    coords3_injective coords3_inverse (fun x hx => coords3_prime_cap hx) coords3_product F

theorem weight4_sum (N : ℕ) (F : ℕ → ℝ) :
    (∑ x ∈ p5U7ArithmeticFour N, F (p5U7FourProduct x)) =
      ∑ u ∈ Part3.labelledPrimeTuples 4 N, weight4 N u * F (Part3.labelledProduct u) := by
  exact finite_marked_reindex 4 N (p5U7ArithmeticFour N) coords4 inverse4 p5U7FourProduct
    coords4_injective coords4_inverse (fun x hx => coords4_prime_cap hx) coords4_product F

theorem congruence3_eq (N ell : ℕ) :
    p5z_labelledCongruenceMass (p5U7ArithmeticThree N) p5U7ThreeProduct (fun _ => 1) N ell =
      p5z_labelledCongruenceMass (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (weight3 N) N ell := by
  simpa only [p5z_labelledCongruenceMass,mul_ite,mul_one,mul_zero] using
    weight3_sum N (fun m => if Nat.ModEq ell m N then 1 else 0)
theorem coprime3_eq (N ell : ℕ) :
    p5z_labelledCoprimeMass (p5U7ArithmeticThree N) p5U7ThreeProduct (fun _ => 1) ell =
      p5z_labelledCoprimeMass (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (weight3 N) ell := by
  simpa only [p5z_labelledCoprimeMass,mul_ite,mul_one,mul_zero] using
    weight3_sum N (fun m => if Nat.Coprime m ell then 1 else 0)
theorem congruence4_eq (N ell : ℕ) :
    p5z_labelledCongruenceMass (p5U7ArithmeticFour N) p5U7FourProduct (fun _ => 1) N ell =
      p5z_labelledCongruenceMass (Part3.labelledPrimeTuples 4 N) Part3.labelledProduct
        (weight4 N) N ell := by
  simpa only [p5z_labelledCongruenceMass,mul_ite,mul_one,mul_zero] using
    weight4_sum N (fun m => if Nat.ModEq ell m N then 1 else 0)
theorem coprime4_eq (N ell : ℕ) :
    p5z_labelledCoprimeMass (p5U7ArithmeticFour N) p5U7FourProduct (fun _ => 1) ell =
      p5z_labelledCoprimeMass (Part3.labelledPrimeTuples 4 N) Part3.labelledProduct
        (weight4 N) ell := by
  simpa only [p5z_labelledCoprimeMass,mul_ite,mul_one,mul_zero] using
    weight4_sum N (fun m => if Nat.Coprime m ell then 1 else 0)

theorem inverse3_product {N : ℕ} (u : Fin 3 → Fin (N+1)) :
    p5U7ThreeProduct (inverse3 u) = Part3.labelledProduct u := by
  rw [← coords3_product]
  unfold Part3.labelledProduct
  apply Finset.prod_congr rfl
  intro i _
  exact coords3_inverse u i
theorem inverse4_product {N : ℕ} (u : Fin 4 → Fin (N+1)) :
    p5U7FourProduct (inverse4 u) = Part3.labelledProduct u := by
  rw [← coords4_product]
  unfold Part3.labelledProduct
  apply Finset.prod_congr rfl
  intro i _
  exact coords4_inverse u i

theorem weight3_support {N : ℕ} {u : Fin 3 → Fin (N+1)} (hu : weight3 N u ≠ 0) :
    inverse3 u ∈ p5U7ArithmeticThree N := by
  by_contra hnot
  exact hu (by simp only [weight3,if_neg hnot])
theorem weight4_support {N : ℕ} {u : Fin 4 → Fin (N+1)} (hu : weight4 N u ≠ 0) :
    inverse4 u ∈ p5U7ArithmeticFour N := by
  by_contra hnot
  exact hu (by simp only [weight4,if_neg hnot])

theorem weight3_original_walls {N : ℕ} {u : Fin 3 → Fin (N+1)} (hu : weight3 N u ≠ 0) :
    (N : ℝ) ^ (59 / 250 : ℝ) ≤ ((u 0).val : ℝ) ∧ (u 0).val < (u 1).val ∧
      (u 1).val ≤ (u 2).val ∧
      ((u 1).val : ℝ) < Real.sqrt ((N : ℝ) / ((u 0).val : ℝ)) :=
  p5U7ArithmeticThree_original_walls (weight3_support hu)
theorem weight4_original_walls {N : ℕ} {u : Fin 4 → Fin (N+1)} (hu : weight4 N u ≠ 0) :
    (N : ℝ) ^ (59 / 250 : ℝ) ≤ ((u 0).val : ℝ) ∧ (u 0).val < (u 1).val ∧
      (u 1).val ≤ (u 2).val ∧ (u 1).val ≤ (u 3).val ∧
      ((u 1).val : ℝ) < Real.sqrt ((N : ℝ) / ((u 0).val : ℝ)) :=
  p5U7ArithmeticFour_original_walls (weight4_support hu)

/-- Sorted weak terminal walls retain repeated coordinates literally. -/
theorem weight3_sorted_primitive {N : ℕ} {u : Fin 3 → Fin (N+1)} (hu : weight3 N u ≠ 0) :
    (u 0).val < (u 1).val ∧ (u 1).val ≤ (u 2).val ∧
      Part3.labelledProduct u < N ∧ Nat.Coprime (Part3.labelledProduct u) N ∧
      Nat.Coprime (N-Part3.labelledProduct u) N := by
  obtain ⟨_,_,_,_,h12,h2q,_,hlt,hcop⟩ := p5U7ArithmeticThree_data (weight3_support hu)
  rw [inverse3_product] at hlt hcop
  exact ⟨h12,h2q,hlt,hcop,(Nat.coprime_self_sub_left hlt.le).mpr hcop⟩

theorem weight4_sorted_primitive {N : ℕ} {u : Fin 4 → Fin (N+1)} (hu : weight4 N u ≠ 0) :
    (u 0).val < (u 1).val ∧ (u 1).val ≤ (u 2).val ∧ (u 2).val ≤ (u 3).val ∧
      Part3.labelledProduct u < N ∧ Nat.Coprime (Part3.labelledProduct u) N ∧
      Nat.Coprime (N-Part3.labelledProduct u) N := by
  obtain ⟨_,_,_,_,_,h12,h2r,hrs,_,hlt,hcop⟩ := p5U7ArithmeticFour_data (weight4_support hu)
  rw [inverse4_product] at hlt hcop
  exact ⟨h12,h2r,hrs,hlt,hcop,(Nat.coprime_self_sub_left hlt.le).mpr hcop⟩

theorem weight3_lower_power {N : ℕ} {u : Fin 3 → Fin (N+1)} (hu : weight3 N u ≠ 0) :
    ∀ i : Fin 3, (N : ℝ) ^ (59 / 250 : ℝ) ≤ ((u i).val : ℝ) := by
  obtain ⟨hD,h12,h2q,_⟩ := p5U7ArithmeticThree_original_walls (weight3_support hu)
  have h01 : ((u 0).val : ℝ) ≤ ((u 1).val : ℝ) := by exact_mod_cast h12.le
  have h12R : ((u 1).val : ℝ) ≤ ((u 2).val : ℝ) := by exact_mod_cast h2q
  intro i
  fin_cases i
  · exact hD
  · exact hD.trans h01
  · exact hD.trans (h01.trans h12R)

theorem weight4_lower_power {N : ℕ} {u : Fin 4 → Fin (N+1)} (hu : weight4 N u ≠ 0) :
    ∀ i : Fin 4, (N : ℝ) ^ (59 / 250 : ℝ) ≤ ((u i).val : ℝ) := by
  obtain ⟨hD,h12,h2r,h2s,_⟩ := p5U7ArithmeticFour_original_walls (weight4_support hu)
  have h01 : ((u 0).val : ℝ) ≤ ((u 1).val : ℝ) := by exact_mod_cast h12.le
  have h02 : ((u 0).val : ℝ) ≤ ((u 2).val : ℝ) := by exact_mod_cast h12.le.trans h2r
  have h03 : ((u 0).val : ℝ) ≤ ((u 3).val : ℝ) := by exact_mod_cast h12.le.trans h2s
  intro i
  fin_cases i
  · exact hD
  · exact hD.trans h01
  · exact hD.trans h02
  · exact hD.trans h03

/-- Finite signed-distribution transport derived only from exact test
reindexing; it adds no analytic estimate or geometric licence. -/
theorem distribution_reindex {A : Type*} (k N : ℕ) (S : Finset A) (f : A → ℕ)
    (W : (Fin k → Fin (N+1)) → ℝ)
    (hsum : ∀ F : ℕ → ℝ, (∑ x ∈ S, F (f x)) =
      ∑ u ∈ Part3.labelledPrimeTuples k N, W u * F (Part3.labelledProduct u))
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError S f (fun _ => 1) N Q rho =
      Part3.primeProductSignedError k N N Q rho W := by
  have hc : ∀ ell, p5z_labelledCongruenceMass S f (fun _ => 1) N ell =
      p5z_labelledCongruenceMass (Part3.labelledPrimeTuples k N) Part3.labelledProduct W N ell := by
    intro ell
    simpa only [p5z_labelledCongruenceMass,mul_ite,mul_one,mul_zero] using
      hsum (fun m => if Nat.ModEq ell m N then 1 else 0)
  have hp : ∀ ell, p5z_labelledCoprimeMass S f (fun _ => 1) ell =
      p5z_labelledCoprimeMass (Part3.labelledPrimeTuples k N) Part3.labelledProduct W ell := by
    intro ell
    simpa only [p5z_labelledCoprimeMass,mul_ite,mul_one,mul_zero] using
      hsum (fun m => if Nat.Coprime m ell then 1 else 0)
  calc
    _ = p5z_labelledDistributionError (Part3.labelledPrimeTuples k N) Part3.labelledProduct W N Q rho := by
      unfold p5z_labelledDistributionError
      simp_rw [hc,hp]
    _ = _ := p5z_labelledDistributionError_eq_primeProductSignedError k N N Q rho W

theorem distribution3_eq_PP (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5U7ArithmeticThree N) p5U7ThreeProduct (fun _ => 1) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho (weight3 N) :=
  distribution_reindex 3 N _ _ (weight3 N) (weight3_sum N) Q rho
theorem distribution4_eq_PP (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (p5U7ArithmeticFour N) p5U7FourProduct (fun _ => 1) N Q rho =
      Part3.primeProductSignedError 4 N N Q rho (weight4 N) :=
  distribution_reindex 4 N _ _ (weight4 N) (weight4_sum N) Q rho

/-- One original signed source error equals PP3+PP4. The ranks are kept
as marked family members; no norms or separate mass constants are inserted. -/
theorem total_source_error_eq_PP3_add_PP4 (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (Finset.range N) id (p5U7ArithmeticProductWeight N) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho (weight3 N) +
        Part3.primeProductSignedError 4 N N Q rho (weight4 N) := by
  have hc : ∀ ell, p5z_labelledCongruenceMass (Finset.range N) id
      (p5U7ArithmeticProductWeight N) N ell =
      p5z_labelledCongruenceMass (p5U7ArithmeticThree N) p5U7ThreeProduct (fun _ => 1) N ell +
        p5z_labelledCongruenceMass (p5U7ArithmeticFour N) p5U7FourProduct (fun _ => 1) N ell := by
    intro ell
    simpa only [p5z_labelledCongruenceMass,id_eq,mul_ite,mul_one,mul_zero] using
      p5U7Arithmetic_product_weighted_Fubini N (fun m => if Nat.ModEq ell m N then 1 else 0)
  have hp : ∀ ell, p5z_labelledCoprimeMass (Finset.range N) id
      (p5U7ArithmeticProductWeight N) ell =
      p5z_labelledCoprimeMass (p5U7ArithmeticThree N) p5U7ThreeProduct (fun _ => 1) ell +
        p5z_labelledCoprimeMass (p5U7ArithmeticFour N) p5U7FourProduct (fun _ => 1) ell := by
    intro ell
    simpa only [p5z_labelledCoprimeMass,id_eq,mul_ite,mul_one,mul_zero] using
      p5U7Arithmetic_product_weighted_Fubini N (fun m => if Nat.Coprime m ell then 1 else 0)
  rw [← distribution3_eq_PP,← distribution4_eq_PP]
  unfold p5z_labelledDistributionError
  simp_rw [hc,hp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ell _
  ring

theorem abs_total_source_error_eq_combined_PP_norm (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |p5z_labelledDistributionError (Finset.range N) id (p5U7ArithmeticProductWeight N) N Q rho| =
      |Part3.primeProductSignedError 3 N N Q rho (weight3 N) +
        Part3.primeProductSignedError 4 N N Q rho (weight4 N)| :=
  congrArg abs (total_source_error_eq_PP3_add_PP4 N Q rho)

theorem abs_two_source_error_eq_combined_PP_norm (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    |2 * p5z_labelledDistributionError (Finset.range N) id (p5U7ArithmeticProductWeight N) N Q rho| =
      |2 * (Part3.primeProductSignedError 3 N N Q rho (weight3 N) +
        Part3.primeProductSignedError 4 N N Q rho (weight4 N))| := by
  rw [total_source_error_eq_PP3_add_PP4]

end ImbalancedChen.P5U7OriginalPhysicalPP
