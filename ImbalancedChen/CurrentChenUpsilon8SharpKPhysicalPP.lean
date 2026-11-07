import ImbalancedChen.CurrentChenUpsilon8SharpKArithmeticSource
import ImbalancedChen.CurrentChenUpsilon8SourceErrorBudget

/-!
# The original U8 sharp-K entry as a sorted rank-three Part3 family

The physical coefficient is a modulus-independent zero-one indicator on
Part3's literal labelledPrimeTuples 3 N. It retains p₁<p₂<=q, including
the q=p₂ diagonal, the original square-root wall and centre mask. Exact
signed PP reindexing precedes every norm. The diagonal and unit counts
are separately retained and proved negligible. No currentK distribution
or density supplier is presumed. SOURCE-WRITTEN, UNCOMPILED.
-/

namespace ImbalancedChen.P5U8SharpKSource

noncomputable section
open scoped BigOperators
open Classical

def natCoord (t : Triple) : Fin 3 → ℕ := ![t.1.1,t.1.2,t.2]

theorem natCoord_product (t : Triple) : (∏ i : Fin 3, natCoord t i) = product t := by
  simp [natCoord,Fin.prod_univ_three,product,mul_assoc]

theorem natCoord_injective : Function.Injective natCoord := by
  intro t s h
  rcases t with ⟨⟨p1,p2⟩,q⟩
  rcases s with ⟨⟨r1,r2⟩,v⟩
  have h0 : p1=r1 := by simpa [natCoord] using congrFun h (0 : Fin 3)
  have h1 : p2=r2 := by simpa [natCoord] using congrFun h (1 : Fin 3)
  have h2 : q=v := by simpa [natCoord] using congrFun h (2 : Fin 3)
  subst r1; subst r2; subst v
  rfl

theorem natCoord_prime_cap {N : ℕ} {t : Triple} (ht : t ∈ arithmeticTriples N) (i : Fin 3) :
    Nat.Prime (natCoord t i) ∧ natCoord t i ≤ N := by
  have hp := pair_prime_data (arithmetic_data ht).1
  have hq := (arithmetic_data ht).2.2.1
  have hqN := Nat.le_of_lt_succ (arithmetic_data ht).2.1
  fin_cases i
  · simpa [natCoord] using And.intro hp.1 hp.2.2.2.1.le
  · simpa [natCoord] using And.intro hp.2.1 hp.2.2.2.2.le
  · simpa [natCoord] using And.intro hq hqN

def physicalInverse {N : ℕ} (u : Fin 3 → Fin (N+1)) : Triple :=
  ⟨((u 0).val,(u 1).val),(u 2).val⟩

theorem natCoord_physicalInverse {N : ℕ} (u : Fin 3 → Fin (N+1)) (i : Fin 3) :
    natCoord (physicalInverse u) i = (u i).val := by
  fin_cases i <;> simp [natCoord,physicalInverse]

theorem physicalInverse_product {N : ℕ} (u : Fin 3 → Fin (N+1)) :
    product (physicalInverse u) = Part3.labelledProduct u := by
  rw [← natCoord_product]
  unfold Part3.labelledProduct
  apply Finset.prod_congr rfl
  intro i _
  exact natCoord_physicalInverse u i

def physicalWeight (N : ℕ) (u : Fin 3 → Fin (N+1)) : ℝ :=
  if physicalInverse u ∈ arithmeticTriples N then 1 else 0

theorem physicalWeight_abs_le_one (N : ℕ) (u : Fin 3 → Fin (N+1)) :
    |physicalWeight N u| ≤ 1 := by
  unfold physicalWeight
  split_ifs <;> norm_num

theorem physicalWeight_support_data {N : ℕ} {u : Fin 3 → Fin (N+1)}
    (hu : physicalWeight N u ≠ 0) :
    (u 0).val < (u 1).val ∧ (u 1).val ≤ (u 2).val ∧
      Part3.labelledProduct u < N ∧ Nat.Coprime (Part3.labelledProduct u) N ∧
      Nat.Coprime (N-Part3.labelledProduct u) N := by
  have ht : physicalInverse u ∈ arithmeticTriples N := by
    by_contra hnot
    exact hu (by simp only [physicalWeight,if_neg hnot])
  have hs := arithmetic_sorted ht
  refine ⟨hs.1,hs.2,?_,?_,?_⟩
  · rw [← physicalInverse_product]; exact arithmetic_product_lt ht
  · rw [← physicalInverse_product]; exact arithmetic_product_coprime ht
  · rw [← physicalInverse_product]; exact (arithmetic_data ht).2.2.2.2.2

theorem physicalWeight_lower_power {N : ℕ} {u : Fin 3 → Fin (N+1)}
    (hu : physicalWeight N u ≠ 0) :
    ∀ i : Fin 3, (N : ℝ) ^ (417 / 5000 : ℝ) ≤ ((u i).val : ℝ) := by
  have ht : physicalInverse u ∈ arithmeticTriples N := by
    by_contra hnot
    exact hu (by simp only [physicalWeight,if_neg hnot])
  obtain ⟨_,hA,_⟩ := Finset.mem_filter.mp (arithmetic_data ht).1
  have hs := arithmetic_sorted ht
  have h01 : ((u 0).val : ℝ) ≤ ((u 1).val : ℝ) := by exact_mod_cast hs.1.le
  have h12 : ((u 1).val : ℝ) ≤ ((u 2).val : ℝ) := by exact_mod_cast hs.2
  intro i
  fin_cases i
  · exact hA
  · exact hA.trans h01
  · exact hA.trans (h01.trans h12)

/-- Actual finite bijection with native Part3 triples. The entire source
predicate is the coefficient, independent of every future physical modulus. -/
theorem physicalWeight_sum (N : ℕ) (F : ℕ → ℝ) :
    (∑ t ∈ arithmeticTriples N, F (product t)) =
      ∑ u ∈ Part3.labelledPrimeTuples 3 N, physicalWeight N u * F (Part3.labelledProduct u) := by
  let encode : (t : Triple) → t ∈ arithmeticTriples N → (Fin 3 → Fin (N+1)) :=
    fun t ht i => ⟨natCoord t i,Nat.lt_succ_of_le (natCoord_prime_cap ht i).2⟩
  have hencode_inverse (t : Triple) (ht : t ∈ arithmeticTriples N) :
      physicalInverse (encode t ht) = t := by
    apply natCoord_injective
    funext i
    exact natCoord_physicalInverse (encode t ht) i
  let T := (Part3.labelledPrimeTuples 3 N).filter
    (fun u => physicalInverse u ∈ arithmeticTriples N)
  have hbij : (∑ t ∈ arithmeticTriples N, F (product t)) =
      ∑ u ∈ T, F (Part3.labelledProduct u) := by
    refine Finset.sum_bij encode ?_ ?_ ?_ ?_
    · intro t ht
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i => (natCoord_prime_cap ht i).1⟩
      · rw [hencode_inverse t ht]; exact ht
    · intro t ht s hs heq
      apply natCoord_injective
      funext i
      exact congrArg (fun u : Fin 3 → Fin (N+1) => (u i).val) heq
    · intro u hu
      have hi := (Finset.mem_filter.mp hu).2
      refine ⟨physicalInverse u,hi,?_⟩
      funext i
      apply Fin.ext
      exact natCoord_physicalInverse u i
    · intro t ht
      have hp : Part3.labelledProduct (encode t ht) = product t := natCoord_product t
      exact congrArg F hp.symm
  calc
    _ = ∑ u ∈ T, F (Part3.labelledProduct u) := hbij
    _ = _ := by
      dsimp only [T]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases ht : physicalInverse u ∈ arithmeticTriples N <;>
        simp only [physicalWeight,ht,if_true,if_false,one_mul,zero_mul]

/-- The actual signed error is the rank-three PP target at this concrete
sorted 0/1 coefficient, with no analytic licence added by reindexing. -/
theorem distribution_eq_physicalPP (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (arithmeticTriples N) product (fun _ => 1) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho (physicalWeight N) := by
  have hcong : ∀ ell, p5z_labelledCongruenceMass (arithmeticTriples N) product (fun _ => 1) N ell =
      p5z_labelledCongruenceMass (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (physicalWeight N) N ell := by
    intro ell
    simpa only [p5z_labelledCongruenceMass,mul_ite,mul_one,mul_zero] using
      physicalWeight_sum N (fun m => if Nat.ModEq ell m N then 1 else 0)
  have hcop : ∀ ell, p5z_labelledCoprimeMass (arithmeticTriples N) product (fun _ => 1) ell =
      p5z_labelledCoprimeMass (Part3.labelledPrimeTuples 3 N) Part3.labelledProduct
        (physicalWeight N) ell := by
    intro ell
    simpa only [p5z_labelledCoprimeMass,mul_ite,mul_one,mul_zero] using
      physicalWeight_sum N (fun m => if Nat.Coprime m ell then 1 else 0)
  calc
    _ = p5z_labelledDistributionError (Part3.labelledPrimeTuples 3 N)
        Part3.labelledProduct (physicalWeight N) N Q rho := by
      unfold p5z_labelledDistributionError
      simp_rw [hcong,hcop]
    _ = _ := p5z_labelledDistributionError_eq_primeProductSignedError 3 N N Q rho (physicalWeight N)

theorem productWeight_distribution_eq_physicalPP (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (Finset.range N) id (productWeight N) N Q rho =
      Part3.primeProductSignedError 3 N N Q rho (physicalWeight N) := by
  rw [productWeight_distribution_eq_labels,distribution_eq_physicalPP]

/-- One physical coefficient rho occurs in the actual source divisor
sum, its density, coprime correction and the exact rank-three PP error. -/
theorem same_rho_physical_sum_eq_main_correction_PP (N : ℕ)
    (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, productWeight N m * physicalDivisorSum Q rho (N-m)) =
      p5z_labelledMass (Finset.range N) (productWeight N) * physicalDensitySum Q rho +
        p5z_labelledCoprimeCorrection (Finset.range N) id (productWeight N) Q rho +
        Part3.primeProductSignedError 3 N N Q rho (physicalWeight N) := by
  rw [← productWeight_distribution_eq_physicalPP N Q rho]
  exact same_rho_physical_sum_eq_main_errors N Q rho

def diagonalTriples (N : ℕ) : Finset Triple :=
  (arithmeticTriples N).filter (fun t => t.2=t.1.2)

def strictTriples (N : ℕ) : Finset Triple :=
  (arithmeticTriples N).filter (fun t => t.1.2<t.2)

/-- The repeated q=p₂ diagonal is retained exactly, not dropped as a
formal ordering wall. It is then paid by the following arithmetic bound. -/
theorem arithmetic_card_eq_strict_add_diagonal (N : ℕ) :
    (arithmeticTriples N).card = (strictTriples N).card + (diagonalTriples N).card := by
  have hnot : (arithmeticTriples N).filter (fun t => ¬t.2=t.1.2) = strictTriples N := by
    ext t
    simp only [strictTriples,Finset.mem_filter]
    constructor
    · rintro ⟨ht,hne⟩
      have hs := (arithmetic_sorted ht).2
      exact ⟨ht,by omega⟩
    · rintro ⟨ht,hs⟩; exact ⟨ht,by omega⟩
  have hp := Finset.card_filter_add_card_filter_not (s := arithmeticTriples N)
    (fun t => t.2=t.1.2)
  rw [hnot] at hp
  change (arithmeticTriples N).card = _
  dsimp only [diagonalTriples]
  omega

theorem diagonal_card_le_prefixProducts (N : ℕ) :
    (diagonalTriples N).card ≤ (currentChenUpsilon8PrefixProducts N).card := by
  apply Finset.card_le_card_of_injOn (fun t : Triple => t.1.1*t.1.2)
  · intro t ht
    exact Finset.mem_image.mpr ⟨t.1,(arithmetic_data (Finset.mem_filter.mp ht).1).1,rfl⟩
  · intro x hx y hy hprod
    rcases x with ⟨⟨p1,p2⟩,q⟩
    rcases y with ⟨⟨r1,r2⟩,s⟩
    have hp := chenY8PrimeSelector_multiplier_injOn N _ _
      (arithmetic_data (Finset.mem_filter.mp hx).1).1
      (arithmetic_data (Finset.mem_filter.mp hy).1).1 hprod
    have h1 : p1=r1 := congrArg Prod.fst hp
    have h2 : p2=r2 := congrArg Prod.snd hp
    subst r1; subst r2
    have hq : q=p2 := (Finset.mem_filter.mp hx).2
    have hs : s=p2 := (Finset.mem_filter.mp hy).2
    subst q; subst s
    rfl

theorem diagonal_card_le_power {N : ℕ} (hN : 1 ≤ N) :
    ((diagonalTriples N).card : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact (Nat.cast_le.mpr (diagonal_card_le_prefixProducts N)).trans
    ((Nat.cast_le.mpr (currentChenUpsilon8_prefixProducts_card_le_panUpper hN)).trans
      (currentChenUpsilon8_panUpper_le_two_thirds hNr))

theorem eventually_units_add_diagonal_negligible (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ((currentChenUpsilon8UnitFibres N).card : ℝ) + ((diagonalTriples N).card : ℝ) ≤
        epsilon * singularNormalization N := by
  filter_upwards [eventually_powerLog_le_singularNormalization 2 (2/3) 0
    (by norm_num) epsilon hepsilon, Filter.eventually_ge_atTop (1 : ℕ)] with N hp hN
  have hu := currentChenUpsilon8_unitFibres_card_le_power hN
  have hd := diagonal_card_le_power hN
  simp only [pow_zero,mul_one] at hp
  linarith only [hu,hd,hp]

end ImbalancedChen.P5U8SharpKSource
