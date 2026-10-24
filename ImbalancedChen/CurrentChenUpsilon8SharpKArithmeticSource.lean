import ImbalancedChen.CurrentChenUpsilon8PrimeSource
import ImbalancedChen.P5zPositiveFamilyBudget

/-!
# Original eighth arithmetic source before the additive-prime test

All original pair bands and the moving square-root wall are retained.
The terminal q is prime and q>=p₂; N-p₁p₂q is required only to be coprime
to the centre, not prime. Product fibres retain exact label multiplicity.
Unit quotient fibres remain a separate literal summand of U8.
SOURCE-WRITTEN, UNCOMPILED. No sharp-currentK estimate is asserted.
-/

namespace ImbalancedChen.P5U8SharpKSource

noncomputable section
open scoped BigOperators
open Classical

abbrev Triple := Σ _ : ℕ × ℕ, ℕ

def product (t : Triple) : ℕ := t.1.1 * t.1.2 * t.2

def pairSelector (N : ℕ) : Finset (ℕ × ℕ) :=
  chenY8PrimeSelector N ((N : ℝ) ^ (417 / 5000 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))

def quotientPrimeWindow (N : ℕ) (p : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun q => Nat.Prime q ∧ p.1 * p.2 * q < N ∧
    (p.2 : ℝ) ≤ (q : ℝ) ∧ Nat.Coprime (N - p.1 * p.2 * q) N

def arithmeticTriples (N : ℕ) : Finset Triple :=
  (pairSelector N).sigma (quotientPrimeWindow N)

theorem mem_arithmeticTriples_iff {N p1 p2 q : ℕ} :
    (⟨(p1,p2),q⟩ : Triple) ∈ arithmeticTriples N ↔
      (p1,p2) ∈ pairSelector N ∧ q < N + 1 ∧ Nat.Prime q ∧
        p1*p2*q < N ∧ (p2 : ℝ) ≤ (q : ℝ) ∧ Nat.Coprime (N-p1*p2*q) N := by
  simp only [arithmeticTriples, quotientPrimeWindow, Finset.mem_sigma,
    Finset.mem_filter, Finset.mem_range]

theorem arithmeticTriples_card_eq_sum (N : ℕ) :
    ((arithmeticTriples N).card : ℝ) =
      ∑ p ∈ pairSelector N, ((quotientPrimeWindow N p).card : ℝ) := by
  simp only [arithmeticTriples, Finset.card_sigma, Nat.cast_sum]

theorem arithmetic_data {N : ℕ} {t : Triple} (ht : t ∈ arithmeticTriples N) :
    t.1 ∈ pairSelector N ∧ t.2 < N+1 ∧ Nat.Prime t.2 ∧ product t < N ∧
      (t.1.2 : ℝ) ≤ (t.2 : ℝ) ∧ Nat.Coprime (N-product t) N := by
  rcases t with ⟨⟨p1,p2⟩,q⟩
  exact mem_arithmeticTriples_iff.mp ht

theorem arithmetic_product_lt {N : ℕ} {t : Triple} (ht : t ∈ arithmeticTriples N) :
    product t < N := (arithmetic_data ht).2.2.2.1

theorem pair_prime_data {N : ℕ} {p : ℕ × ℕ} (hp : p ∈ pairSelector N) :
    Nat.Prime p.1 ∧ Nat.Prime p.2 ∧ p.1 < p.2 ∧ p.1 < N ∧ p.2 < N := by
  obtain ⟨hc, _, hfirst, hsecond, _⟩ := Finset.mem_filter.mp hp
  obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
  have h12 : p.1 < p.2 := by exact_mod_cast hfirst.trans_le hsecond
  exact ⟨(mem_chenAdditivePrimeCarrier.mp h1).2.1,
    (mem_chenAdditivePrimeCarrier.mp h2).2.1,h12,
    (mem_chenAdditivePrimeCarrier.mp h1).1,(mem_chenAdditivePrimeCarrier.mp h2).1⟩

theorem arithmetic_sorted {N : ℕ} {t : Triple} (ht : t ∈ arithmeticTriples N) :
    t.1.1 < t.1.2 ∧ t.1.2 ≤ t.2 := by
  exact ⟨(pair_prime_data (arithmetic_data ht).1).2.2.1,
    by exact_mod_cast (arithmetic_data ht).2.2.2.2.1⟩

theorem arithmetic_product_coprime {N : ℕ} {t : Triple} (ht : t ∈ arithmeticTriples N) :
    Nat.Coprime (product t) N :=
  (Nat.coprime_self_sub_left (arithmetic_product_lt ht).le).mp
    (arithmetic_data ht).2.2.2.2.2

/-- Restoring only the additive-prime test recovers the actual U8 prime
triples, retaining equality q=p₂ and all original centre gates. -/
theorem arithmetic_filter_prime_eq (N : ℕ) :
    (arithmeticTriples N).filter (fun t => Nat.Prime (N-product t)) =
      currentChenUpsilon8PrimeTriples N := by
  ext t
  rcases t with ⟨⟨p1,p2⟩,q⟩
  rw [Finset.mem_filter, mem_arithmeticTriples_iff,
    mem_currentChenUpsilon8PrimeTriples_iff]
  constructor
  · rintro ⟨⟨hp,hqN,hq,hprod,hcut,hcop⟩,hPprime⟩
    obtain ⟨hc,hA,hfirst,hsecond,hcap⟩ := Finset.mem_filter.mp hp
    obtain ⟨h1,h2⟩ := Finset.mem_product.mp hc
    have hpos : 0 < p1*p2*q := mul_pos
      (mul_pos (mem_chenAdditivePrimeCarrier.mp h1).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp h2).2.1.pos) hq.pos
    have hP : N-p1*p2*q ∈ chenAdditivePrimeCarrier N :=
      mem_chenAdditivePrimeCarrier.mpr ⟨by omega,hPprime,hcop⟩
    exact ⟨h1,h2,hA,hfirst,hsecond,hcap,hq,hprod,hP,hcut⟩
  · rintro ⟨h1,h2,hA,hfirst,hsecond,hcap,hq,hprod,hP,hcut⟩
    have hp : (p1,p2) ∈ pairSelector N := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨h1,h2⟩,hA,hfirst,hsecond,hcap⟩
    have hqle : q ≤ p1*p2*q := Nat.le_mul_of_pos_left q
      (mul_pos (mem_chenAdditivePrimeCarrier.mp h1).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp h2).2.1.pos)
    exact ⟨⟨hp,by omega,hq,hprod,hcut,(mem_chenAdditivePrimeCarrier.mp hP).2.2⟩,
      (mem_chenAdditivePrimeCarrier.mp hP).2.1⟩

def productWeight (N m : ℕ) : ℝ :=
  (((arithmeticTriples N).filter (fun t => product t = m)).card : ℝ)

theorem productWeight_nonneg (N m : ℕ) : 0 ≤ productWeight N m := Nat.cast_nonneg _

theorem productWeight_eq_zero_of_not_lt {N m : ℕ} (hm : ¬ m < N) : productWeight N m = 0 := by
  have hempty : (arithmeticTriples N).filter (fun t => product t=m) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro t ht
    obtain ⟨ht,heq⟩ := Finset.mem_filter.mp ht
    exact hm (heq ▸ arithmetic_product_lt ht)
  simp only [productWeight,hempty,Finset.card_empty,Nat.cast_zero]

/-- Exact multiplicity Fubini for any signed product test. -/
theorem productWeight_sum (N : ℕ) (F : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, productWeight N m * F m) =
      ∑ t ∈ arithmeticTriples N, F (product t) := by
  have hf := Finset.sum_fiberwise_of_maps_to (s := arithmeticTriples N)
    (t := Finset.range N) (g := product)
    (fun t ht => Finset.mem_range.mpr (arithmetic_product_lt ht)) (fun t => F (product t))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m _
  change (((arithmeticTriples N).filter (fun t => product t=m)).card : ℝ)*F m = _
  calc
    _ = ∑ _t ∈ (arithmeticTriples N).filter (fun t => product t=m), F m := by simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [(Finset.mem_filter.mp ht).2]

theorem productWeight_mass_eq_card (N : ℕ) :
    p5z_labelledMass (Finset.range N) (productWeight N) = ((arithmeticTriples N).card : ℝ) := by
  simpa only [p5z_labelledMass,mul_one,Finset.sum_const,nsmul_eq_mul] using
    productWeight_sum N (fun _ => 1)

theorem currentChenUpsilon8_eq_primeMass_add_units (N : ℕ) :
    currentChenUpsilon8 N =
      p5z_labelledPrimeMass (Finset.range N) id (productWeight N) N +
        ((currentChenUpsilon8UnitFibres N).card : ℝ) := by
  have hp : p5z_labelledPrimeMass (Finset.range N) id (productWeight N) N =
      ((currentChenUpsilon8PrimeTriples N).card : ℝ) := by
    have h := productWeight_sum N (fun m => if m<N ∧ Nat.Prime (N-m) then 1 else 0)
    simp only [mul_ite,mul_one,mul_zero] at h
    have hgate : (arithmeticTriples N).filter (fun t => product t<N ∧ Nat.Prime (N-product t)) =
        currentChenUpsilon8PrimeTriples N := by
      rw [← arithmetic_filter_prime_eq]
      ext t
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ht,_,hp⟩; exact ⟨ht,hp⟩
      · rintro ⟨ht,hp⟩; exact ⟨ht,arithmetic_product_lt ht,hp⟩
    have hcount : (∑ t ∈ arithmeticTriples N,
        if product t<N ∧ Nat.Prime (N-product t) then (1 : ℝ) else 0) =
        ((currentChenUpsilon8PrimeTriples N).card : ℝ) := by
      rw [← Finset.sum_filter,hgate]
      simp
    simpa only [p5z_labelledPrimeMass,id_eq] using h.trans hcount
  rw [currentChenUpsilon8_eq_primeTriples_add_unitFibres,hp]

theorem productWeight_distribution_eq_labels (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (Finset.range N) id (productWeight N) N Q rho =
      p5z_labelledDistributionError (arithmeticTriples N) product (fun _ => 1) N Q rho := by
  have hcong : ∀ ell, p5z_labelledCongruenceMass (Finset.range N) id (productWeight N) N ell =
      p5z_labelledCongruenceMass (arithmeticTriples N) product (fun _ => 1) N ell := by
    intro ell
    simpa only [p5z_labelledCongruenceMass,id_eq,mul_ite,mul_one,mul_zero] using
      productWeight_sum N (fun m => if Nat.ModEq ell m N then 1 else 0)
  have hcop : ∀ ell, p5z_labelledCoprimeMass (Finset.range N) id (productWeight N) ell =
      p5z_labelledCoprimeMass (arithmeticTriples N) product (fun _ => 1) ell := by
    intro ell
    simpa only [p5z_labelledCoprimeMass,id_eq,mul_ite,mul_one,mul_zero] using
      productWeight_sum N (fun m => if Nat.Coprime m ell then 1 else 0)
  unfold p5z_labelledDistributionError
  simp_rw [hcong,hcop]

theorem same_rho_physical_sum_eq_main_errors (N : ℕ) (Q : Finset ℕ) (rho : ℕ → ℝ) :
    (∑ m ∈ Finset.range N, productWeight N m * physicalDivisorSum Q rho (N-m)) =
      p5z_labelledMass (Finset.range N) (productWeight N) * physicalDensitySum Q rho +
        p5z_labelledCoprimeCorrection (Finset.range N) id (productWeight N) Q rho +
        p5z_labelledDistributionError (Finset.range N) id (productWeight N) N Q rho :=
  p5z_labelled_physical_sum_eq_main_add_errors (Finset.range N) id (productWeight N)
    N Q rho (fun m hm => (Finset.mem_range.mp hm).le)

end ImbalancedChen.P5U8SharpKSource
