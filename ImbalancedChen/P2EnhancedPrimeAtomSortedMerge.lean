import ImbalancedChen.P2EnhancedSelectedSortedDwellMerge
import ImbalancedChen.ActualPrimeSlotSquarefreeSymmetry

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Arithmetic binding of the sorted merge to the ACTUAL decreasing prime
factor vector of B*d. Coprimality with the old squarefree prefix excludes
every selected old prime from the residual atom. The merged product is
squarefree, the vector is strictly decreasing, and the original selected
list and every selected remaining-square test are retained on that actual
primeFactorsList.reverse vector at total Q and level Q/A.

Existing unique factorization and prime-vector squarefree/nodup results
are reused. Residual well support is primitive atom support at Q/B;
no signed AP or K estimate is inferred from this geometry.
-/

namespace ImbalancedChen.P2EnhancedPrimeAtomSortedMerge

noncomputable section

open P2EnhancedSortedDwellMerge P2EnhancedSelectedSortedDwellMerge
open scoped Classical

theorem sortedUnion_primes (old residual : List ℕ)
    (hold : ∀ p ∈ old, p.Prime) (hres : ∀ p ∈ residual, p.Prime) :
    ∀ p ∈ sortedUnion old residual, p.Prime := by
  intro p hp
  rcases List.mem_append.mp ((sortedUnion_perm old residual).mem_iff.mp hp) with hp | hp
  · exact hold p hp
  · exact hres p hp

/-- Whole-product coprimality excludes the actual selected old labels;
this is derived rather than assumed as a new residual-label licence. -/
theorem residual_avoids_selected {B d : ℕ} (old residual : List ℕ) (S : ℕ → Prop)
    (hB : old.prod = B) (hd : residual.prod = d) (hcop : B.Coprime d)
    (hresPrime : ∀ p ∈ residual, p.Prime) (hselected : ∀ p, S p → p ∈ old) :
    ∀ p ∈ residual, ¬ S p := by
  intro p hp hS
  have hpB : p ∣ B := hB ▸ List.dvd_prod (hselected p hS)
  have hpd : p ∣ d := hd ▸ List.dvd_prod hp
  have hpone : p ∣ 1 := by
    simpa only [hcop.gcd_eq_one] using Nat.dvd_gcd hpB hpd
  exact (hresPrime p hp).not_dvd_one hpone

/-- The original selected product remains a literal divisor of B. -/
theorem selected_product_dvd {B : ℕ} (old : List ℕ) (S : ℕ → Prop) (hB : old.prod = B) :
    (selected old S).prod ∣ B := by
  rw [← hB, ← selected_mul_remaining old S]
  exact dvd_mul_right _ _

/-- The canonical sorted union is the actual decreasing factor vector,
not a replacement factorization with the same product. -/
theorem sortedUnion_eq_primeFactors {B d : ℕ} (old residual : List ℕ)
    (hB : old.prod = B) (hd : residual.prod = d) (hB0 : B ≠ 0) (hd0 : d ≠ 0)
    (holdPrime : ∀ p ∈ old, p.Prime) (hresPrime : ∀ p ∈ residual, p.Prime) :
    sortedUnion old residual = (B * d).primeFactorsList.reverse := by
  have hprime := sortedUnion_primes old residual holdPrime hresPrime
  have hcanonical : ∀ p ∈ (B * d).primeFactorsList.reverse, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactorsList (List.mem_reverse.mp hp)
  have hprod : (sortedUnion old residual).prod = ((B * d).primeFactorsList.reverse).prod := by
    rw [sortedUnion_product, hB, hd, List.prod_reverse,
      Nat.prod_primeFactorsList (mul_ne_zero hB0 hd0)]
  have hperm := (Nat.primeFactorsList_unique hprod hprime).trans
    (Nat.primeFactorsList_unique
      (rfl : ((B * d).primeFactorsList.reverse).prod = ((B * d).primeFactorsList.reverse).prod)
      hcanonical).symm
  exact hperm.eq_of_pairwise' (sortedUnion_sorted old residual)
    (Nat.primeFactorsList_sorted (B * d)).reverse.pairwise

theorem sortedUnion_squarefree {B d : ℕ} (old residual : List ℕ)
    (hB : old.prod = B) (hd : residual.prod = d)
    (hBsf : Squarefree B) (hdsf : Squarefree d) (hcop : B.Coprime d) :
    Squarefree (sortedUnion old residual).prod := by
  rw [sortedUnion_product, hB, hd]
  exact (Nat.squarefree_mul hcop).mpr ⟨hBsf, hdsf⟩

/-- Distinct actual merged prime factors are strictly decreasing. -/
theorem sortedUnion_strict {B d : ℕ} (old residual : List ℕ)
    (hB : old.prod = B) (hd : residual.prod = d)
    (hBsf : Squarefree B) (hdsf : Squarefree d) (hcop : B.Coprime d)
    (holdPrime : ∀ p ∈ old, p.Prime) (hresPrime : ∀ p ∈ residual, p.Prime) :
    (sortedUnion old residual).Pairwise (· > ·) := by
  have hprime := sortedUnion_primes old residual holdPrime hresPrime
  have hsf := sortedUnion_squarefree old residual hB hd hBsf hdsf hcop
  have hnodup := actualPrimeVector_nodup_of_squarefree (sortedUnion old residual) hprime hsf
  have hsort := sortedUnion_sorted old residual
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hle := (List.pairwise_iff_getElem.mp hsort) i j hi hj hij
  have hne := (List.pairwise_iff_getElem.mp hnodup) i j hi hj hij
  omega

/-- Actual old squarefree prefix and coprime residual atom, retaining all
original selected labels and every full/selected square gate at the SAME Q. -/
theorem prime_atom_full_and_selected {Q : ℝ} {B d : ℕ}
    (old residual : List ℕ) (S : ℕ → Prop)
    (hB : old.prod = B) (hd : residual.prod = d)
    (hBsf : Squarefree B) (hdsf : Squarefree d) (hcop : B.Coprime d)
    (holdPrime : ∀ p ∈ old, p.Prime) (hresPrime : ∀ p ∈ residual, p.Prime)
    (holdSort : old.Pairwise (· ≥ ·)) (holdWell : actualDwellSupport Q old)
    (hgates : RemainingSquares Q old S)
    (hselected : ∀ p, S p → p ∈ old)
    (hresWell : actualDwellSupport (Q / (B : ℝ)) residual) :
    actualDwellSupport Q ((B * d).primeFactorsList.reverse) ∧
      Squarefree (B * d) ∧ ((B * d).primeFactorsList.reverse).Pairwise (· > ·) ∧
      selected ((B * d).primeFactorsList.reverse) S = selected old S ∧
      actualDwellSupport (Q / ((selected old S).prod : ℝ))
        (remaining ((B * d).primeFactorsList.reverse) S) ∧
      (remaining ((B * d).primeFactorsList.reverse) S).prod = (remaining old S).prod * d := by
  have holdOne : ∀ p ∈ old, 1 ≤ p := fun p hp => (holdPrime p hp).one_lt.le
  have hresOne : ∀ p ∈ residual, 1 ≤ p := fun p hp => (hresPrime p hp).one_lt.le
  have holdProd : 0 < old.prod := by rw [hB]; exact Nat.pos_of_ne_zero hBsf.ne_zero
  have hres : actualDwellSupport (Q / (old.prod : ℝ)) residual := by
    simpa only [hB] using hresWell
  have hno := residual_avoids_selected old residual S hB hd hcop hresPrime hselected
  have hfull := full_and_selected_sortedUnion old residual S holdProd holdWell holdSort holdOne
    hgates hres hresOne hno
  have heq := sortedUnion_eq_primeFactors old residual hB hd hBsf.ne_zero hdsf.ne_zero
    holdPrime hresPrime
  have hstrict := sortedUnion_strict old residual hB hd hBsf hdsf hcop holdPrime hresPrime
  rw [heq] at hfull hstrict
  exact ⟨hfull.1, (Nat.squarefree_mul hcop).mpr ⟨hBsf, hdsf⟩, hstrict,
    hfull.2.1, hfull.2.2.1, by simpa only [hd] using hfull.2.2.2⟩

end
end ImbalancedChen.P2EnhancedPrimeAtomSortedMerge
