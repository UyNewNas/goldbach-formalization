import ImbalancedChen.P2Selected430ActualW1SourceCoverage
import ImbalancedChen.P5zPositiveFamilyBudget
import ImbalancedChen.P5OriginalCommonRefinedConstructor

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The earlier positiveTripleWords already tests primality of its additive
receiver ell. It is NOT the unsifted mass X_W in the positive-K theorem.
Here the independent arithmetic labels are (q1,q2,q3,n), with the original
same-Q window, coprimality, strict q ordering, rough tail and product bound.
There is no additive-prime test and no PP-modulus argument in this family.
Primality of N-m and the frozen receiver are restored separately below.

The actual common-refined policy8 rho is used without replacement in the
finite physical identity. No PP, currentK density, source-mass asymptotic,
positive-K bound or arbitrary family licence is assumed or concluded.
-/
namespace ImbalancedChen.P2W1UnsiftedPrimeProductSource
noncomputable section
open Finset Set
open scoped Classical BigOperators
open P2EnhancedW1OrderedPositiveTripleWord
open P2EnhancedW1R2ActualCarrierBranch (eligiblePrimes eligiblePrime_data)
open P2EnhancedW1FinitePrimeOwnership (activePrimes)
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2LargerSActualPositiveCounts (historyCarrier)
open P5OriginalActionMassBound (W1Target W1Anchor)

abbrev Label := TripleLabel × ℕ

def product (old : List ℕ) (a : Label) : ℕ := old.prod * tripleProduct a.1 * a.2

def primeWindow (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) (p : ℕ) : Prop :=
  p.Prime ∧ cutoff Q old.prod (W1Anchor j) ≤ (p : ℝ) ∧
    (p : ℝ) < cutoff Q old.prod (W1Target i) ∧ p.Coprime (old.prod*N)

def Geometry (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) (a : Label) : Prop :=
  primeWindow N Q old i j (first a.1) ∧
  primeWindow N Q old i j (middle a.1) ∧
  primeWindow N Q old i j (last a.1) ∧
  first a.1 < middle a.1 ∧ middle a.1 < last a.1 ∧
  0 < a.2 ∧ roughTail a.2 (middle a.1) ∧ product old a < N

def ambient (N : ℕ) : Finset Label :=
  (((Finset.range (N+1)).product (Finset.range (N+1))).product
    (Finset.range (N+1))).product (Finset.range (N+1))

def arithmeticLabels (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10) : Finset Label :=
  (ambient N).filter (Geometry N Q old i j)

/-- The old receiver/history predicate is explicit in the weight. Its
actual geometric licensing is not inferred for an arbitrary E. The D
source-prefix theorem supplies its exact frozen interpretation. -/
def frozenWeight (N : ℕ) (old : List ℕ) (E : ℕ → ℕ → Prop) (sigma : ℝ) (a : Label) : ℝ :=
  if E old.prod (N-product old a) then sigma else 0

theorem geometry_product_pos {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (hB : 0 < old.prod) (h : Geometry N Q old i j a) : 0 < product old a := by
  exact mul_pos (mul_pos hB (mul_pos (mul_pos h.1.1.pos h.2.1.1.pos) h.2.2.1.1.pos)) h.2.2.2.2.2.1

private theorem geometry_ambient {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (hB : 0 < old.prod) (h : Geometry N Q old i j a) : a ∈ ambient N := by
  have hp := geometry_product_pos hB h
  have hcap := h.2.2.2.2.2.2.2
  have hfirst : first a.1 ∣ product old a := by
    refine ⟨old.prod*middle a.1*last a.1*a.2,?_⟩
    dsimp [product,tripleProduct]
    ring
  have hmiddle : middle a.1 ∣ product old a := by
    refine ⟨old.prod*first a.1*last a.1*a.2,?_⟩
    dsimp [product,tripleProduct]
    ring
  have hlast : last a.1 ∣ product old a := by
    refine ⟨old.prod*first a.1*middle a.1*a.2,?_⟩
    dsimp [product,tripleProduct]
    ring
  have hn : a.2 ∣ product old a := by exact dvd_mul_left _ _
  have h1 := (Nat.le_of_dvd hp hfirst).trans hcap.le
  have h2 := (Nat.le_of_dvd hp hmiddle).trans hcap.le
  have h3 := (Nat.le_of_dvd hp hlast).trans hcap.le
  have h4 := (Nat.le_of_dvd hp hn).trans hcap.le
  exact Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega),Finset.mem_range.mpr (by omega)⟩,
      Finset.mem_range.mpr (by omega)⟩,Finset.mem_range.mpr (by omega)⟩

theorem mem_arithmeticLabels {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (hB : 0 < old.prod) :
    a ∈ arithmeticLabels N Q old i j ↔ Geometry N Q old i j a := by
  exact ⟨fun h => (Finset.mem_filter.mp h).2,
    fun h => Finset.mem_filter.mpr ⟨geometry_ambient hB h,h⟩⟩

/-- A source triple is embedded with its EXACT integer quotient tail,
retaining the receiver through m=N-ell and every original triple label. -/
theorem source_to_arithmetic {N ell : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {t : TripleLabel} (hB : 0 < old.prod)
    (ht : t ∈ positiveTripleWords N ell Q old i j E) :
    (t,tail N ell old t) ∈ arithmeticLabels N Q old i j ∧
    product old (t,tail N ell old t) = N-ell ∧
    Nat.Prime (N-product old (t,tail N ell old t)) ∧
    E old.prod (N-product old (t,tail N ell old t)) := by
  have hd := positiveTripleWords_data ht
  have hp1 := eligiblePrime_data hd.1
  have hp2 := eligiblePrime_data hd.2.1
  have hp3 := eligiblePrime_data hd.2.2.1
  have hell := hd.2.2.2.1
  obtain ⟨hcarrier,hE⟩ := Finset.mem_filter.mp hell
  obtain ⟨hrange,hprime,hdiv,hsift⟩ := Finset.mem_filter.mp hcarrier
  have hlt : ell < N := hd.2.2.2.2.1
  have hprod : product old (t,tail N ell old t) = N-ell := positiveTripleWords_physical_product ht
  have hn : 0 < tail N ell old t := by
    have hpos : 0 < N-ell := Nat.sub_pos_of_lt hlt
    by_contra hn
    have hz : tail N ell old t = 0 := by omega
    rw [← hprod,hz] at hpos
    simp [product] at hpos
  have hprodlt : product old (t,tail N ell old t) < N := by
    rw [hprod]
    exact Nat.sub_lt (by omega) hprime.pos
  have hgeom : Geometry N Q old i j (t,tail N ell old t) :=
    ⟨⟨hp1.1,hp1.2.2.1,hp1.2.2.2.1,hp1.2.2.2.2⟩,
     ⟨hp2.1,hp2.2.2.1,hp2.2.2.2.1,hp2.2.2.2.2⟩,
     ⟨hp3.1,hp3.2.2.1,hp3.2.2.2.1,hp3.2.2.2.2⟩,
     hd.2.2.2.2.2.1,hd.2.2.2.2.2.2.1,hn,hd.2.2.2.2.2.2.2.2,hprodlt⟩
  have hrecover : N-product old (t,tail N ell old t) = ell := by rw [hprod]; omega
  refine ⟨(mem_arithmeticLabels hB).mpr hgeom,hprod,?_,?_⟩
  · simpa only [hrecover] using hprime
  · simpa only [hrecover] using hE

/-- Whole residual roughness, derived from the three prime windows and
actual rough tail. It implies the old-mask sifted quotient without any
new coprime-mean or additive-prime assumption. -/
private theorem geometry_sift {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {a : Label} (h : Geometry N Q old i j a) :
    ∀ r : ℕ, r.Prime → (r : ℝ) < cutoff Q old.prod (W1Anchor j) →
      ¬ r ∣ tripleProduct a.1*a.2 := by
  intro r hr hrz hd
  rcases hr.dvd_mul.mp hd with hq | hn
  · change r ∣ first a.1*middle a.1*last a.1 at hq
    rcases hr.dvd_mul.mp hq with h12 | h3
    · rcases hr.dvd_mul.mp h12 with h1 | h2
      · have heq := (Nat.prime_dvd_prime_iff_eq hr h.1.1).mp h1
        subst r
        exact (not_lt_of_ge h.1.2.1) hrz
      · have heq := (Nat.prime_dvd_prime_iff_eq hr h.2.1.1).mp h2
        subst r
        exact (not_lt_of_ge h.2.1.2.1) hrz
    · have heq := (Nat.prime_dvd_prime_iff_eq hr h.2.2.1.1).mp h3
      subst r
      exact (not_lt_of_ge h.2.2.1.2.1) hrz
  · have hrge : middle a.1 ≤ r := h.2.2.2.2.2.2.1 r hr hn
    have hre : (middle a.1 : ℝ) ≤ r := by exact_mod_cast hrge
    exact (not_lt_of_ge (h.2.1.2.1.trans hre)) hrz

/-- Restoring ONLY the actual additive-prime test and old frozen receiver
recovers a literal positiveTripleWords member with the same exact tail. -/
theorem arithmetic_to_source {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    {E : ℕ → ℕ → Prop} {a : Label} (hB : 0 < old.prod)
    (ha : a ∈ arithmeticLabels N Q old i j)
    (hprime : Nat.Prime (N-product old a))
    (hE : E old.prod (N-product old a)) :
    a.1 ∈ positiveTripleWords N (N-product old a) Q old i j E ∧
    tail N (N-product old a) old a.1 = a.2 := by
  have hg := (mem_arithmeticLabels hB).mp ha
  have hpos := geometry_product_pos hB hg
  have hlt := hg.2.2.2.2.2.2.2
  have hsub : N-(N-product old a) = product old a := Nat.sub_sub_self hlt.le
  have hquot : oldQuotient N (N-product old a) old = tripleProduct a.1*a.2 := by
    unfold oldQuotient
    rw [hsub]
    simpa only [product,Nat.mul_assoc] using Nat.mul_div_cancel_left (tripleProduct a.1*a.2) hB
  have hqpos : 0 < tripleProduct a.1 :=
    mul_pos (mul_pos hg.1.1.pos hg.2.1.1.pos) hg.2.2.1.1.pos
  have htail : tail N (N-product old a) old a.1 = a.2 := by
    unfold tail
    rw [hquot]
    exact Nat.mul_div_cancel_left a.2 hqpos
  have hel : N-product old a < N := Nat.sub_lt (by omega) hpos
  have hdivB : old.prod ∣ N-(N-product old a) := by
    rw [hsub]
    exact ⟨tripleProduct a.1*a.2,by dsimp [product]; ring⟩
  have hhistory : N-product old a ∈ historyCarrier N old.prod E
      (cutoff Q old.prod (W1Anchor j)) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,hprime,hdivB,?_⟩,hE⟩
    · simp only [Finset.mem_range]
      omega
    · intro r hr hmask hrz hrdiv
      exact geometry_sift hg r hr hrz (by simpa only [oldQuotient] using (hquot ▸ hrdiv))
  have he (p : ℕ) (hp : primeWindow N Q old i j p) (hpd : p ∣ tripleProduct a.1*a.2) :
      p ∈ eligiblePrimes N (N-product old a) Q old i j := by
    unfold eligiblePrimes activePrimes
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Nat.mem_primeFactors.mpr ⟨hp.1,?_,?_⟩,hp.2.1,hp.2.2.1⟩,hp.2.2.2⟩
    · simpa only [oldQuotient] using (hquot.symm ▸ hpd)
    · have hnpos : 0 < tripleProduct a.1*a.2 := mul_pos hqpos hg.2.2.2.2.2.1
      change oldQuotient N (N-product old a) old ≠ 0
      rw [hquot]
      exact hnpos.ne'
  have h1 : first a.1 ∈ eligiblePrimes N (N-product old a) Q old i j :=
    he _ hg.1 ⟨middle a.1*last a.1*a.2,by dsimp [tripleProduct]; ring⟩
  have h2 : middle a.1 ∈ eligiblePrimes N (N-product old a) Q old i j :=
    he _ hg.2.1 ⟨first a.1*last a.1*a.2,by dsimp [tripleProduct]; ring⟩
  have h3 : last a.1 ∈ eligiblePrimes N (N-product old a) Q old i j :=
    he _ hg.2.2.1 ⟨first a.1*middle a.1*a.2,by dsimp [tripleProduct]; ring⟩
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_product.mpr ⟨h1,h2⟩,h3⟩,hhistory,hel,
    hg.2.2.2.1,hg.2.2.2.2.1,?_,?_⟩,htail⟩
  · rw [hquot]
    exact dvd_mul_right _ _
  · rw [htail]
    exact hg.2.2.2.2.2.2.1


/-- Additive-prime/receiver restoration is kept as a separate filter. -/
def restoredLabels (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (E : ℕ → ℕ → Prop) : Finset Label :=
  (arithmeticLabels N Q old i j).filter
    (fun a => Nat.Prime (N-product old a) ∧ E old.prod (N-product old a))

abbrev SourceLabel := Sigma (fun _ell : ℕ => TripleLabel)

def sourceLabels (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (E : ℕ → ℕ → Prop) : Finset SourceLabel :=
  (Finset.range (N+1)).sigma (fun ell => positiveTripleWords N ell Q old i j E)

def encodeSource (N : ℕ) (old : List ℕ) (a : SourceLabel) : Label :=
  (a.2,tail N a.1 old a.2)

/-- Exact finite cardinal transport: no product-map injection is used.
The additive receiver is recovered by ell=N-m and q1/q2/q3 remain labels. -/
theorem sourceLabels_card {N : ℕ} {Q : ℝ} {old : List ℕ} {i : Fin 7} {j : Fin 10}
    (E : ℕ → ℕ → Prop) (hB : 0 < old.prod) :
    (sourceLabels N Q old i j E).card = (restoredLabels N Q old i j E).card := by
  refine Finset.card_bij (fun a _ => encodeSource N old a) ?_ ?_ ?_
  · intro a ha
    have ht := (Finset.mem_sigma.mp ha).2
    obtain ⟨har,hprod,hprime,hE⟩ := source_to_arithmetic hB ht
    exact Finset.mem_filter.mpr ⟨har,hprime,hE⟩
  · intro a ha b hb hab
    rcases a with ⟨ell,t⟩
    rcases b with ⟨ell',t'⟩
    have hta := (Finset.mem_sigma.mp ha).2
    have htb := (Finset.mem_sigma.mp hb).2
    have ht : t=t' := congrArg Prod.fst hab
    have hm := congrArg (product old) hab
    have hma := (source_to_arithmetic hB hta).2.1
    have hmb := (source_to_arithmetic hB htb).2.1
    change product old (t,tail N ell old t) =
      product old (t',tail N ell' old t') at hm
    rw [hma,hmb] at hm
    have hell := (positiveTripleWords_data hta).2.2.2.2.1
    have hell' := (positiveTripleWords_data htb).2.2.2.2.1
    have heq : ell=ell' := by omega
    subst ell'
    subst t'
    rfl
  · intro a ha
    obtain ⟨har,hprime,hE⟩ := Finset.mem_filter.mp ha
    obtain ⟨ht,htail⟩ := arithmetic_to_source hB har hprime hE
    have hg := (mem_arithmeticLabels hB).mp har
    have hp := geometry_product_pos hB hg
    have hlt := hg.2.2.2.2.2.2.2
    refine ⟨⟨N-product old a,a.1⟩,?_,?_⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr (by omega),ht⟩
    · exact Prod.ext rfl htail

theorem labelledPrimeMass_eq_restored (N : ℕ) (Q : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) (sigma : ℝ) :
    p5z_labelledPrimeMass (arithmeticLabels N Q old i j) (product old)
      (frozenWeight N old E sigma) N =
        sigma * ((restoredLabels N Q old i j E).card : ℝ) := by
  have hsum : p5z_labelledPrimeMass (arithmeticLabels N Q old i j) (product old)
      (frozenWeight N old E sigma) N =
      ∑ _a ∈ restoredLabels N Q old i j E, sigma := by
    unfold p5z_labelledPrimeMass restoredLabels
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a ha
    have hlt := (Finset.mem_filter.mp ha).2.2.2.2.2.2.2.2
    by_cases hp : Nat.Prime (N-product old a)
    · by_cases hE : E old.prod (N-product old a)
      · simp only [frozenWeight,if_pos hE,if_pos ⟨hlt,hp⟩,if_pos ⟨hp,hE⟩]
      · simp only [frozenWeight,if_neg hE,if_pos ⟨hlt,hp⟩,
          if_neg (show ¬(Nat.Prime (N-product old a) ∧ E old.prod (N-product old a))
            from fun h => hE h.2)]
    · simp only [if_neg (show ¬(product old a<N ∧ Nat.Prime (N-product old a))
          from fun h => hp h.2),
        if_neg (show ¬(Nat.Prime (N-product old a) ∧ E old.prod (N-product old a))
          from fun h => hp h.1)]
  rw [hsum]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

/-- The actual W1 positive switched count equals the prime count on the
independent unsifted family. n=1 and all ordered label multiplicities stay. -/
theorem actual_switched_count_eq_labelledPrimeMass {N : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (E : ℕ → ℕ → Prop) (sigma : ℝ) (hB : 0 < old.prod) :
    sigma * (∑ ell ∈ Finset.range (N+1),
      ((positiveTripleWords N ell Q old i j E).card : ℝ)) =
    p5z_labelledPrimeMass (arithmeticLabels N Q old i j) (product old)
      (frozenWeight N old E sigma) N := by
  have hcard := sourceLabels_card (N:=N) (Q:=Q) (i:=i) (j:=j) E hB
  rw [labelledPrimeMass_eq_restored,← hcard]
  simp only [sourceLabels,Finset.card_sigma,Nat.cast_sum]

/-- Positivity permits dropping the genuine frozen receiver for costing.
The unsifted source then has the constant old marked weight sigma; its
weight cannot conceal an additive-prime or congruence-modulus condition. -/
theorem actual_switched_count_le_unmasked {N : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (E : ℕ → ℕ → Prop) (sigma : ℝ)
    (hB : 0 < old.prod) (hsigma : 0 ≤ sigma) :
    sigma * (∑ ell ∈ Finset.range (N+1),
      ((positiveTripleWords N ell Q old i j E).card : ℝ)) ≤
    p5z_labelledPrimeMass (arithmeticLabels N Q old i j) (product old)
      (fun _ => sigma) N := by
  rw [actual_switched_count_eq_labelledPrimeMass E sigma hB]
  unfold p5z_labelledPrimeMass
  apply Finset.sum_le_sum
  intro a ha
  by_cases hp : product old a<N ∧ Nat.Prime (N-product old a)
  · simp only [if_pos hp]
    by_cases hE : E old.prod (N-product old a)
    · simp only [frozenWeight,if_pos hE,le_refl]
    · simpa only [frozenWeight,if_neg hE] using hsigma
  · simp only [if_neg hp,le_refl]

/-- The actual independent source (not an arbitrary positive family)
feeds exactly the SAME common-refined policy8 coefficient in count,
density, primitive AP discrepancy and exact coprime correction. -/
theorem actual_common_rho_finite_identity
    (d : P5OriginalCommonRefinedConstructor.OriginalData)
    (N enumerationCap : ℕ) (Q w z L : ℝ) (old : List ℕ)
    (i : Fin 7) (j : Fin 10) (E : ℕ → ℕ → Prop) (sigma : ℝ) :
    (∑ a ∈ arithmeticLabels N Q old i j,
      frozenWeight N old E sigma a *
      physicalDivisorSum (P5OriginalCommonRefinedConstructor.moduli d N enumerationCap w z)
        (P5OriginalCommonRefinedConstructor.rho d N enumerationCap w z L)
        (N-product old a)) =
    p5z_labelledMass (arithmeticLabels N Q old i j) (frozenWeight N old E sigma) *
      physicalDensitySum (P5OriginalCommonRefinedConstructor.moduli d N enumerationCap w z)
        (P5OriginalCommonRefinedConstructor.rho d N enumerationCap w z L) +
    p5z_labelledCoprimeCorrection (arithmeticLabels N Q old i j) (product old)
      (frozenWeight N old E sigma)
      (P5OriginalCommonRefinedConstructor.moduli d N enumerationCap w z)
      (P5OriginalCommonRefinedConstructor.rho d N enumerationCap w z L) +
    p5z_labelledDistributionError (arithmeticLabels N Q old i j) (product old)
      (frozenWeight N old E sigma) N
      (P5OriginalCommonRefinedConstructor.moduli d N enumerationCap w z)
      (P5OriginalCommonRefinedConstructor.rho d N enumerationCap w z L) := by
  apply p5z_labelled_physical_sum_eq_main_add_errors
  intro a ha
  exact ((Finset.mem_filter.mp ha).2.2.2.2.2.2.2.2).le

end
end ImbalancedChen.P2W1UnsiftedPrimeProductSource
