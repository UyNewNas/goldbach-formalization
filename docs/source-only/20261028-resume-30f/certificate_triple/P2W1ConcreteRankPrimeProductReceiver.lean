import ImbalancedChen.P2W1ActualPrefixFamilyBinding
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity
import ImbalancedChen.PrimeHistoryLogCoordinates

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual independent W1 arithmetic labels are encoded into the existing
Part3 prime-product source at each COMPLETE canonical rank. The old word,
three distinguished slots and every canonical tail prime remain visible.
The encoding into tuples is injective; the PRODUCT map need not be.
The exact signed PP discrepancy is identified, not estimated or licensed
by an assumption named PP/K. Geometric/group-capacity licences remain OPEN.
-/
namespace ImbalancedChen.P2W1ConcreteRankPrimeProductReceiver
noncomputable section
open scoped Classical BigOperators
open P2W1UnsiftedPrimeProductSource P2W1ActualCanonicalPrimeWord
open P2EnhancedW1OrderedPositiveTripleWord

def rankSource (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (rank : ℕ) : Finset Label :=
  (arithmeticLabels N Q old i j).filter (fun a => (primeWord old a).length=rank)

def rawTuple (old : List ℕ) (rank : ℕ) (a : Label) : Fin rank → ℕ :=
  primeHistoryTuple rank (primeWord old a).reverse

/-- Total finite tuple. The minimum is inactive on the genuine source;
no default or truncated prime occurs in any source theorem below. -/
def tuple (N : ℕ) (old : List ℕ) (rank : ℕ) (a : Label) : Fin rank → Fin (N+1) :=
  fun k => ⟨min N (rawTuple old rank a k),Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

def family (N : ℕ) (Q : ℝ) (old : List ℕ) (i : Fin 7) (j : Fin 10)
    (rank : ℕ) : Finset (Fin rank → Fin (N+1)) :=
  (rankSource N Q old i j rank).image (tuple N old rank)

theorem rankSource_data {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label}
    (ha : a ∈ rankSource N Q old i j rank) :
    Geometry N Q old i j a ∧ (primeWord old a).length=rank := by
  have hd := Finset.mem_filter.mp ha
  exact ⟨(Finset.mem_filter.mp hd.1).2,hd.2⟩

theorem rawTuple_mem {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label}
    (ha : a ∈ rankSource N Q old i j rank) (k : Fin rank) :
    rawTuple old rank a k ∈ primeWord old a := by
  have hlen : (primeWord old a).reverse.length=rank := by
    simpa only [List.length_reverse] using (rankSource_data ha).2
  exact List.mem_reverse.mp (primeHistoryTuple_mem hlen k)

theorem tuple_val {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label} (hB : 0<old.prod)
    (ha : a ∈ rankSource N Q old i j rank) (k : Fin rank) :
    (tuple N old rank a k).val=rawTuple old rank a k := by
  have hg := (rankSource_data ha).1
  have hp : 0<(primeWord old a).prod := by
    rw [primeWord_product hg]
    exact geometry_product_pos hB hg
  have hd : rawTuple old rank a k ∣ (primeWord old a).prod :=
    List.dvd_prod (rawTuple_mem ha k)
  have hc : rawTuple old rank a k≤N := by
    have hh := Nat.le_of_dvd hp hd
    rw [primeWord_product hg] at hh
    exact hh.trans hg.2.2.2.2.2.2.2.le
  exact Nat.min_eq_right hc

theorem tuple_word {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label} (hB : 0<old.prod)
    (ha : a ∈ rankSource N Q old i j rank) :
    List.ofFn (fun k => (tuple N old rank a k).val)=primeWord old a := by
  have heq : (fun k => (tuple N old rank a k).val)=rawTuple old rank a := by
    funext k
    exact tuple_val hB ha k
  rw [heq]
  have hlen : (primeWord old a).reverse.length=rank := by
    simpa only [List.length_reverse] using (rankSource_data ha).2
  simpa only [rawTuple,List.reverse_reverse] using primeHistoryTuple_ofFn hlen

/-- The tuple contains the three distinguished q slots before its exact
canonical tail. Hence even equal-product labels are not collapsed. -/
theorem primeWord_injective {N : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a b : Label}
    (ha : Geometry N Q old i j a) (hb : Geometry N Q old i j b)
    (h : primeWord old a=primeWord old b) : a=b := by
  have hs : [first a.1,middle a.1,last a.1]++a.2.primeFactorsList =
      [first b.1,middle b.1,last b.1]++b.2.primeFactorsList := by
    apply List.append_cancel_left
    simpa only [primeWord,List.append_assoc] using h
  simp only [List.cons_append,List.nil_append,List.cons.injEq] at hs
  obtain ⟨h1,h2,h3,htail⟩ := hs
  have hn := congrArg List.prod htail
  rw [Nat.prod_primeFactorsList ha.2.2.2.2.2.1.ne',
    Nat.prod_primeFactorsList hb.2.2.2.2.2.1.ne'] at hn
  apply Prod.ext
  · exact Prod.ext (Prod.ext h1 h2) h3
  · exact hn

theorem tuple_injective_on_source {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod) :
    Set.InjOn (tuple N old rank) (rankSource N Q old i j rank : Set Label) := by
  intro a ha b hb hab
  have hw := congrArg (fun t : Fin rank → Fin (N+1) => List.ofFn (fun k => (t k).val)) hab
  rw [tuple_word hB ha,tuple_word hB hb] at hw
  exact primeWord_injective (rankSource_data ha).1 (rankSource_data hb).1 hw

theorem tuple_product {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} {a : Label} (hB : 0<old.prod)
    (ha : a ∈ rankSource N Q old i j rank) :
    Part3.labelledProduct (tuple N old rank a)=product old a := by
  rw [Part3.labelledProduct,← List.prod_ofFn,tuple_word hB ha,
    primeWord_product (rankSource_data ha).1]

theorem family_prime {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hold : ∀ p ∈ old,Nat.Prime p) :
    family N Q old i j rank ⊆ Part3.labelledPrimeTuples rank N := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro k
  rw [tuple_val hB ha k]
  exact primeWord_primes hold (rankSource_data ha).1 _ (rawTuple_mem ha k)

theorem family_product_cap {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod) :
    ∀ t ∈ family N Q old i j rank,Part3.labelledProduct t<N := by
  intro t ht
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  rw [tuple_product hB ha]
  exact (rankSource_data ha).1.2.2.2.2.2.2.2

theorem family_fixed_power {N rank : ℕ} {Q eta : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hold : ∀ p ∈ old,(N : ℝ)^eta≤(p : ℝ))
    (hcut : (N : ℝ)^eta≤P2EnhancedTwentyOneSameQWeighted.cutoff Q old.prod
      (P5OriginalActionMassBound.W1Anchor j)) :
    ∀ t ∈ family N Q old i j rank,∀ k,(N : ℝ)^eta≤((t k).val : ℝ) := by
  intro t ht k
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  rw [tuple_val hB ha k]
  exact primeWord_fixed_power (rankSource_data ha).1 hold hcut _ (rawTuple_mem ha k)

/-- The actual PP weight is a constant marked weight on the concrete
tuple image, zero elsewhere. Its norm bound has no modulus argument. -/
theorem actualPPWeight_bound {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (sigma : ℝ) (hsigma : 0≤sigma)
    (t : Fin rank → Fin (N+1)) :
    0≤p5z_markedPhysicalWeight (family N Q old i j rank) (fun _ => sigma) t ∧
    p5z_markedPhysicalWeight (family N Q old i j rank) (fun _ => sigma) t≤sigma := by
  by_cases ht : t ∈ family N Q old i j rank
  · simp only [p5z_markedPhysicalWeight,if_pos ht]
    exact ⟨hsigma,le_rfl⟩
  · simp only [p5z_markedPhysicalWeight,if_neg ht]
    exact ⟨le_rfl,hsigma⟩

/-- Exact finite labelled test transport. The tuple injection was proved
from the actual old/q/tail slots, not assumed as a licence. -/
theorem family_test {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod) (sigma : ℝ) (G : ℕ → ℝ) :
    (∑ t ∈ family N Q old i j rank,sigma*G (Part3.labelledProduct t)) =
      ∑ a ∈ rankSource N Q old i j rank,sigma*G (product old a) := by
  unfold family
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro a ha
    rw [tuple_product hB ha]
  · exact tuple_injective_on_source hB

theorem rank_primeMass_eq_tuple {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod) (sigma : ℝ) :
    p5z_labelledPrimeMass (rankSource N Q old i j rank) (product old) (fun _ => sigma) N =
      p5z_labelledPrimeMass (family N Q old i j rank) Part3.labelledProduct (fun _ => sigma) N := by
  have h := family_test (N:=N) (rank:=rank) (Q:=Q) (i:=i) (j:=j) hB sigma
    (fun m => if m<N ∧ Nat.Prime (N-m) then 1 else 0)
  simpa only [p5z_labelledPrimeMass,mul_ite,mul_one,mul_zero] using h.symm

/-- The concrete original source discrepancy is precisely the original
Part3 PP discrepancy with a modulus-independent marked tuple weight.
No estimate for this discrepancy is an input or a conclusion here. -/
theorem rank_distribution_eq_actualPP {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hold : ∀ p ∈ old,Nat.Prime p) (sigma : ℝ) (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (rankSource N Q old i j rank) (product old)
      (fun _ => sigma) N D rho =
      Part3.primeProductSignedError rank N N D rho
        (p5z_markedPhysicalWeight (family N Q old i j rank) (fun _ => sigma)) := by
  rw [← p5z_markedDistribution_eq_physicalPP _ (family_prime hB hold) _ D rho]
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass
  apply Finset.sum_congr rfl
  intro d hd
  have hc := family_test (N:=N) (rank:=rank) (Q:=Q) (i:=i) (j:=j) hB sigma
    (fun m => if Nat.ModEq d m N then 1 else 0)
  have hp := family_test (N:=N) (rank:=rank) (Q:=Q) (i:=i) (j:=j) hB sigma
    (fun m => if Nat.Coprime m d then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at hc hp
  rw [hc,hp]

/-- Actual small-prime partners at this complete rank have the existing
finite payment, with all product collisions retained. -/
theorem rank_smallPrimeMass_le {N rank : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hold : ∀ p ∈ old,Nat.Prime p) (sigma : ℝ) (hsigma : 0≤sigma) (z : ℕ) :
    p5z_labelledSmallPrimeMass (rankSource N Q old i j rank) (product old)
      (fun _ => sigma) N z ≤ sigma*(rank^rank : ℕ)*(z : ℝ) := by
  have ht := family_test (N:=N) (rank:=rank) (Q:=Q) (i:=i) (j:=j) hB sigma
    (fun m => if m<N ∧ Nat.Prime (N-m) ∧ N-m<z then 1 else 0)
  have heq : p5z_labelledSmallPrimeMass (family N Q old i j rank)
      Part3.labelledProduct (fun _ => sigma) N z =
      p5z_labelledSmallPrimeMass (rankSource N Q old i j rank)
        (product old) (fun _ => sigma) N z := by
    simpa only [p5z_labelledSmallPrimeMass,mul_ite,mul_one,mul_zero] using ht
  rw [← heq]
  exact p5z_markedSmallPrimeMass_le _ (family_prime hB hold) _ sigma hsigma
    (fun _ _ => le_rfl) (fun t ht => (family_product_cap hB t ht).le) z

/-- Partition by the complete rank without deleting a rank, including
the exact rank of n=1. R bounds the actual source, not its image size. -/
theorem source_test_eq_rank_sum {N R : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10}
    (hR : ∀ a ∈ arithmeticLabels N Q old i j,(primeWord old a).length≤R)
    (sigma : ℝ) (G : ℕ → ℝ) :
    (∑ a ∈ arithmeticLabels N Q old i j,sigma*G (product old a)) =
      ∑ rank ∈ Finset.range (R+1),
        ∑ a ∈ rankSource N Q old i j rank,sigma*G (product old a) := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s:=arithmeticLabels N Q old i j) (t:=Finset.range (R+1))
    (g:=fun a => (primeWord old a).length)
    (fun a ha => Finset.mem_range.mpr (Nat.lt_succ_of_le (hR a ha)))
    (fun a => sigma*G (product old a))
  exact hf.symm

theorem source_primeMass_eq_rank_tuple_sum {N R : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hR : ∀ a ∈ arithmeticLabels N Q old i j,(primeWord old a).length≤R)
    (sigma : ℝ) :
    p5z_labelledPrimeMass (arithmeticLabels N Q old i j) (product old) (fun _ => sigma) N =
      ∑ rank ∈ Finset.range (R+1),
        p5z_labelledPrimeMass (family N Q old i j rank) Part3.labelledProduct
          (fun _ => sigma) N := by
  have ht := source_test_eq_rank_sum hR sigma
    (fun m => if m<N ∧ Nat.Prime (N-m) then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at ht
  change p5z_labelledPrimeMass _ _ _ N =
    ∑ rank ∈ Finset.range (R+1),p5z_labelledPrimeMass _ _ _ N at ht
  rw [ht]
  apply Finset.sum_congr rfl
  intro rank hrank
  exact rank_primeMass_eq_tuple hB sigma

/-- The original frozen-receiver W1 count is costed by the actual finite
rank tuple families. The receiver is dropped by positivity exactly once;
it is not folded into a purported geometrically licensed PP coefficient. -/
theorem actual_W1_count_le_rank_tuple_sum {N R : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hR : ∀ a ∈ arithmeticLabels N Q old i j,(primeWord old a).length≤R)
    (E : ℕ → ℕ → Prop) (sigma : ℝ) (hsigma : 0≤sigma) :
    sigma*(∑ ell ∈ Finset.range (N+1),
      ((positiveTripleWords N ell Q old i j E).card : ℝ)) ≤
      ∑ rank ∈ Finset.range (R+1),
        p5z_labelledPrimeMass (family N Q old i j rank) Part3.labelledProduct
          (fun _ => sigma) N := by
  rw [← source_primeMass_eq_rank_tuple_sum hB hR sigma]
  exact actual_switched_count_le_unmasked E sigma hB hsigma

/-- All actual additive-prime partners below z receive a finite bound.
The constant depends only on the preselected rank cap and sigma, with
no additive-prime deletion or pairwise product injectivity premise. -/
theorem source_smallPrimeMass_le {N R : ℕ} {Q : ℝ} {old : List ℕ}
    {i : Fin 7} {j : Fin 10} (hB : 0<old.prod)
    (hold : ∀ p ∈ old,Nat.Prime p)
    (hR : ∀ a ∈ arithmeticLabels N Q old i j,(primeWord old a).length≤R)
    (sigma : ℝ) (hsigma : 0≤sigma) (z : ℕ) :
    p5z_labelledSmallPrimeMass (arithmeticLabels N Q old i j) (product old)
      (fun _ => sigma) N z ≤
      ∑ rank ∈ Finset.range (R+1),sigma*(rank^rank : ℕ)*(z : ℝ) := by
  have ht := source_test_eq_rank_sum hR sigma
    (fun m => if m<N ∧ Nat.Prime (N-m) ∧ N-m<z then 1 else 0)
  simp only [mul_ite,mul_one,mul_zero] at ht
  change p5z_labelledSmallPrimeMass _ _ _ N z =
    ∑ rank ∈ Finset.range (R+1),p5z_labelledSmallPrimeMass _ _ _ N z at ht
  rw [ht]
  exact Finset.sum_le_sum (fun rank hrank => rank_smallPrimeMass_le hB hold sigma hsigma z)

end
end ImbalancedChen.P2W1ConcreteRankPrimeProductReceiver
