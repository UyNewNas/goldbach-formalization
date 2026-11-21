import ImbalancedChen.P2NativeOmega3ExpandedPrimeWords
import ImbalancedChen.P5zMarkedPrimeFamilyMultiplicity

/-!
SOURCE ONLY / UNCOMPILED.

Each independent native label is encoded as its complete prime tuple:
the ordered old window tuple, p1,p2,p3, then the canonical tail factors.
Tuple encoding is injective; multiplication need not be. Unit weights
therefore retain every original convolution representation exactly.

The final dictionary covers every fixed k,delta using a derived finite
rank cap, with one threshold before N,i,Delta,V. indexedWeight is a concrete
argument for the existing UniformPrimeProductTarget, not an assertion of
that target, geometric admission, density, K1, or an H247 endpoint.
-/
namespace ImbalancedChen.P2NativeOmega3RankTupleReceiver

noncomputable section
open Finset Real Wu2008DoubleSieve
open P2NativeOmega3PrimeOutputFamily P2NativeOmega3ExpandedPrimeWords
open scoped Classical BigOperators

def rankLabels {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) (r : ℕ) :
    Finset (ExpandedLabel i) :=
  (expandedLabels N δ s t W).filter (fun a => (primeWord a).length=r)

def rawTuple {i : ℕ} (r : ℕ) (a : ExpandedLabel i) : Fin r → ℕ :=
  primeHistoryTuple r (primeWord a).reverse

def tuple {i : ℕ} (N r : ℕ) (a : ExpandedLabel i) : Fin r → Fin (N+1) :=
  fun j => ⟨min N (rawTuple r a j),Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩

def family {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) (r : ℕ) :
    Finset (Fin r → Fin (N+1)) :=
  (rankLabels N δ s t W r).image (tuple N r)

theorem rank_data {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (ha : a ∈ rankLabels N δ s t W r) :
    a ∈ expandedLabels N δ s t W ∧ (primeWord a).length=r := mem_filter.mp ha

theorem rawTuple_mem {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (ha : a ∈ rankLabels N δ s t W r) (j : Fin r) :
    rawTuple r a j ∈ primeWord a := by
  have hlen : (primeWord a).reverse.length=r := by
    simpa only [List.length_reverse] using (rank_data ha).2
  exact List.mem_reverse.mp (primeHistoryTuple_mem hlen j)

theorem tuple_val {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (hW : ∀ j p, p ∈ W j → p.Prime)
    (ha : a ∈ rankLabels N δ s t W r) (j : Fin r) :
    (tuple N r a j).val=rawTuple r a j := by
  have hsrc := (rank_data ha).1
  have hp : 0 < (primeWord a).prod :=
    List.prod_pos (fun p hp => (word_primes hW hsrc p hp).pos)
  have hd : rawTuple r a j ∣ (primeWord a).prod := List.dvd_prod (rawTuple_mem ha j)
  have hcap : rawTuple r a j ≤ N := by
    have hh := Nat.le_of_dvd hp hd
    rw [word_product hsrc] at hh
    exact hh.trans (source_product_le (expanded_data hsrc).2)
  exact Nat.min_eq_right hcap

theorem tuple_word {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (hW : ∀ j p, p ∈ W j → p.Prime)
    (ha : a ∈ rankLabels N δ s t W r) :
    List.ofFn (fun j => (tuple N r a j).val)=primeWord a := by
  have heq : (fun j => (tuple N r a j).val)=rawTuple r a := by
    funext j
    exact tuple_val hW ha j
  rw [heq]
  have hlen : (primeWord a).reverse.length=r := by
    simpa only [List.length_reverse] using (rank_data ha).2
  simpa only [rawTuple,List.reverse_reverse] using primeHistoryTuple_ofFn hlen

private theorem word_take_old {i : ℕ} (a : ExpandedLabel i) :
    (primeWord a).take i=List.ofFn a.1 := by
  unfold primeWord
  rw [List.append_assoc]
  simpa only [List.length_ofFn] using
    List.take_append_length (List.ofFn a.1)
      ([a.2.2.2.1,a.2.2.1,a.2.1] ++ a.2.2.2.2.primeFactorsList)

/-- Unlike product equality, word equality recovers all old slots and
all distinguished positions. The exact integer tail is recovered by product. -/
theorem word_injective {i N : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a b : ExpandedLabel i} (ha : a ∈ expandedLabels N δ s t W)
    (hb : b ∈ expandedLabels N δ s t W) (hword : primeWord a=primeWord b) : a=b := by
  have hv : a.1=b.1 := by
    apply List.ofFn_injective
    have hh := congrArg (fun l : List ℕ => l.take i) hword
    simpa only [word_take_old] using hh
  have hrest :
      [a.2.2.2.1,a.2.2.1,a.2.1] ++ a.2.2.2.2.primeFactorsList =
        [b.2.2.2.1,b.2.2.1,b.2.1] ++ b.2.2.2.2.primeFactorsList := by
    apply List.append_cancel_left
    simpa only [primeWord,List.append_assoc,hv] using hword
  simp only [List.cons_append,List.nil_append,List.cons.injEq] at hrest
  obtain ⟨h1,h2,h3,htail⟩ := hrest
  have hna := (mem_filter.mp (mem_omega3SwitchedLabels.mp (expanded_data ha).2).2.2.2.2).2.1
  have hnb := (mem_filter.mp (mem_omega3SwitchedLabels.mp (expanded_data hb).2).2.2.2.2).2.1
  have hn := congrArg List.prod htail
  rw [Nat.prod_primeFactorsList (by exact hna.ne'),
    Nat.prod_primeFactorsList (by exact hnb.ne')] at hn
  rcases a with ⟨va,pa3,pa2,pa1,na⟩
  rcases b with ⟨vb,pb3,pb2,pb1,nb⟩
  dsimp only at hv h1 h2 h3 hn
  subst vb
  subst pb1
  subst pb2
  subst pb3
  subst nb
  rfl

theorem tuple_injective {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    (hW : ∀ j p, p ∈ W j → p.Prime) :
    Set.InjOn (tuple (i:=i) N r) (rankLabels N δ s t W r : Set (ExpandedLabel i)) := by
  intro a ha b hb hab
  have hw := congrArg (fun u : Fin r → Fin (N+1) => List.ofFn (fun j => (u j).val)) hab
  rw [tuple_word hW ha,tuple_word hW hb] at hw
  exact word_injective (rank_data ha).1 (rank_data hb).1 hw

theorem tuple_product {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    {a : ExpandedLabel i} (hW : ∀ j p, p ∈ W j → p.Prime)
    (ha : a ∈ rankLabels N δ s t W r) :
    Part3.labelledProduct (tuple N r a)=expandedProduct a := by
  rw [Part3.labelledProduct,←List.prod_ofFn,tuple_word hW ha,word_product (rank_data ha).1]

theorem family_prime {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    (hW : ∀ j p, p ∈ W j → p.Prime) :
    family N δ s t W r ⊆ Part3.labelledPrimeTuples r N := by
  intro u hu
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  refine mem_filter.mpr ⟨mem_univ _,?_⟩
  intro j
  rw [tuple_val hW ha j]
  exact word_primes hW (rank_data ha).1 _ (rawTuple_mem ha j)

theorem family_product_cap {i N r : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    (hW : ∀ j p, p ∈ W j → p.Prime) :
    ∀ u ∈ family N δ s t W r, Part3.labelledProduct u ≤ N := by
  intro u hu
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  rw [tuple_product hW ha]
  exact source_product_le (expanded_data (rank_data ha).1).2

theorem family_test {i : ℕ} (N : ℕ) (δ s t : ℝ) (W : Fin i → Finset ℕ) (r : ℕ)
    (hW : ∀ j p, p ∈ W j → p.Prime) (G : ℕ → ℝ) :
    (∑ u ∈ family N δ s t W r, G (Part3.labelledProduct u)) =
      ∑ a ∈ rankLabels N δ s t W r, G (expandedProduct a) := by
  unfold family
  rw [sum_image]
  · apply sum_congr rfl
    intro a ha
    rw [tuple_product hW ha]
  · exact tuple_injective hW

theorem rank_distribution_eq_actualPP {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (r : ℕ) (hW : ∀ j p, p ∈ W j → p.Prime)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (rankLabels N δ s t W r) expandedProduct
      (fun _ => 1) N D rho =
      Part3.primeProductSignedError r N N D rho
        (p5z_markedPhysicalWeight (family N δ s t W r) (fun _ => 1)) := by
  rw [←p5z_markedDistribution_eq_physicalPP _ (family_prime hW) _ D rho]
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass
  apply sum_congr rfl
  intro q hq
  have hc := family_test N δ s t W r hW (fun m => if Nat.ModEq q m N then 1 else 0)
  have hp := family_test N δ s t W r hW (fun m => if Nat.Coprime m q then 1 else 0)
  rw [hc,hp]

theorem source_test_eq_rank_sum {i N R : ℕ} {δ s t : ℝ} {W : Fin i → Finset ℕ}
    (hR : ∀ a ∈ expandedLabels N δ s t W, (primeWord a).length ≤ R)
    (G : ℕ → ℝ) :
    (∑ a ∈ expandedLabels N δ s t W, G (expandedProduct a)) =
      ∑ r ∈ Finset.range (R+1),
        ∑ a ∈ rankLabels N δ s t W r, G (expandedProduct a) := by
  have hf := sum_fiberwise_of_maps_to
    (s:=expandedLabels N δ s t W) (t:=Finset.range (R+1))
    (g:=fun a => (primeWord a).length)
    (fun a ha => mem_range.mpr (Nat.lt_succ_of_le (hR a ha)))
    (fun a => G (expandedProduct a))
  exact hf.symm

theorem primeMass_eq_rank_tuple_sum {i N R : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} (hW : ∀ j p, p ∈ W j → p.Prime)
    (hR : ∀ a ∈ expandedLabels N δ s t W, (primeWord a).length ≤ R) :
    primeMass N δ s t W =
      ∑ r ∈ Finset.range (R+1),
        p5z_labelledPrimeMass (family N δ s t W r) Part3.labelledProduct
          (fun _ => 1) N := by
  rw [expanded_primeMass]
  unfold p5z_labelledPrimeMass
  rw [source_test_eq_rank_sum hR]
  apply sum_congr rfl
  intro r hr
  exact (family_test N δ s t W r hW
    (fun m => if m < N ∧ Nat.Prime (N-m) then 1 else 0)).symm

/-- The complete signed source error partitions by full rank before any
absolute value is taken. The physical D and rho are identical in every term. -/
theorem expanded_distribution_eq_rank_sum {i N R : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ}
    (hR : ∀ a ∈ expandedLabels N δ s t W, (primeWord a).length ≤ R)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (expandedLabels N δ s t W) expandedProduct
      (fun _ => 1) N D rho =
      ∑ r ∈ Finset.range (R+1),
        p5z_labelledDistributionError (rankLabels N δ s t W r) expandedProduct
          (fun _ => 1) N D rho := by
  unfold p5z_labelledDistributionError p5z_labelledCongruenceMass p5z_labelledCoprimeMass
  calc
    _ = ∑ q ∈ D, ∑ r ∈ Finset.range (R+1), rho q *
        ((∑ a ∈ rankLabels N δ s t W r,
          if Nat.ModEq q (expandedProduct a) N then (1:ℝ) else 0) -
        (∑ a ∈ rankLabels N δ s t W r,
          if Nat.Coprime (expandedProduct a) q then (1:ℝ) else 0) / (Nat.totient q:ℝ)) := by
      apply sum_congr rfl
      intro q hq
      have hc := source_test_eq_rank_sum hR (fun m => if Nat.ModEq q m N then 1 else 0)
      have hp := source_test_eq_rank_sum hR (fun m => if Nat.Coprime m q then 1 else 0)
      rw [hc,hp,←sum_div,←sum_sub_distrib,mul_sum]
    _ = _ := by rw [sum_comm]

theorem native_distribution_eq_rank_PP {i N R : ℕ} {δ s t : ℝ}
    {W : Fin i → Finset ℕ} (hW : ∀ j p, p ∈ W j → p.Prime)
    (hR : ∀ a ∈ expandedLabels N δ s t W, (primeWord a).length ≤ R)
    (D : Finset ℕ) (rho : ℕ → ℝ) :
    p5z_labelledDistributionError (labels N δ s t W) sourceProduct (weight W) N D rho =
      ∑ r ∈ Finset.range (R+1), Part3.primeProductSignedError r N N D rho
        (p5z_markedPhysicalWeight (family N δ s t W r) (fun _ => 1)) := by
  rw [expanded_distribution,expanded_distribution_eq_rank_sum hR]
  apply sum_congr rfl
  intro r hr
  exact rank_distribution_eq_actualPP N δ s t W r hW D rho

/-- A fixed index type, independent of N, for arbitrary depth and moving
window endpoints. Invalid source parameters contribute the empty family. -/
abbrev BoxIndex := Σ i : ℕ, ℝ × (Fin i → ℝ)

def indexedFamily (k : ℕ) (δ : ℝ) (r N : ℕ) (b : BoxIndex) :
    Finset (Fin r → Fin (N+1)) :=
  if wuSourceBox k δ N b.1 b.2.1 b.2.2 then
    family N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2) r
  else ∅

def indexedWeight (k : ℕ) (δ : ℝ) (r N : ℕ) (b : BoxIndex) :
    (Fin r → Fin (N+1)) → ℝ :=
  p5z_markedPhysicalWeight (indexedFamily k δ r N b) (fun _ => 1)

theorem indexedWeight_bounds (k : ℕ) (δ : ℝ) (r N : ℕ) (b : BoxIndex)
    (u : Fin r → Fin (N+1)) :
    0 ≤ indexedWeight k δ r N b u ∧ indexedWeight k δ r N b u ≤ 1 := by
  by_cases hu : u ∈ indexedFamily k δ r N b <;>
    simp [indexedWeight,p5z_markedPhysicalWeight,hu]

theorem indexedFamily_prime (k : ℕ) (δ : ℝ) (r N : ℕ) (b : BoxIndex) :
    indexedFamily k δ r N b ⊆ Part3.labelledPrimeTuples r N := by
  unfold indexedFamily
  split_ifs
  · exact family_prime (fun j p hp => (mem_convolutionWuWindows.mp hp).1)
  · exact empty_subset _

/-- The promised concrete dictionary at edge99's real W1 parameters.
No fixed numerical cap on prime rank is imposed. R and T precede every box. -/
theorem uniform_original_count_dictionary (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) (hε : 0 < ε) :
    ∃ R T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
        wuOmega3Sum N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2) ≤
          (∑ r ∈ Finset.range (R+1),
            p5z_labelledPrimeMass (indexedFamily k δ r N b)
              Part3.labelledProduct (fun _ => 1) N) +
          ε*boxTheta N ((N:ℝ)^(1/2-δ)) (convolutionWuWindows N b.2.1 b.2.2) := by
  obtain ⟨R,T1,hT14,hT1⟩ := uniform_complete_rank k hδ hδhi
  obtain ⟨T2,hT24,hT2⟩ := uniform_original_le_primeFamily k hδ hδhi hε
  refine ⟨R,max T1 T2,hT14.trans (le_max_left _ _),?_⟩
  intro N hN he b hb
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hR : ∀ a ∈ expandedLabels N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2),
      (primeWord a).length ≤ R :=
    fun a ha => (hT1 N hN1 b.1 b.2.1 b.2.2 hb 3 (16/5)
      (by norm_num) (by norm_num) (by norm_num) a ha).1
  have hdict := primeMass_eq_rank_tuple_sum
    (fun j p hp => (mem_convolutionWuWindows.mp hp).1) hR
  have hbase := hT2 N hN2 he b.1 b.2.1 b.2.2 hb 3 (16/5)
    (by norm_num) (by norm_num) (by norm_num)
  rw [hdict] at hbase
  simpa only [indexedFamily,if_pos hb] using hbase

/-- Concrete all-box PP receiver dictionary with the threshold preceding
all moving box parameters. This identifies the existing PP functional; it
does not bound it or assert a smooth-family licence for indexedWeight. -/
theorem uniform_indexed_signed_error_dictionary (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/10) :
    ∃ R T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ b : BoxIndex, wuSourceBox k δ N b.1 b.2.1 b.2.2 →
      ∀ (D : Finset ℕ) (rho : ℕ → ℝ),
        let W := convolutionWuWindows N b.2.1 b.2.2
        p5z_labelledDistributionError (labels N δ 3 (16/5) W)
          sourceProduct (weight W) N D rho =
          ∑ r ∈ Finset.range (R+1), Part3.primeProductSignedError r N N D rho
            (indexedWeight k δ r N b) := by
  obtain ⟨R,T,hT4,hT⟩ := uniform_complete_rank k hδ hδhi
  refine ⟨R,T,hT4,?_⟩
  intro N hN b hb D rho
  dsimp only
  have hR : ∀ a ∈ expandedLabels N δ 3 (16/5) (convolutionWuWindows N b.2.1 b.2.2),
      (primeWord a).length ≤ R :=
    fun a ha => (hT N hN b.1 b.2.1 b.2.2 hb 3 (16/5)
      (by norm_num) (by norm_num) (by norm_num) a ha).1
  have h := native_distribution_eq_rank_PP
    (fun j p hp => (mem_convolutionWuWindows.mp hp).1) hR D rho
  simpa only [indexedWeight,indexedFamily,if_pos hb] using h

end
end ImbalancedChen.P2NativeOmega3RankTupleReceiver
