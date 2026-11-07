import ImbalancedChen.P2ActualSameQTwentyOnePositiveSourceBinding
import ImbalancedChen.P2EnhancedOrderedReciprocalBudget
import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual G small-partner remainder is paid by its output fibres.  Only
the original specified prime word is encoded; the masked tail is recovered
from its full product.  Thus no absolute tail roughness, complete-word rank
cap, old-prime floor, or switched-family licence is required for this bound.
Every original Gamma occurrence and every real marked weight is retained.
-/
namespace ImbalancedChen.P2TwentyOneSmallPartnerOutputFibres
noncomputable section
open Finset Wu2008DoubleSieve
open scoped Classical BigOperators
open P2TwentyOneUnsiftedArithmeticSource
open P2TwentyOneAllWordTailDecomposition
open P2ActualSameQTwentyOnePositiveSourceBinding
open P2EnhancedTwentyOneSameQWeighted (cutoff)
open P2EnhancedOrderedReciprocalBudget (wordBudget wordBudget_le_sixth)

def coordinates (r : ℕ) (x : Label) : Fin r → ℕ := fun j => x.1.getD j.val 0

theorem coordinates_word {r : ℕ} {x : Label} (hlen : x.1.length=r) :
    List.ofFn (coordinates r x)=x.1 := by
  subst r
  rw [show coordinates x.1.length x=(fun j : Fin x.1.length => x.1[j.val]) from by
    funext j
    exact List.getD_eq_getElem _ _ j.isLt]
  exact List.ofFn_getElem

theorem source_word_length {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    {x : Label} (hx : x ∈ arithmeticLabels N d M a b c e f cs) : x.1.length=cs.length := by
  have hw := (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  exact ((secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hw).1).1

/-- The full product and the labelled specified word recover the exact tail.
This is not injectivity of the product map.  The tail n=1 is included. -/
theorem product_coordinates_injective {N d M : ℕ} {a b c e f : ℝ} {cs : List ℕ}
    (hd : 0<d) :
    Set.InjOn (fun x : Label => (product d x,coordinates cs.length x))
      (arithmeticLabels N d M a b c e f cs : Set Label) := by
  intro x hx y hy hxy
  have hc := congrArg Prod.snd hxy
  have hw : x.1=y.1 := (coordinates_word (source_word_length hx)).symm.trans
    ((congrArg List.ofFn hc).trans (coordinates_word (source_word_length hy)))
  have hprod := congrArg Prod.fst hxy
  have hp : 0<d*x.1.prod := mul_pos hd
    (word_prod_pos (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1)
  have hn : x.2=y.2 := by
    apply Nat.eq_of_mul_eq_mul_left hp
    simpa only [product,← hw] using hprod
  exact Prod.ext hw hn

def smallLabels (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) (z : ℕ) : Finset Label :=
  (arithmeticLabels N d M a b c e f cs).filter
    (fun x => product d x<N ∧ Nat.Prime (N-product d x) ∧ N-product d x<z)

theorem smallMass_eq_card (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) (z : ℕ) :
    p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs)
      (product d) (fun _ => 1) N z=(smallLabels N d M a b c e f cs z).card := by
  simp only [p5z_labelledSmallPrimeMass,smallLabels,Finset.card_eq_sum_ones,
    Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

/-- All arities, with the original masked tail.  The exact small output
interval has at most z products, and each product retains every word label. -/
theorem prefix_smallMass_le {N d M z : ℕ} {a b c e f eta : ℝ} {cs : List ℕ}
    (hN : 1<N) (hd : 0<d) (heta : 0<eta) (hcut : (N : ℝ)^eta≤a) :
    p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs)
      (product d) (fun _ => 1) N z ≤ (1/eta)^cs.length*(z : ℝ) := by
  let S := smallLabels N d M a b c e f cs z
  let E := (Finset.range z).image (fun ell => N-ell)
  have hs (x : Label) (hx : x ∈ S) : x ∈ arithmeticLabels N d M a b c e f cs :=
    (Finset.mem_filter.mp hx).1
  have hg (x : Label) (hx : x ∈ S) : Geometry N d x :=
    (Finset.mem_filter.mp (hs x hx)).2
  have hbound : (S.card : ℝ)≤(1/eta)^cs.length*(E.card : ℝ) := by
    apply omega3_labels_card_le_outputs S (product d) (coordinates cs.length) E
      ((product_coordinates_injective (N:=N) (M:=M) (a:=a) (b:=b)
        (c:=c) (e:=e) (f:=f) (cs:=cs) hd).mono (Finset.filter_subset _ _)) _ hN heta
    · intro x hx
      apply Finset.mem_image.mpr
      refine ⟨N-product d x,Finset.mem_range.mpr (Finset.mem_filter.mp hx).2.2.2,?_⟩
      exact Nat.sub_sub_self (hg x hx).2.2.le
    · intro x hx
      exact ⟨mul_pos (mul_pos hd
        (word_prod_pos (Finset.mem_product.mp (Finset.mem_filter.mp (hs x hx)).1).1))
          (hg x hx).1,(hg x hx).2.2.le⟩
    · intro x hx j
      have hw := (Finset.mem_product.mp (Finset.mem_filter.mp (hs x hx)).1).1
      have ht := (secondFunctionalMother_tuple_mem _ _ _).mp (Finset.mem_filter.mp hw).1
      have hj : j.val<x.1.length := by rw [ht.1]; exact j.isLt
      have hm : coordinates cs.length x j ∈ x.1 := by
        simp only [coordinates,List.getD_eq_getElem _ _ hj]
        exact List.getElem_mem hj
      have hp := mem_primeWindow.mp (ht.2.2 _ hm)
      refine ⟨hp.1,?_,hcut.trans hp.2.2.1⟩
      exact (List.dvd_prod hm).trans
        ((dvd_mul_left x.1.prod d).trans (dvd_mul_right (d*x.1.prod) x.2))
  have hE : E.card≤z := Finset.card_image_le.trans (by simp)
  rw [smallMass_eq_card]
  exact hbound.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hE)
    (pow_nonneg (one_div_nonneg.mpr heta.le) _))

/-- The existing production polynomial counts all 22 original occurrences:
2 H^2 + 14 H^3 + 4 H^4 + H^5 + H^6.  No occurrence is deduplicated. -/
theorem allWords_smallMass_le {N d M z : ℕ} {a b c e f eta : ℝ}
    (hN : 1<N) (hd : 0<d) (heta : 0<eta) (hcut : (N : ℝ)^eta≤a) :
    smallPartnerSwitchedMass N d M a b c e f z ≤
      22*(max 1 (1/eta))^6*(z : ℝ) := by
  let H : ℝ := max 1 (1/eta)
  have hword (cs : List ℕ) :
      p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs)
        (product d) (fun _ => 1) N z≤H^cs.length*(z : ℝ) :=
    (prefix_smallMass_le hN hd heta hcut).trans
      (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (one_div_nonneg.mpr heta.le) (le_max_right _ _) _)
        (Nat.cast_nonneg z))
  have hrow (i : ℕ) := secondFunctionalMother_list_sum_mono
    (secondFunctionalMotherGammaWords i)
    (fun cs => p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs)
      (product d) (fun _ => 1) N z)
    (fun cs => H^cs.length*(z : ℝ)) (fun cs _ => hword cs)
  have hall := secondFunctionalMother_list_sum_mono secondFunctionalMotherPrefixIndices
    (fun i => ((secondFunctionalMotherGammaWords i).map fun cs =>
      p5z_labelledSmallPrimeMass (arithmeticLabels N d M a b c e f cs)
        (product d) (fun _ => 1) N z).sum)
    (fun i => ((secondFunctionalMotherGammaWords i).map fun cs => H^cs.length).sum*(z : ℝ))
    (fun i _ => by simpa only [List.sum_map_mul_right] using hrow i)
  have hmass : smallPartnerSwitchedMass N d M a b c e f z≤wordBudget H*(z : ℝ) := by
    simpa only [smallPartnerSwitchedMass,wordBudget,List.sum_map_mul_right] using hall
  exact hmass.trans (mul_le_mul_of_nonneg_right
    (wordBudget_le_sixth (le_max_left _ _)) (Nat.cast_nonneg z))

theorem actualSmallPartnerMass_le {N z : ℕ} {Q eta : ℝ}
    (D : Finset ℕ) (sigma : ℕ → ℝ) (hN : 1<N) (heta : 0<eta)
    (hd : ∀ d ∈ D,0<d) (hsigma : ∀ d ∈ D,0≤sigma d)
    (hcut : ∀ d ∈ D,(N : ℝ)^eta≤cutoff Q d (227/50)) :
    actualSmallPartnerMass N Q D sigma z≤
      (22*(max 1 (1/eta))^6*(z : ℝ))*(∑ d ∈ D,sigma d) := by
  unfold actualSmallPartnerMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdD
  have h := mul_le_mul_of_nonneg_left
    (allWords_smallMass_le (M:=N) (z:=z)
      (b:=cutoff Q d (353/100)) (c:=cutoff Q d (29/10))
      (e:=cutoff Q d (61/25)) (f:=cutoff Q d (11/5))
      hN (hd d hdD) heta (hcut d hdD)) (hsigma d hdD)
  simpa only [mul_comm] using h

end
end ImbalancedChen.P2TwentyOneSmallPartnerOutputFibres
