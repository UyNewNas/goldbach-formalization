import ImbalancedChen.P2GammaInducedCharacterDictionary
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDivisorMean
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherFinite
import Mathlib.Data.Finset.Card

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

Actual original Gamma product fibres have a fixed ordered-divisor norm.
No injectivity of the product map is assumed: every word/quotient label is
retained. The old marked pair is encoded as one positive factor, all word
positions as ordered factors, and the quotient as the last factor. This
proves order cs.length+2 on the COMPLETE integer. Quotient 1 is allowed.

This is a norm theorem, not a distribution theorem. It does not construct
the separated prime factor and its complementary coefficient, and does
not replace the fixed old pair by a long variable.
-/

namespace ImbalancedChen.P2OriginalGammaDivisorNorm
noncomputable section
open scoped Classical BigOperators
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P5OriginalU5CausalFinite (pairSupport)
open P2OriginalU5ExactNormalizedSource P2OriginalGammaUpperLowRankConsumer
open Wu2008DoubleSieve

/-- All ordered positive-factor lists, including the empty factorization
of 1. No literal enumeration is used. -/
def orderedFactors : ℕ → ℕ → Finset (List ℕ)
  | 0,n => if n=1 then {[]} else ∅
  | j+1,n => n.divisors.biUnion
      (fun d => (orderedFactors j (n/d)).image (List.cons d))

theorem mem_orderedFactors (j n : ℕ) (w : List ℕ) :
    w∈orderedFactors j n ↔ w.length=j ∧ w.prod=n ∧ 0<n := by
  induction j generalizing n w with
  | zero =>
      cases w <;> by_cases hn : n=1 <;> simp [orderedFactors,hn,eq_comm]
  | succ j ih =>
      rw [orderedFactors,Finset.mem_biUnion]
      constructor
      · rintro ⟨d,hd,hw⟩
        obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨hlen,hprod,hpos⟩ := (ih (n/d) v).mp hv
        refine ⟨by simpa using congrArg Nat.succ hlen,?_,
          Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2⟩
        rw [List.prod_cons,hprod]
        exact Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      · rintro ⟨hlen,hprod,hpos⟩
        cases w with
        | nil => simp at hlen
        | cons d v =>
          have hdpos : 0<d := by
            have hmul : 0<d*v.prod := by
              rw [← hprod] at hpos
              exact hpos
            exact (Nat.mul_pos_iff.mp hmul).1
          have hvpos : 0<v.prod := by
            have hmul : 0<d*v.prod := by
              rw [← hprod] at hpos
              exact hpos
            exact (Nat.mul_pos_iff.mp hmul).2
          have hddiv : d∣n := by rw [← hprod,List.prod_cons]; exact dvd_mul_right _ _
          refine ⟨d,Nat.mem_divisors.mpr ⟨hddiv,hpos.ne'⟩,Finset.mem_image.mpr ⟨v,?_,rfl⟩⟩
          apply (ih (n/d) v).mpr
          refine ⟨by simpa using hlen,?_,?_⟩
          · rw [← hprod,List.prod_cons,Nat.mul_div_cancel_left _ hdpos]
          · rw [← hprod,List.prod_cons,Nat.mul_div_cancel_left _ hdpos]
            exact hvpos

/-- Counting all ordered factorizations gives the actual zeta-convolution
power, with units and repeated factors retained. -/
theorem card_orderedFactors (j n : ℕ) :
    (orderedFactors j n).card=fouvryTau j n := by
  induction j generalizing n with
  | zero => simp [orderedFactors,fouvryTau,ArithmeticFunction.one_apply]
  | succ j ih =>
      have hdisj : (n.divisors : Set ℕ).PairwiseDisjoint
          (fun d => (orderedFactors j (n/d)).image (List.cons d)) := by
        intro d hd e he hde
        apply Finset.disjoint_left.mpr
        intro w hwd hwe
        obtain ⟨u,hu,hwu⟩ := Finset.mem_image.mp hwd
        obtain ⟨v,hv,hwv⟩ := Finset.mem_image.mp hwe
        have hhead : d=e := (List.cons.inj (hwu.trans hwv.symm)).1
        exact hde hhead
      rw [orderedFactors,Finset.card_biUnion hdisj]
      have hcard (d : ℕ) :
          ((orderedFactors j (n/d)).image (List.cons d)).card=
            fouvryTau j (n/d) := by
        calc
          _ = (orderedFactors j (n/d)).card :=
            Finset.card_image_iff.mpr (fun u hu v hv h => (List.cons.inj h).2)
          _ = _ := ih (n/d)
      simp_rw [hcard]
      rw [fouvryTau_succ]
      exact (Nat.sum_divisorsAntidiagonal (fun _ e => fouvryTau j e)).symm.trans
        (Nat.sum_divisorsAntidiagonal' (fun _ e => fouvryTau j e))

def rootProductFiber (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) (m : ℕ) : Finset Label :=
  (rootLabels N t cs).filter (fun x => product (t.1*t.2) x=m)

def rootProducts (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) : Finset ℕ :=
  (rootLabels N t cs).image (product (t.1*t.2))

def rootFactorList (t : ℕ × ℕ) (x : Label) : List ℕ :=
  (t.1*t.2)::(x.1++[x.2])

/-- Literal positive fixed-mark Gamma fibres, rather than an abstract
divisor-bounded sequence. No source identity or norm is assumed. -/
theorem card_rootProductFiber_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) (m : ℕ) :
    (rootProductFiber N t cs m).card≤fouvryTau (cs.length+2) m := by
  rw [← card_orderedFactors]
  apply Finset.card_le_card_of_injOn (rootFactorList t)
  · intro x hx
    obtain ⟨hx,hm⟩ := Finset.mem_filter.mp hx
    have hdata := rootLabels_data hx
    have hdpos := P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht
    have hpos : 0<product (t.1*t.2) x :=
      Nat.mul_pos (Nat.mul_pos hdpos (word_prod_pos hdata.1)) hdata.2.1
    apply (mem_orderedFactors (cs.length+2) m (rootFactorList t x)).mpr
    refine ⟨?_,?_,by simpa only [hm] using hpos⟩
    · simp only [rootFactorList,List.length_cons,List.length_append,List.length_singleton,
        root_word_length hx]
      omega
    · simpa only [rootFactorList,List.prod_cons,List.prod_append,List.prod_singleton,
        product,mul_assoc] using hm
  · intro x hx y hy hxy
    have hxroot := (Finset.mem_filter.mp hx).1
    have hyroot := (Finset.mem_filter.mp hy).1
    have happ : x.1++[x.2]=y.1++[y.2] := (List.cons.inj hxy).2
    obtain ⟨hw,hn⟩ := List.append_inj happ
      ((root_word_length hxroot).trans (root_word_length hyroot).symm)
    exact Prod.ext hw (by simpa using hn)

/-- Signs are combined on the original product fibre before taking a norm. -/
def rootCoefficient (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (w : Label → ℂ) (m : ℕ) : ℂ :=
  ∑ x ∈ rootProductFiber N t cs m,w x

/-- Every original word/quotient occurrence is grouped at its COMPLETE
product, with its signed scalar intact. -/
theorem root_word_test_eq_grouped (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (w : Label → ℂ) (F : ℕ → ℂ) :
    (∑ x∈rootLabels N t cs,w x*F (product (t.1*t.2) x)) =
      ∑ m∈rootProducts N t cs,rootCoefficient N t cs w m*F m := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := rootLabels N t cs) (t := rootProducts N t cs)
    (g := product (t.1*t.2)) (fun x hx => Finset.mem_image_of_mem _ hx)
    (fun x => w x*F (product (t.1*t.2) x))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  rw [rootCoefficient,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

theorem root_word_real_test_eq_grouped (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (F : ℕ → ℝ) :
    (∑ x∈rootLabels N t cs,F (product (t.1*t.2) x)) =
      ∑ m∈rootProducts N t cs,((rootProductFiber N t cs m).card : ℝ)*F m := by
  have hf := Finset.sum_fiberwise_of_maps_to
    (s := rootLabels N t cs) (t := rootProducts N t cs)
    (g := product (t.1*t.2)) (fun x hx => Finset.mem_image_of_mem _ hx)
    (fun x => F (product (t.1*t.2) x))
  rw [← hf]
  apply Finset.sum_congr rfl
  intro m hm
  calc
    _ = ∑ _x∈rootProductFiber N t cs m,F m := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by simp

/-- Exact grouped original Gamma discrepancy. The list sums preserve all
mother-word multiplicities and keep the same q in count and mean. -/
theorem original_Gamma_eq_grouped (N : ℕ) (t : ℕ × ℕ) (q : ℕ) :
    gammaDiscrepancy N t q =
      (secondFunctionalMotherPrefixIndices.map fun i =>
        ((secondFunctionalMotherGammaWords i).map fun cs =>
          ∑ m∈rootProducts N t cs,
            ((rootProductFiber N t cs m).card : ℝ)*gammaKernel N q m).sum).sum := by
  unfold gammaDiscrepancy sourceTest
  simp_rw [root_word_real_test_eq_grouped]

theorem rootCoefficient_norm_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) (w : Label → ℂ)
    (hw : ∀ x∈rootLabels N t cs,‖w x‖≤1) (m : ℕ) :
    ‖rootCoefficient N t cs w m‖≤(fouvryTau (cs.length+2) m : ℝ) := by
  calc
    _ ≤ ∑ x ∈ rootProductFiber N t cs m,‖w x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ rootProductFiber N t cs m,(1 : ℝ) :=
      Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
    _ = ((rootProductFiber N t cs m).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_rootProductFiber_le ht cs m

/-- The complete-integer coefficient has a fixed logarithmic second norm.
The divisor order depends on the original word length, never on A or N. -/
theorem rootCoefficient_square_sum_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) (w : Label → ℂ)
    (hw : ∀ x∈rootLabels N t cs,‖w x‖≤1) {X : ℝ} (hX : 1≤X)
    (S : Finset ℕ) (hS : S⊆Finset.Ioc 0 (Nat.floor X)) :
    (∑ m∈S,‖rootCoefficient N t cs w m‖^2) ≤
      X*(1+Real.log X)^((cs.length+2)^2-1) := by
  apply sum_alpha_sq_le_fouvryTau (by omega : 1≤cs.length+2) hX S hS
    (fun m => ‖rootCoefficient N t cs w m‖)
  intro m hm
  simpa only [abs_norm] using rootCoefficient_norm_le ht cs w hw m

/-- The unweighted original Gamma occurrence needs no coefficient-norm
premise: its actual fibre multiplicity is the proved divisor majorant. -/
theorem original_Gamma_word_square_sum_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) {X : ℝ} (hX : 1≤X)
    (S : Finset ℕ) (hS : S⊆Finset.Ioc 0 (Nat.floor X)) :
    (∑ m∈S,((rootProductFiber N t cs m).card : ℝ)^2) ≤
      X*(1+Real.log X)^((cs.length+2)^2-1) := by
  apply sum_alpha_sq_le_fouvryTau (by omega : 1≤cs.length+2) hX S hS
    (fun m => ((rootProductFiber N t cs m).card : ℝ))
  intro m hm
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast card_rootProductFiber_le ht cs m

/-- Project away ONE original prime position. This is only the complement
carrier; the original head-dependent geometric mask is not erased. -/
def rootComplementLabels (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) : Finset Label :=
  (rootLabels N t cs).image (fun x => (x.1.tail,x.2))

def labelHead (x : Label) : ℕ := x.1.headD 0

def labelComplement (x : Label) : Label := (x.1.tail,x.2)

theorem original_label_head_prime {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hcs : 0<cs.length) {x : Label} (hx : x∈rootLabels N t cs) :
    (labelHead x).Prime := by
  have hlen := root_word_length hx
  have hwindow := ((secondFunctionalMother_tuple_mem _ _ _).mp
    (Finset.mem_filter.mp (rootLabels_data hx).1).1).2.2
  rcases x with ⟨w,n⟩
  cases w with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons p v =>
      exact (mem_primeWindow.mp (hwindow p (List.mem_cons_self p v))).1

/-- The complete complement contains the old marked pair and the exact
quotient. In particular it is not the residual quotient alone. -/
theorem original_label_head_product {N : ℕ} {t : ℕ × ℕ} {cs : List ℕ}
    (hcs : 0<cs.length) {x : Label} (hx : x∈rootLabels N t cs) :
    product (t.1*t.2) x =
      product (t.1*t.2) (labelComplement x)*labelHead x := by
  have hlen := root_word_length hx
  rcases x with ⟨w,n⟩
  cases w with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons p v =>
      simp only [product,labelComplement,labelHead,List.tail_cons,List.headD_cons,List.prod_cons]
      ring

/-- Actual short PRIME fibre, with the exact moving residue and nonunit
vanishing. This does not charge a complete-scale BV error to each fibre. -/
theorem original_Gamma_prime_fibre_kernel {N q : ℕ} (hq : 0<q)
    (hN : N.Coprime q) {t : ℕ × ℕ} {cs : List ℕ}
    (hcs : 0<cs.length) {x : Label} (hx : x∈rootLabels N t cs) :
    gammaKernel N q (product (t.1*t.2) x) =
      if (product (t.1*t.2) (labelComplement x)).Coprime q then
        gammaKernel (U9SemiprimeSwitch.residue N
          (product (t.1*t.2) (labelComplement x)) q) q (labelHead x)
      else 0 := by
  rw [original_label_head_product hcs hx]
  exact P2OriginalGammaUpperPrimeBVAttachment.gammaKernel_mul hq hN _ _

def rootComplementFiber (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ) (m : ℕ) : Finset Label :=
  (rootComplementLabels N t cs).filter (fun y => product (t.1*t.2) y=m)

private theorem tail_product_pos {w : List ℕ} (hw : 0<w.prod) : 0<w.tail.prod := by
  cases w with
  | nil => simp
  | cons p v => exact (Nat.mul_pos_iff.mp hw).2

/-- Fixed divisor norm of the ACTUAL complete complementary carrier.
The old marked pair remains a sparse factor inside beta; its size is not
discarded from the support scale. There is no number-of-head-primes factor. -/
theorem card_rootComplementFiber_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) (hcs : 1≤cs.length) (m : ℕ) :
    (rootComplementFiber N t cs m).card≤fouvryTau (cs.length+1) m := by
  have hdata : ∀ y∈rootComplementLabels N t cs,
      y.1.length+1=cs.length ∧ 0<y.1.prod ∧ 0<y.2 := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hd := rootLabels_data hx
    refine ⟨?_,tail_product_pos (word_prod_pos hd.1),hd.2.1⟩
    simp only [List.length_tail,root_word_length hx]
    omega
  rw [← card_orderedFactors]
  apply Finset.card_le_card_of_injOn (rootFactorList t)
  · intro y hy
    obtain ⟨hy,hm⟩ := Finset.mem_filter.mp hy
    obtain ⟨hlen,hw,hn⟩ := hdata y hy
    have hpos : 0<product (t.1*t.2) y :=
      Nat.mul_pos (Nat.mul_pos (P2OriginalU5SmallPartnerRootPayment.pair_product_pos ht) hw) hn
    apply (mem_orderedFactors (cs.length+1) m (rootFactorList t y)).mpr
    refine ⟨?_,?_,by simpa only [hm] using hpos⟩
    · simp only [rootFactorList,List.length_cons,List.length_append,List.length_singleton]
      omega
    · simpa only [rootFactorList,List.prod_cons,List.prod_append,List.prod_singleton,
        product,mul_assoc] using hm
  · intro y hy z hz heq
    have hylen := (hdata y (Finset.mem_filter.mp hy).1).1
    have hzlen := (hdata z (Finset.mem_filter.mp hz).1).1
    have happ : y.1++[y.2]=z.1++[z.2] := (List.cons.inj heq).2
    obtain ⟨hw,hn⟩ := List.append_inj happ (by omega : y.1.length=z.1.length)
    exact Prod.ext hw (by simpa using hn)

def rootComplementCoefficient (N : ℕ) (t : ℕ × ℕ) (cs : List ℕ)
    (w : Label → ℂ) (m : ℕ) : ℂ :=
  ∑ y∈rootComplementFiber N t cs m,w y

theorem rootComplementCoefficient_norm_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) (hcs : 1≤cs.length)
    (w : Label → ℂ) (hw : ∀ y∈rootComplementLabels N t cs,‖w y‖≤1) (m : ℕ) :
    ‖rootComplementCoefficient N t cs w m‖≤(fouvryTau (cs.length+1) m : ℝ) := by
  calc
    _ ≤ ∑ y∈rootComplementFiber N t cs m,‖w y‖ := norm_sum_le _ _
    _ ≤ ∑ _y∈rootComplementFiber N t cs m,(1 : ℝ) :=
      Finset.sum_le_sum (fun y hy => hw y (Finset.mem_filter.mp hy).1)
    _ = ((rootComplementFiber N t cs m).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast card_rootComplementFiber_le ht cs hcs m

/-- The complete complementary L2 norm is a fixed logarithmic power.
This is the actual projected Gamma coefficient, rather than an assumed
divisor norm in an abstract convolution class. -/
theorem rootComplementCoefficient_square_sum_le {N : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (cs : List ℕ) (hcs : 1≤cs.length)
    (w : Label → ℂ) (hw : ∀ y∈rootComplementLabels N t cs,‖w y‖≤1)
    {X : ℝ} (hX : 1≤X) (S : Finset ℕ) (hS : S⊆Finset.Ioc 0 (Nat.floor X)) :
    (∑ m∈S,‖rootComplementCoefficient N t cs w m‖^2) ≤
      X*(1+Real.log X)^((cs.length+1)^2-1) := by
  apply sum_alpha_sq_le_fouvryTau (by omega : 1≤cs.length+1) hX S hS
    (fun m => ‖rootComplementCoefficient N t cs w m‖)
  intro m hm
  simpa only [abs_norm] using rootComplementCoefficient_norm_le ht cs hcs w hw m

/-- Original mother-list membership discharges nonemptiness; no extra
prime-fibre shape hypothesis is needed for any original occurrence. -/
theorem actual_mother_prime_fibre {N q i : ℕ} (hq : 0<q) (hN : N.Coprime q)
    {t : ℕ × ℕ} (hi : i∈secondFunctionalMotherPrefixIndices) {cs : List ℕ}
    (hcs : cs∈secondFunctionalMotherGammaWords i) {x : Label}
    (hx : x∈rootLabels N t cs) :
    (labelHead x).Prime ∧
      gammaKernel N q (product (t.1*t.2) x) =
        if (product (t.1*t.2) (labelComplement x)).Coprime q then
          gammaKernel (U9SemiprimeSwitch.residue N
            (product (t.1*t.2) (labelComplement x)) q) q (labelHead x)
        else 0 := by
  have hlen := secondFunctionalMother_prefix_lengths i hi cs hcs
  exact ⟨original_label_head_prime (by omega) hx,
    original_Gamma_prime_fibre_kernel hq hN (by omega) hx⟩

/-- The actual complete Gamma complement receives the fixed divisor
second moment for every original mother occurrence, including unit tails. -/
theorem actual_mother_complement_square_sum {N i : ℕ} {t : ℕ × ℕ}
    (ht : t∈pairSupport N) (hi : i∈secondFunctionalMotherPrefixIndices) {cs : List ℕ}
    (hcs : cs∈secondFunctionalMotherGammaWords i)
    (w : Label → ℂ) (hw : ∀ y∈rootComplementLabels N t cs,‖w y‖≤1)
    {X : ℝ} (hX : 1≤X) (S : Finset ℕ) (hS : S⊆Finset.Ioc 0 (Nat.floor X)) :
    (∑ m∈S,‖rootComplementCoefficient N t cs w m‖^2) ≤
      X*(1+Real.log X)^((cs.length+1)^2-1) := by
  have hlen := secondFunctionalMother_prefix_lengths i hi cs hcs
  exact rootComplementCoefficient_square_sum_le ht cs (by omega) w hw hX S hS

end
end ImbalancedChen.P2OriginalGammaDivisorNorm
