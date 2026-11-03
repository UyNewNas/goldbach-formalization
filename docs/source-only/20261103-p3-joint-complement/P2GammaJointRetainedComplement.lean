import ImbalancedChen.P2GammaJointLabels
import ImbalancedChen.P2GammaRetainedSameRhoRows

/-!
SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED.

Joint retained COMPLEMENTS, not complete Gamma products. Both old primes,
the original tail word and the original positive quotient are encoded.
The order is cs.length + 3 for a full mother word c::cs. Equal products
are summed with their labelled multiplicities. No outside pair count or
selector L1 mass occurs in the coefficient bound.
-/

namespace ImbalancedChen.P2GammaJointRetainedComplement
noncomputable section
open scoped Classical BigOperators
open P2TwentyOneUnsiftedArithmeticSource P2OriginalU5WholeGroupCapacity
open P2OriginalGammaDivisorNorm P2GammaJointLabels
open P2GammaOriginalCartesianMask P2GammaRetainedInteriorGeometry
open P2GammaRetainedActualNorms P2GammaSmoothLogGrid
open P5OriginalU5CausalFinite (pairSupport)
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- A tagged union, before choosing any modulus, character or residue. -/
def jointRetainedLabels (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ) :
    Finset JointLabel :=
  (pairSupport N).biUnion (fun t =>
    (retainedComplementLabels N t c cs H δ j l).image (fun y => (t,y)))

theorem mem_jointRetainedLabels (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l : ℕ) (z : JointLabel) :
    z ∈ jointRetainedLabels N c cs H δ j l ↔
      z.1 ∈ pairSupport N ∧
        z.2 ∈ retainedComplementLabels N z.1 c cs H δ j l := by
  rcases z with ⟨t,y⟩
  simp [jointRetainedLabels]

theorem retained_tail_length {N c : ℕ} {cs : List ℕ} {H δ : ℝ}
    {j l : ℕ} {t : ℕ × ℕ} {y : Label}
    (hy : y ∈ retainedComplementLabels N t c cs H δ j l) :
    y.1.length = cs.length := by
  obtain ⟨p,hp⟩ := complement_has_original_head (Finset.mem_filter.mp hy).1
  have h := root_word_length hp
  change (p::y.1).length = (c::cs).length at h
  exact Nat.succ.inj h

theorem jointRetained_product_pos {N c : ℕ} {cs : List ℕ} {H δ : ℝ}
    {j l : ℕ} {z : JointLabel}
    (hz : z ∈ jointRetainedLabels N c cs H δ j l) : 0 < jointProduct z := by
  obtain ⟨ht,hy⟩ := (mem_jointRetainedLabels N c cs H δ j l z).mp hz
  exact complement_product_pos ht (Finset.mem_filter.mp hy).1

/-- Generic additive reindexing preserves all tagged occurrences. -/
theorem jointRetained_sum_eq_pair_sum {α : Type*} [AddCommMonoid α]
    (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ) (F : JointLabel → α) :
    (∑ z ∈ jointRetainedLabels N c cs H δ j l,F z) =
      ∑ t ∈ pairSupport N,
        ∑ y ∈ retainedComplementLabels N t c cs H δ j l,F (t,y) := by
  have hd : (↑(pairSupport N) : Set (ℕ × ℕ)).PairwiseDisjoint
      (fun t => (retainedComplementLabels N t c cs H δ j l).image (fun y => (t,y))) := by
    intro t ht u hu htu
    apply Finset.disjoint_left.mpr
    intro z hzt hzu
    obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hzt
    obtain ⟨y,hy,hyz⟩ := Finset.mem_image.mp hzu
    exact htu (congrArg Prod.fst (hxz.trans hyz.symm))
  rw [jointRetainedLabels,Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.sum_image (fun x hx y hy hxy => (Prod.mk.inj hxy).2)

def jointRetainedFiber (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l m : ℕ) :
    Finset JointLabel :=
  (jointRetainedLabels N c cs H δ j l).filter (fun z => jointProduct z = m)

def jointRetainedProducts (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ) :
    Finset ℕ :=
  (jointRetainedLabels N c cs H δ j l).image jointProduct

/-- The code is the existing [t1,t2] ++ tail ++ [quotient]. Its recovery
is injective, not the complementary-product map. Quotient one is kept. -/
theorem card_jointRetainedFiber_le (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l m : ℕ) :
    (jointRetainedFiber N c cs H δ j l m).card ≤ fouvryTau (cs.length+3) m := by
  rw [← card_orderedFactors]
  apply Finset.card_le_card_of_injOn jointFactorList
  · intro z hz
    obtain ⟨hz,hm⟩ := Finset.mem_filter.mp hz
    obtain ⟨ht,hy⟩ := (mem_jointRetainedLabels N c cs H δ j l z).mp hz
    apply (mem_orderedFactors (cs.length+3) m (jointFactorList z)).mpr
    refine ⟨?_,?_,hm ▸ jointRetained_product_pos hz⟩
    · simp only [jointFactorList,List.length_cons,List.length_append,
        List.length_singleton,retained_tail_length hy]
      omega
    · simpa only [jointFactorList,List.prod_cons,List.prod_append,
        List.prod_singleton,jointProduct,product,mul_assoc] using hm
  · intro z hz v hv heq
    have hz' := (mem_jointRetainedLabels N c cs H δ j l z).mp
      (Finset.mem_filter.mp hz).1
    have hv' := (mem_jointRetainedLabels N c cs H δ j l v).mp
      (Finset.mem_filter.mp hv).1
    obtain ⟨h1,hrest⟩ := List.cons.inj heq
    obtain ⟨h2,happ⟩ := List.cons.inj hrest
    obtain ⟨hw,hq⟩ := List.append_inj happ
      ((retained_tail_length hz'.2).trans (retained_tail_length hv'.2).symm)
    exact Prod.ext (Prod.ext h1 h2) (Prod.ext hw (by simpa using hq))

/-- Actual joint coefficient; complex selectors permit later signed
interval decompositions without changing the source or its fibre bound. -/
def jointBeta (N c : ℕ) (cs : List ℕ) (H δ : ℝ) (j l : ℕ)
    (sigma : (ℕ × ℕ) → ℂ) (m : ℕ) : ℂ :=
  ∑ z ∈ jointRetainedFiber N c cs H δ j l m,
    sigma z.1 * betaLabel N z.1 H δ j l z.2

theorem jointBeta_eq_pair_sum (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l m : ℕ) (sigma : (ℕ × ℕ) → ℂ) :
    jointBeta N c cs H δ j l sigma m =
      ∑ t ∈ pairSupport N,sigma t * retainedBeta N t c cs H δ j l m := by
  simp only [jointBeta,jointRetainedFiber,Finset.sum_filter]
  rw [jointRetained_sum_eq_pair_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [retainedBeta_eq_retained_fiber,Finset.sum_filter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hm : product (t.1*t.2) y = m <;> simp [jointProduct,hm]

theorem jointBeta_zero_off_support (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l m : ℕ) (sigma : (ℕ × ℕ) → ℂ)
    (hm : m ∉ jointRetainedProducts N c cs H δ j l) :
    jointBeta N c cs H δ j l sigma m = 0 := by
  apply Finset.sum_eq_zero
  intro z hz
  obtain ⟨hz,hzm⟩ := Finset.mem_filter.mp hz
  exact (hm (Finset.mem_image.mpr ⟨z,hz,hzm⟩)).elim

theorem jointBeta_norm_le (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l m : ℕ) (sigma : (ℕ × ℕ) → ℂ) {height : ℝ}
    (hh : 0 ≤ height) (hs : ∀ t ∈ pairSupport N,‖sigma t‖ ≤ height) :
    ‖jointBeta N c cs H δ j l sigma m‖ ≤
      height * (fouvryTau (cs.length+3) m : ℝ) := by
  calc
    _ ≤ ∑ z ∈ jointRetainedFiber N c cs H δ j l m,
        ‖sigma z.1 * betaLabel N z.1 H δ j l z.2‖ := norm_sum_le _ _
    _ ≤ ∑ _z ∈ jointRetainedFiber N c cs H δ j l m,height := by
      apply Finset.sum_le_sum
      intro z hz
      have ht := ((mem_jointRetainedLabels N c cs H δ j l z).mp
        (Finset.mem_filter.mp hz).1).1
      rw [norm_mul]
      exact (mul_le_mul (hs z.1 ht) (betaLabel_norm_le_one N z.1 H δ j l z.2)
        (norm_nonneg _) hh).trans_eq (mul_one _)
    _ ≤ height * (fouvryTau (cs.length+3) m : ℝ) := by
      simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm] using
        mul_le_mul_of_nonneg_left
          (show ((jointRetainedFiber N c cs H δ j l m).card : ℝ) ≤
              (fouvryTau (cs.length+3) m : ℝ) by
            exact_mod_cast card_jointRetainedFiber_le N c cs H δ j l m) hh

/-- Exact test identity, chosen after constructing the joint coefficient. -/
theorem jointBeta_test_eq_pair (N c : ℕ) (cs : List ℕ) (H δ : ℝ)
    (j l : ℕ) (sigma : (ℕ × ℕ) → ℂ) (F : ℕ → ℂ) :
    (∑ m ∈ jointRetainedProducts N c cs H δ j l,
      jointBeta N c cs H δ j l sigma m * F m) =
      ∑ t ∈ pairSupport N,sigma t *
        ∑ m ∈ retainedComplementSupport N t c cs H δ j l,
          retainedBeta N t c cs H δ j l m * F m := by
  simp_rw [jointBeta_eq_pair_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  simp only [mul_assoc]
  symm
  apply Finset.sum_subset
  · intro m hm
    obtain ⟨y,hy,hym⟩ := Finset.mem_image.mp hm
    exact Finset.mem_image.mpr ⟨(t,y),
      (mem_jointRetainedLabels N c cs H δ j l (t,y)).mpr ⟨ht,hy⟩,hym⟩
  · intro m hm hnot
    simp only [retainedBeta_zero_off_support N t c cs H δ j l m hnot,mul_zero,zero_mul]

/-- The complete complementary scale is inherited from actual nonzero
hat labels, including both old primes. -/
theorem jointRetainedProducts_subset_cap (N c : ℕ) (cs : List ℕ)
    (H : ℝ) {δ : ℝ} (hδ : 0 < δ) (hwidth : 2*δ ≤ Real.log 2) (j l : ℕ) :
    jointRetainedProducts N c cs H δ j l ⊆
      Finset.Icc 1 (Nat.floor (2*lower δ l)) := by
  intro m hm
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨ht,hy⟩ := (mem_jointRetainedLabels N c cs H δ j l z).mp hz
  exact retainedComplementSupport_subset_cap ht hδ hwidth j l
    (Finset.mem_image_of_mem (product (z.1.1*z.1.2)) hy)

end
end ImbalancedChen.P2GammaJointRetainedComplement
