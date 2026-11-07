import ImbalancedChen.RoughSquareException
import ImbalancedChen.P4BNoncoprimeSlotTail
import ImbalancedChen.P4BLabelledPairDictionary
import ImbalancedChen.ActualUpperCountingInputs

/-!
# Weighted original-slot decay on the complete product hyperbola

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

For a bounded rank-two source with complete product at most K, a fixed
original prime p has at most K/p positive cofactors. Combining this actual
count with the reciprocal-square tail gives a weighted slot estimate with
no source-mass or PNT premise. K is a complete-product cap and may exceed N.
Repeated prime slots and both orientations are retained.

The final correction uses the literal attached upper coefficient and its
already proved unit amplitude. The displayed modulus cap Q remains visible;
this file does not manufacture the missing original full22 polynomial range,
a currentK density, geometric licensing, or the signed PP estimate.
-/

namespace ImbalancedChen.P4BWeightedHyperbolaSlotDecay

noncomputable section
open scoped Classical BigOperators
open Part3 P4BLabelledPairDictionary P4BNoncoprimeSlotTail

/-- Every positive cofactor is enumerated, without an additive floor loss. -/
def positiveHyperbolaPairs (K L : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc L K).biUnion (fun p =>
    (Finset.Icc 1 (K / p)).image (fun q => (p, q)))

theorem mem_positiveHyperbolaPairs {K L : ℕ} (hL : 2 ≤ L) (a : ℕ × ℕ) :
    a ∈ positiveHyperbolaPairs K L ↔
      L ≤ a.1 ∧ 1 ≤ a.2 ∧ a.1 * a.2 ≤ K := by
  constructor
  · intro ha
    obtain ⟨p, hp, hpa⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hpa
    cases heq
    have hp0 : 0 < p := by have := (Finset.mem_Icc.mp hp).1; omega
    exact ⟨(Finset.mem_Icc.mp hp).1, (Finset.mem_Icc.mp hq).1,
      by simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le hp0).mp (Finset.mem_Icc.mp hq).2⟩
  · rintro ⟨haL, haq, haK⟩
    have hp0 : 0 < a.1 := by omega
    have hpK : a.1 ≤ K :=
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left a.1 haq).trans haK
    apply Finset.mem_biUnion.mpr
    refine ⟨a.1, Finset.mem_Icc.mpr ⟨haL, hpK⟩, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨a.2, Finset.mem_Icc.mpr ⟨haq, ?_⟩, rfl⟩
    exact (Nat.le_div_iff_mul_le hp0).mpr (by simpa only [Nat.mul_comm] using haK)

/-- Exact cofactor summation. Distinct first coordinates have disjoint fibres. -/
theorem hyperbola_first_reciprocal_eq (K L : ℕ) :
    (∑ a ∈ positiveHyperbolaPairs K L, 1 / ((a.1 : ℝ) - 1)) =
      ∑ p ∈ Finset.Icc L K, ((K / p : ℕ) : ℝ) / ((p : ℝ) - 1) := by
  unfold positiveHyperbolaPairs
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _hp
    rw [Finset.sum_image]
    · simp
    · intro q _hq r _hr hqr
      exact congrArg Prod.snd hqr
  · intro p _hp r _hr hpr
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨q, _hq, hq⟩ := Finset.mem_image.mp ha
    obtain ⟨s, _hs, hs⟩ := Finset.mem_image.mp hb
    exact hpr (congrArg Prod.fst (hq.trans hs.symm))

/-- The hyperbola itself supplies inverse-cutoff decay; no weighted mass
bound or prime-distribution estimate occurs in the hypotheses. -/
theorem hyperbola_first_reciprocal_le (K L : ℕ) (hL : 2 ≤ L) :
    (∑ a ∈ positiveHyperbolaPairs K L, 1 / ((a.1 : ℝ) - 1)) ≤
      2 * (K : ℝ) / ((L : ℝ) - 1) := by
  rw [hyperbola_first_reciprocal_eq]
  have hterms : (∑ p ∈ Finset.Icc L K,
      ((K / p : ℕ) : ℝ) / ((p : ℝ) - 1)) ≤
      ∑ p ∈ Finset.Icc L K, (2 * (K : ℝ)) * (1 / (p : ℝ) ^ 2) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hL.trans (Finset.mem_Icc.mp hp).1)
    have hp0 : (0 : ℝ) < p := by linarith only [hp2]
    have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hp2]
    have hdiv : ((K / p : ℕ) : ℝ) ≤ (K : ℝ) / (p : ℝ) := by
      apply (le_div_iff₀ hp0).mpr
      exact_mod_cast Nat.div_mul_le_self K p
    have hrec : 1 / ((p : ℝ) - 1) ≤ 2 / (p : ℝ) := by
      apply (div_le_div_iff₀ hp1 hp0).mpr
      linarith only [hp2]
    calc
      _ = ((K / p : ℕ) : ℝ) * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ ((K : ℝ) / (p : ℝ)) * (2 / (p : ℝ)) :=
        mul_le_mul hdiv hrec (one_div_nonneg.mpr hp1.le) (by positivity)
      _ = _ := by field_simp [hp0.ne']; ring
  calc
    _ ≤ ∑ p ∈ Finset.Icc L K, (2 * (K : ℝ)) * (1 / (p : ℝ) ^ 2) := hterms
    _ = (2 * (K : ℝ)) * ∑ p ∈ Finset.Icc L K, 1 / (p : ℝ) ^ 2 :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 * (K : ℝ)) * (1 / ((L : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_left (reciprocalSquare_Icc_tail_le K hL) (by positivity)
    _ = _ := by ring

def otherSlot (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

def slotPair {N : ℕ} (i : Fin 2) (t : Fin 2 → Fin (N + 1)) : ℕ × ℕ :=
  ((t i).val, (t (otherSlot i)).val)

theorem slotPair_injective (N : ℕ) (i : Fin 2) : Function.Injective (@slotPair N i) := by
  intro t u h
  funext j
  apply Fin.ext
  fin_cases i <;> fin_cases j
  · simpa [slotPair, otherSlot] using congrArg Prod.fst h
  · simpa [slotPair, otherSlot] using congrArg Prod.snd h
  · simpa [slotPair, otherSlot] using congrArg Prod.snd h
  · simpa [slotPair, otherSlot] using congrArg Prod.fst h

theorem slotPair_product {N : ℕ} (i : Fin 2) (t : Fin 2 → Fin (N + 1)) :
    (slotPair i t).1 * (slotPair i t).2 = labelledProduct t := by
  fin_cases i <;> simp [slotPair, otherSlot, labelledProduct, Fin.prod_univ_two, Nat.mul_comm]

/-- Each original labelled slot has its own actual hyperbola decay. -/
theorem labelled_slot_reciprocal_le {N K L : ℕ} (hL : 2 ≤ L)
    (S : Finset (Fin 2 → Fin (N + 1))) (hS : S ⊆ labelledPrimeTuples 2 N)
    (hrough : ∀ t ∈ S, ∀ i, L ≤ (t i).val)
    (hproduct : ∀ t ∈ S, labelledProduct t ≤ K) (i : Fin 2) :
    (∑ t ∈ S, 1 / (((t i).val : ℝ) - 1)) ≤ 2 * (K : ℝ) / ((L : ℝ) - 1) := by
  let A := S.image (slotPair i)
  have hA : A ⊆ positiveHyperbolaPairs K L := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    have hp := (Finset.mem_filter.mp (hS ht)).2 (otherSlot i)
    exact (mem_positiveHyperbolaPairs hL _).mpr
      ⟨hrough t ht i, hp.one_le, by simpa only [slotPair_product] using hproduct t ht⟩
  have heq : (∑ a ∈ A, 1 / ((a.1 : ℝ) - 1)) =
      ∑ t ∈ S, 1 / (((t i).val : ℝ) - 1) := by
    exact Finset.sum_image (fun t _ht u _hu htu => slotPair_injective N i htu)
  rw [← heq]
  apply (Finset.sum_le_sum_of_subset_of_nonneg hA ?_).trans
    (hyperbola_first_reciprocal_le K L hL)
  intro a ha _hnot
  have haL := ((mem_positiveHyperbolaPairs hL a).mp ha).1
  have ha2 : (2 : ℝ) ≤ a.1 := by exact_mod_cast hL.trans haL
  exact one_div_nonneg.mpr (by linarith only [ha2])

/-- A quantitative weighted-slot supplier from complete-product geometry.
No source-mass limit is assumed, and |V| permits either sign of the weight. -/
theorem weighted_labelled_slot_cost_le {N K L : ℕ} (hL : 2 ≤ L)
    (S : Finset (Fin 2 → Fin (N + 1))) (hS : S ⊆ labelledPrimeTuples 2 N)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ t ∈ S, |V t| ≤ B)
    (hrough : ∀ t ∈ S, ∀ i, L ≤ (t i).val)
    (hproduct : ∀ t ∈ S, labelledProduct t ≤ K) :
    (∑ t ∈ S, |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1))) ≤
      16 * B * (K : ℝ) / ((L : ℝ) - 1) := by
  have hslot (i : Fin 2) :
      (∑ t ∈ S, |V t| * (4 / (((t i).val : ℝ) - 1))) ≤
        (4 * B) * (2 * (K : ℝ) / ((L : ℝ) - 1)) := by
    calc
      _ ≤ ∑ t ∈ S, B * (4 / (((t i).val : ℝ) - 1)) := by
        apply Finset.sum_le_sum
        intro t ht
        have hp2 : (2 : ℝ) ≤ (t i).val := by
          exact_mod_cast ((Finset.mem_filter.mp (hS ht)).2 i).two_le
        exact mul_le_mul_of_nonneg_right (hV t ht) (by positivity)
      _ = (4 * B) * ∑ t ∈ S, 1 / (((t i).val : ℝ) - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _ht
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (labelled_slot_reciprocal_le hL S hS hrough hproduct i) (by positivity)
  calc
    _ = ∑ i : Fin 2, ∑ t ∈ S, |V t| * (4 / (((t i).val : ℝ) - 1)) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ _i : Fin 2, (4 * B) * (2 * (K : ℝ) / ((L : ℝ) - 1)) :=
      Finset.sum_le_sum (fun i _hi => hslot i)
    _ = _ := by simp only [Fin.sum_univ_two]; ring

/-- Support restrictions are required only where the signed weight is
nonzero; zero-weight points in the full prime carrier stay harmless. -/
theorem full_weighted_slot_cost_le {N K L : ℕ} (hL : 2 ≤ L)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, |V t| ≤ B)
    (hrough : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → ∀ i, L ≤ (t i).val)
    (hproduct : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → labelledProduct t ≤ K) :
    (∑ t ∈ labelledPrimeTuples 2 N,
      |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1))) ≤
      16 * B * (K : ℝ) / ((L : ℝ) - 1) := by
  let S := (labelledPrimeTuples 2 N).filter (fun t => V t ≠ 0)
  have heq : (∑ t ∈ S, |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1))) =
      ∑ t ∈ labelledPrimeTuples 2 N,
        |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _ht
    by_cases ht : V t = 0 <;> simp [ht]
  rw [← heq]
  exact weighted_labelled_slot_cost_le hL S
    (fun t ht => (Finset.mem_filter.mp ht).1) V B hB
    (fun t ht => hV t (Finset.mem_filter.mp ht).1)
    (fun t ht => hrough t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2)
    (fun t ht => hproduct t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2)

/-- Quantitative complete-product correction for the literal actual upper
coefficient. Its amplitude is proved by the original unique small/rough
construction, rather than supplied as an unrelated bound. Polynomial Q
is intentionally not asserted for an arbitrary retention policy. -/
theorem actual_upper_outer_correction_le_hyperbola
    {N K L Q : ℕ} (hL : 2 ≤ L)
    (nu r epsilon : ℝ) (retain : ℕ → List ℕ → Bool) (cap : ℕ → ℕ)
    (hQ : attachedUpperModuli nu r epsilon retain cap N ⊆ Finset.Icc 1 Q)
    (V : (Fin 2 → Fin (N + 1)) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hV : ∀ t ∈ labelledPrimeTuples 2 N, |V t| ≤ B)
    (hrough : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → ∀ i, L ≤ (t i).val)
    (hproduct : ∀ t ∈ labelledPrimeTuples 2 N, V t ≠ 0 → labelledProduct t ≤ K) :
    |∑ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      attachedUpperCoefficient nu r epsilon retain cap N d *
        ((finiteCoprimeMass (P4BLabelledOuterPushforward.productCarrier N)
            (P4BLabelledOuterPushforward.productWeight N V) d -
          finiteSourceMass (P4BLabelledOuterPushforward.productCarrier N)
            (P4BLabelledOuterPushforward.productWeight N V)) / (Nat.totient d : ℝ))| ≤
      (16 * B * (K : ℝ) / ((L : ℝ) - 1)) * (1 + Real.log (max 1 (Q : ℝ))) := by
  have hrho : ∀ d ∈ attachedUpperModuli nu r epsilon retain cap N,
      |attachedUpperCoefficient nu r epsilon retain cap N d| ≤ 1 := by
    intro d _hd
    exact actualSmallRoughRho_abs_le_one (retain N) N (cap N) _ _ _ d
  have hfinite := outer_signed_correction_le_slot_cost N V
    (attachedUpperModuli nu r epsilon retain cap N) Q hQ
    (attachedUpperCoefficient nu r epsilon retain cap N) 1 (by norm_num) hrho
  have hlog : 0 ≤ 1 + Real.log (max 1 (Q : ℝ)) := by
    have := Real.log_nonneg (le_max_left (1 : ℝ) (Q : ℝ))
    linarith
  have heq : (∑ t ∈ labelledPrimeTuples 2 N, |V t| * (1 *
      (∑ i : Fin 2, (4 / (((t i).val : ℝ) - 1)) *
        (1 + Real.log (max 1 (Q : ℝ))))))) =
      (∑ t ∈ labelledPrimeTuples 2 N,
        |V t| * (∑ i : Fin 2, 4 / (((t i).val : ℝ) - 1))) *
          (1 + Real.log (max 1 (Q : ℝ))) := by
    simp_rw [← Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _ht
    ring
  rw [heq] at hfinite
  exact hfinite.trans (mul_le_mul_of_nonneg_right
    (full_weighted_slot_cost_le hL V B hB hV hrough hproduct) hlog)

end
end ImbalancedChen.P4BWeightedHyperbolaSlotDecay
