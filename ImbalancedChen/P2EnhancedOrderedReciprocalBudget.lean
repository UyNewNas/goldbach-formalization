import ImbalancedChen.P2EnhancedTwentyOneQuotientFinite
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitSieveMultiplicity
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Finite reciprocal mass of the actual arbitrary-arity ordered mother
tuples. Every whole ordered list embeds in the full coordinate cube;
the product image is never used as the label carrier. The existing exact
list-recovery lemma is reused. The cube mass is evaluated by finite
Fubini, and the original Gamma7,...,Gamma21 dictionary has the explicit
budget 2 H^2 + 14 H^3 + 4 H^4 + H^5 + H^6 <= 22 H^6 for H>=1.

This is the reciprocal-mass prerequisite for summing the real selected
square collision bound. It is independent of all enhanced H/h, moving
residue, K, and numerical seed assumptions.
-/

namespace ImbalancedChen.P2EnhancedOrderedReciprocalBudget

noncomputable section

open Finset Wu2008DoubleSieve
open scoped Classical

def coordinates (r : ℕ) (l : List ℕ) : Fin r → ℕ := fun j => l.getD j 0

theorem coordinates_product {r : ℕ} {l : List ℕ} (hlen : l.length = r) :
    (∏ j : Fin r, (coordinates r l j : ℝ)) = (l.prod : ℝ) := by
  subst r
  have hof : List.ofFn (coordinates l.length l) = l := by
    rw [show coordinates l.length l = (fun j : Fin l.length => l[j.val]) from by
      funext j
      exact List.getD_eq_getElem _ _ j.isLt]
    exact List.ofFn_getElem
  have hprod := congrArg (fun xs : List ℕ => (xs.prod : ℝ)) hof
  simpa only [Nat.cast_list_prod, List.map_ofFn, List.prod_ofFn] using hprod

/-- All ordered lists, including empty carriers, embed with every slot retained. -/
def tupleEmbedding (P : Finset ℕ) (r : ℕ) :
    (secondFunctionalMotherTuples P r) ↪ (Fin r → P) where
  toFun l j := ⟨coordinates r l.val j, by
    have ht := (secondFunctionalMother_tuple_mem P r l.val).mp l.property
    have hi : j.val < l.val.length := by rw [ht.1]; exact j.isLt
    change l.val.getD j.val 0 ∈ P
    rw [List.getD_eq_getElem _ _ hi]
    exact ht.2.2 _ (List.getElem_mem hi)⟩
  inj' := by
    intro l l' h
    apply Subtype.ext
    apply HighNonunit.list_eq_of_getD
      ((secondFunctionalMother_tuple_mem P r l.val).mp l.property).1
      ((secondFunctionalMother_tuple_mem P r l'.val).mp l'.property).1
    funext j
    exact congrArg Subtype.val (congr_fun h j)

theorem tupleEmbedding_weight (P : Finset ℕ) (r : ℕ)
    (l : secondFunctionalMotherTuples P r) :
    (∏ j : Fin r, 1 / (((tupleEmbedding P r l) j).val : ℝ)) = 1 / (l.val.prod : ℝ) := by
  change (∏ j : Fin r, 1 / (coordinates r l.val j : ℝ)) = _
  rw [prod_div_distrib, prod_const_one,
    coordinates_product ((secondFunctionalMother_tuple_mem P r l.val).mp l.property).1]

/-- Finite Fubini on the full labelled cube; no estimate for primes is used. -/
theorem tuple_reciprocal_le_cube (P : Finset ℕ) (r : ℕ) :
    (∑ l ∈ secondFunctionalMotherTuples P r, 1 / (l.prod : ℝ)) ≤
      (∑ p ∈ P, 1 / (p : ℝ)) ^ r := by
  let E := tupleEmbedding P r
  let w : (Fin r → P) → ℝ := fun t => ∏ j : Fin r, 1 / ((t j).val : ℝ)
  have hsub : (∑ t ∈ univ.image E, w t) ≤ ∑ t : Fin r → P, w t := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
    intro t _ _
    exact prod_nonneg (fun j _ => by positivity)
  have he : (∑ t ∈ univ.image E, w t) =
      ∑ l ∈ secondFunctionalMotherTuples P r, 1 / (l.prod : ℝ) := by
    rw [sum_image (fun a _ b _ h => E.injective h)]
    dsimp only [E, w]
    simp_rw [tupleEmbedding_weight]
    exact sum_coe_sort (secondFunctionalMotherTuples P r)
      (fun l : List ℕ => 1 / (l.prod : ℝ))
  rw [he] at hsub
  have hcube : (∑ t : Fin r → P, w t) = (∑ p ∈ P, 1 / (p : ℝ)) ^ r := by
    change (∑ t : Fin r → P, ∏ j : Fin r, 1 / ((t j).val : ℝ)) = _
    rw [← Fintype.prod_sum (fun (_ : Fin r) (p : P) => 1 / (p.val : ℝ))]
    simp only [prod_const, card_univ, Fintype.card_fin]
    rw [sum_coe_sort P (fun p : ℕ => 1 / (p : ℝ))]
  exact hsub.trans_eq hcube

theorem tuple_reciprocal_le_power (P : Finset ℕ) (r : ℕ) {H : ℝ}
    (hH : (∑ p ∈ P, 1 / (p : ℝ)) ≤ H) :
    (∑ l ∈ secondFunctionalMotherTuples P r, 1 / (l.prod : ℝ)) ≤ H ^ r := by
  exact (tuple_reciprocal_le_cube P r).trans
    (pow_le_pow_left₀ (sum_nonneg (fun _ _ => by positivity)) hH r)

/-- A uniform elementary budget when the actual prime window is below N. -/
theorem reciprocal_le_one_add_log (P : Finset ℕ) (N : ℕ)
    (hP : P ⊆ Icc 1 N) : (∑ p ∈ P, 1 / (p : ℝ)) ≤ 1 + Real.log N := by
  calc
    _ ≤ ∑ p ∈ Icc 1 N, 1 / (p : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hP (fun _ _ _ => by positivity)
    _ = (harmonic N : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    _ ≤ _ := harmonic_le_one_add_log N

/-- The full word dictionary, before any arity or multiplicity is enlarged. -/
def wordBudget (H : ℝ) : ℝ :=
  (secondFunctionalMotherPrefixIndices.map fun i =>
    ((secondFunctionalMotherGammaWords i).map (fun cs => H ^ cs.length)).sum).sum

theorem wordBudget_eq (H : ℝ) :
    wordBudget H = 2 * H ^ 2 + 14 * H ^ 3 + 4 * H ^ 4 + H ^ 5 + H ^ 6 := by
  norm_num [wordBudget, secondFunctionalMotherPrefixIndices, secondFunctionalMotherGammaWords]
  <;> ring

theorem wordBudget_le_sixth {H : ℝ} (hH : 1 ≤ H) : wordBudget H ≤ 22 * H ^ 6 := by
  rw [wordBudget_eq]
  have h2 := pow_le_pow_right₀ hH (by norm_num : (2 : ℕ) ≤ 6)
  have h3 := pow_le_pow_right₀ hH (by norm_num : (3 : ℕ) ≤ 6)
  have h4 := pow_le_pow_right₀ hH (by norm_num : (4 : ℕ) ≤ 6)
  have h5 := pow_le_pow_right₀ hH (by norm_num : (5 : ℕ) ≤ 6)
  linarith

end
end ImbalancedChen.P2EnhancedOrderedReciprocalBudget
