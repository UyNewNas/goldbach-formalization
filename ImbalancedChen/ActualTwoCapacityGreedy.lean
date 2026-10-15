import MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Nodup

/-!
# The actual deterministic two-capacity allocation

The input is the full original list of prime slots.  Its `PrefixSquareBound`
is precisely the defining inequality of the manuscript's D-well support,
not a condition on a replacement remainder.  We reuse the pinned numerical
allocation core, including its append-fit theorem and exact prefix identity.

The policy implemented below always chooses the left bin when it fits.
The right-bin capacity is a theorem, not an additional test or a supplied
allocation.  The natural factors retain the original slots.  In the
capacity-below-one repair the policy is rerun on the full original list.
No estimate for the three analytic monomials or distribution mean is claimed.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical
open MathlibNt.SieveTheory.LiLiuPrereqWFBoxAllocation

/-- One deterministic step: prefer the left bin, including equality. -/
def actualTwoCapacityStep {α : Type*} (weight : α → ℝ) (A : ℝ)
    (bins : List α × List α) (p : α) : List α × List α :=
  if (bins.1.map weight).prod * weight p ≤ A then
    (bins.1 ++ [p], bins.2)
  else (bins.1, bins.2 ++ [p])

/-- Process every original occurrence in order; the initial products are one. -/
def actualTwoCapacityGreedy {α : Type*} (weight : α → ℝ) (A : ℝ)
    (input : List α) : List α × List α :=
  input.foldl (actualTwoCapacityStep weight A) ([], [])

theorem actualTwoCapacityGreedy_append {α : Type*} (weight : α → ℝ)
    (A : ℝ) (input : List α) (p : α) :
    actualTwoCapacityGreedy weight A (input ++ [p]) =
      actualTwoCapacityStep weight A (actualTwoCapacityGreedy weight A input) p := by
  simp only [actualTwoCapacityGreedy, List.foldl_append, List.foldl_cons,
    List.foldl_nil]

/-- The numerical provider's real append-fit theorem validates this particular
prefer-left policy, rather than merely choosing some bounded partition. -/
theorem actualTwoCapacityGreedy_correct {α : Type*} (weight : α → ℝ)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (input : List α)
    (hfull : PrefixSquareBound weight (A * B) input) :
    BoxPartition (actualTwoCapacityGreedy weight A input).1
      (actualTwoCapacityGreedy weight A input).2 input ∧
      (((actualTwoCapacityGreedy weight A input).1).map weight).prod ≤ A ∧
      (((actualTwoCapacityGreedy weight A input).2).map weight).prod ≤ B := by
  induction input using List.reverseRecOn with
  | nil => exact ⟨BoxPartition.nil, by simpa [actualTwoCapacityGreedy] using hA,
      by simpa [actualTwoCapacityGreedy] using hB⟩
  | append_singleton input p ih =>
      obtain ⟨hprefix, hlast⟩ :=
        (prefixSquareBound_append_singleton_iff weight (A * B) input p).mp hfull
      obtain ⟨hpart, hleft, hright⟩ := ih hprefix
      rw [← hpart.prod_eq weight] at hlast
      have hfits := append_fits_one_box
        (zero_le_one.trans hA) (zero_le_one.trans hB) hlast
      rw [actualTwoCapacityGreedy_append]
      unfold actualTwoCapacityStep
      split_ifs with hleftFits
      · exact ⟨hpart.left p, by simpa using hleftFits, hright⟩
      · exact ⟨hpart.right p, hleft, by simpa using hfits.resolve_left hleftFits⟩

/-- D-well uses the original full vector's exact indexed prefix-square tests. -/
abbrev actualDwellSupport (D : ℝ) (input : List ℕ) : Prop :=
  PrefixSquareBound (fun p : ℕ => (p : ℝ)) D input

/-- The pinned parity-sensitive original cubic support pays every square test;
the head restriction and decreasing order are fields of actual admissibility. -/
theorem actualDwellSupport_of_admissible {upper : Bool} {D : ℝ}
    {input : List ℕ}
    (h : MathlibNt.SieveTheory.LiLiuPrereqWFAdmissibility.Admissible upper
      (fun p : ℕ => (p : ℝ)) D input) : actualDwellSupport D input :=
  h.prefixSquareBound

theorem actualNatList_cast_prod (input : List ℕ) :
    (input.map (fun p : ℕ => (p : ℝ))).prod = (input.prod : ℝ) := by
  induction input with
  | nil => simp
  | cons p input ih =>
      rw [List.map_cons, List.prod_cons, List.prod_cons, Nat.cast_mul, ih]

/-- The two complementary natural factors are products of the allocated
original subsequences; no real product is rounded to an integer. -/
def actualTwoCapacityFactors (A : ℝ) (input : List ℕ) : ℕ × ℕ :=
  ((actualTwoCapacityGreedy (fun p : ℕ => (p : ℝ)) A input).1.prod,
    (actualTwoCapacityGreedy (fun p : ℕ => (p : ℝ)) A input).2.prod)

theorem actualTwoCapacityFactors_correct {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (input : List ℕ) (hfull : actualDwellSupport (A * B) input) :
    (actualTwoCapacityFactors A input).1 * (actualTwoCapacityFactors A input).2 =
      input.prod ∧
      ((actualTwoCapacityFactors A input).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A input).2 : ℝ) ≤ B := by
  obtain ⟨hpart, hleft, hright⟩ :=
    actualTwoCapacityGreedy_correct (fun p : ℕ => (p : ℝ)) hA hB input hfull
  refine ⟨?_, ?_, ?_⟩
  · exact (by simpa only [actualTwoCapacityFactors, List.prod_append] using hpart.perm.prod_eq)
  · simpa only [actualTwoCapacityFactors, actualNatList_cast_prod] using hleft
  · simpa only [actualTwoCapacityFactors, actualNatList_cast_prod] using hright

/-- Every side preserves the original label condition, including primality,
target exclusion, or a sieve cutoff chosen by the actual caller. -/
theorem actualTwoCapacityGreedy_labels {α : Type*} (weight : α → ℝ)
    {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) (input : List α)
    (hfull : PrefixSquareBound weight (A * B) input) (P : α → Prop)
    (hlabels : ∀ p ∈ input, P p) :
    (∀ p ∈ (actualTwoCapacityGreedy weight A input).1, P p) ∧
      (∀ p ∈ (actualTwoCapacityGreedy weight A input).2, P p) := by
  have hpart := (actualTwoCapacityGreedy_correct weight hA hB input hfull).1
  exact ⟨fun p hp => hlabels p (hpart.sublists.1.subset hp),
    fun p hp => hlabels p (hpart.sublists.2.subset hp)⟩

/-- Distinct original primes give coprime complementary factors.  Occurrence
preservation alone would not justify this statement for repeated primes. -/
theorem actualTwoCapacityFactors_coprime {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B)
    (input : List ℕ) (hfull : actualDwellSupport (A * B) input)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hnodup : input.Nodup) :
    Nat.Coprime (actualTwoCapacityFactors A input).1
      (actualTwoCapacityFactors A input).2 := by
  have hpart := (actualTwoCapacityGreedy_correct
    (fun p : ℕ => (p : ℝ)) hA hB input hfull).1
  have hdisj := List.disjoint_of_nodup_append (hpart.perm.nodup_iff.mpr hnodup)
  apply Nat.coprime_list_prod_left_iff.mpr
  intro p hp
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hq
  apply (Nat.coprime_primes
    (hprime p (hpart.sublists.1.subset hp))
    (hprime q (hpart.sublists.2.subset hq))).mpr
  intro hpq
  exact (List.disjoint_left.mp hdisj hp) (hpq.symm ▸ hq)

/-- The capacity-below-one repair is performed on the entire original vector.
The final right factor need not equal the formerly selected product `b₀`.
The only square support input is the original D-well predicate. -/
theorem actualDwell_full_vector_repair {D A : ℝ} (hA : 1 ≤ A)
    (hB : 1 ≤ D / A) (input : List ℕ) (hfull : actualDwellSupport D input)
    (b₀ : ℕ) (hb₀ : 0 < b₀) (hsmall : D / (A * b₀) < 1) :
    D / A < (b₀ : ℝ) ∧
      (actualTwoCapacityFactors A input).1 * (actualTwoCapacityFactors A input).2 =
        input.prod ∧
      ((actualTwoCapacityFactors A input).1 : ℝ) ≤ A ∧
      ((actualTwoCapacityFactors A input).2 : ℝ) ≤ D / A := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hbpos : (0 : ℝ) < b₀ := by exact_mod_cast hb₀
  have hsplit : A * (D / A) = D := by
    simpa only [mul_comm] using (div_mul_cancel₀ D hApos.ne')
  have hbudget : actualDwellSupport (A * (D / A)) input := by
    simpa only [hsplit] using hfull
  refine ⟨?_, actualTwoCapacityFactors_correct hA hB input hbudget⟩
  apply (div_lt_iff₀ hApos).mpr
  have hD : D < A * (b₀ : ℝ) := (div_lt_one (mul_pos hApos hbpos)).mp hsmall
  simpa only [mul_comm] using hD

end

end ImbalancedChen
