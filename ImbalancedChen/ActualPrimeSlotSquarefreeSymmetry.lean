import ImbalancedChen.ActualFrozenSlotCoefficientRegrouping
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The literal Mobius diagonal and a repeated-label factorial orbit

The Mobius function is evaluated at the original full rough product. Its
vanishing removes repeated-prime tuples exactly before any absolute value
is taken. For a single repeated fine label, the complete product fibre of
a distinct-prime representative is precisely its permutation orbit, of
size m!. This is the original repeated-label factorial, independently of
the three later group normalizations.

The original first-exit support is not replaced by this box. Identifying
all its ordered fine-label blocks and their full scalar remains a separate
source dictionary; no distribution or arithmetic mean is asserted here.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

/-- Unique factorization also gives the converse of the prime-vector
squarefreeness lemma. It applies to the full original list, including nil. -/
theorem actualPrimeVector_nodup_of_squarefree (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hsquarefree : Squarefree input.prod) :
    input.Nodup := by
  have hperm := Nat.primeFactorsList_unique (rfl : input.prod = input.prod) hprime
  exact hperm.nodup_iff.mpr
    ((Nat.squarefree_iff_nodup_primeFactorsList hsquarefree.ne_zero).mp hsquarefree)

/-- A repeated rough prime has zero literal Mobius coefficient. This is
not a redefinition of the full-integer normalized convolution coefficient. -/
theorem actualPrimeVector_moebius_eq_zero_of_not_nodup (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hnodup : ¬input.Nodup) :
    ArithmeticFunction.moebius input.prod = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hsquarefree
  exact hnodup (actualPrimeVector_nodup_of_squarefree input hprime hsquarefree)

theorem actualPrimeVector_moebius_eq_sign (input : List ℕ)
    (hprime : ∀ p ∈ input, Nat.Prime p) (hnodup : input.Nodup) :
    ArithmeticFunction.moebius input.prod = (-1 : ℤ) ^ input.length := by
  have hperm := Nat.primeFactorsList_unique (rfl : input.prod = input.prod) hprime
  rw [ArithmeticFunction.moebius_apply_of_squarefree
    (actualPrimeVector_squarefree input hprime hnodup), ArithmeticFunction.cardFactors_apply,
    ← hperm.length_eq]

/-- The entire signed full-box sum has exactly its original distinct-prime
part. Nothing about a positive majorant or a post-absolute-value sum is
used to discard the diagonal. -/
theorem actualPrimeTuple_moebius_sum_eq_distinct_sign
    (T : Finset (List ℕ)) (m : ℕ)
    (hlen : ∀ ps ∈ T, ps.length = m)
    (hprime : ∀ ps ∈ T, ∀ p ∈ ps, Nat.Prime p) (H : ℕ → ℝ) :
    (∑ ps ∈ T, (ArithmeticFunction.moebius ps.prod : ℝ) * H ps.prod) =
      ∑ ps ∈ T.filter List.Nodup, (-1 : ℝ) ^ m * H ps.prod := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ps hps
  by_cases hnodup : ps.Nodup
  · rw [if_pos hnodup]
    have hsign : (ArithmeticFunction.moebius ps.prod : ℝ) = (-1 : ℝ) ^ m := by
      exact_mod_cast (hlen ps hps ▸ actualPrimeVector_moebius_eq_sign ps (hprime ps hps) hnodup)
    rw [hsign]
  · rw [if_neg hnodup, actualPrimeVector_moebius_eq_zero_of_not_nodup ps (hprime ps hps) hnodup]
    simp

/-- A repeated fine-label block is the complete ordered Cartesian power
of its own prime set, with no injectivity requirement on its values. -/
theorem mem_actualPrimeSlotBox_replicate (B : Finset ℕ) (m : ℕ) (ps : List ℕ) :
    ps ∈ actualPrimeSlotBox (fun _ : Unit => B) (List.replicate m ()) ↔
      ps.length = m ∧ ∀ q ∈ ps, q ∈ B := by
  induction m generalizing ps with
  | zero => simp [actualPrimeSlotBox]
  | succ m ih =>
      cases ps with
      | nil => simp [actualPrimeSlotBox, List.replicate_succ]
      | cons q qs =>
          constructor
          · intro hps
            obtain ⟨⟨r, rs⟩, hmem, heq⟩ := Finset.mem_image.mp hps
            obtain ⟨hr, hrs⟩ := Finset.mem_product.mp hmem
            obtain ⟨rfl, rfl⟩ := List.cons.inj heq
            obtain ⟨hlen, hqs⟩ := (ih qs).mp hrs
            exact ⟨by simpa only [List.length_cons, hlen],
              fun s hs => (List.mem_cons.mp hs).elim (fun h => h.symm ▸ hr) (hqs s)⟩
          · rintro ⟨hlen, hmem⟩
            apply Finset.mem_image.mpr
            refine ⟨(q, qs), Finset.mem_product.mpr ⟨hmem q (by simp), ?_⟩, rfl⟩
            apply (ih qs).mpr
            exact ⟨by simpa only [List.length_cons, Nat.succ.injEq] using hlen,
              fun r hr => hmem r (List.mem_cons_of_mem q hr)⟩

/-- Every squarefree product in one repeated-label block has exactly the
original m! slot assignments. No three-group factorial appears here. -/
theorem actualPrimeSlotBox_replicate_coefficient (B : Finset ℕ) (ps : List ℕ)
    (hBprime : ∀ q ∈ B, Nat.Prime q) (hps : ∀ q ∈ ps, q ∈ B) (hnodup : ps.Nodup) :
    actualPrimeTupleCoefficient
        (actualPrimeSlotBox (fun _ : Unit => B) (List.replicate ps.length ())) ps.prod =
      ps.length.factorial := by
  have hprime : ∀ q ∈ ps, Nat.Prime q := fun q hq => hBprime q (hps q hq)
  have hfibre :
      (actualPrimeSlotBox (fun _ : Unit => B) (List.replicate ps.length ())).filter
        (fun qs => qs.prod = ps.prod) = ps.permutations.toFinset := by
    apply Finset.ext
    intro qs
    constructor
    · intro hqs
      obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp hqs
      obtain ⟨_, hB⟩ := (mem_actualPrimeSlotBox_replicate B ps.length qs).mp hbox
      have hperm := (Nat.primeFactorsList_unique hprod
        (fun q hq => hBprime q (hB q hq))).trans
          (Nat.primeFactorsList_unique (rfl : ps.prod = ps.prod) hprime).symm
      exact List.mem_toFinset.mpr (List.mem_permutations.mpr hperm)
    · intro hqs
      have hperm := List.mem_permutations.mp (List.mem_toFinset.mp hqs)
      refine Finset.mem_filter.mpr ⟨(mem_actualPrimeSlotBox_replicate B ps.length qs).mpr ?_,
        hperm.prod_eq⟩
      exact ⟨hperm.length_eq, fun q hq => hps q (hperm.mem_iff.mp hq)⟩
  unfold actualPrimeTupleCoefficient
  rw [hfibre, List.toFinset_card_of_nodup (List.nodup_permutations ps hnodup),
    List.length_permutations]

/-- Dividing by the original repeated-label factorial gives its squarefree
sorted-product coefficient one, before any later three-group regrouping. -/
theorem actualPrimeSlotBox_replicate_normalized_eq_one (B : Finset ℕ) (ps : List ℕ)
    (hBprime : ∀ q ∈ B, Nat.Prime q) (hps : ∀ q ∈ ps, q ∈ B) (hnodup : ps.Nodup) :
    actualNormalizedPrimeTupleCoefficient
        (actualPrimeSlotBox (fun _ : Unit => B) (List.replicate ps.length ())) ps.length ps.prod = 1 := by
  unfold actualNormalizedPrimeTupleCoefficient
  rw [actualPrimeSlotBox_replicate_coefficient B ps hBprime hps hnodup]
  exact div_self (by exact_mod_cast Nat.factorial_ne_zero ps.length)

end

end ImbalancedChen
