import ImbalancedChen.P3HBRoughLiteralMoment

/-!
P3.6, frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §§2,4: the ACTUAL strict rough HB projector
eliminates the complete-product=T diagonal for even T once z >= 2.

This is a separate original INTEGER HB source, not a relabelled prime tuple.
The real cutoff y, original ordered factor positions, roles, and
the signed +3,-3,+1 coefficients are unchanged. The proof is uniform in
the number of original rough groups; it does not infer any missing
whole-box or source-compiler admission.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED. This does not control
off-target shifted divisors, the mean, Fourier tails, marked even
multipliers, final causal rho/Q, or any external medium estimate.
-/

namespace ImbalancedChen.P3HBEvenRoughTarget

noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.Part3
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords
open ImbalancedChen.P5Z.ActualRoughHeathBrownWords
open ImbalancedChen.P3HBRoughLiteralMoment

/-- The literal strict rough projector forbids the prime 2 at the closed
cutoff z >= 2. An even complete product is therefore annihilated. -/
theorem even_target_rough_slot_zero
    (z : ℝ) (T : ℕ) (hz : (2 : ℝ) ≤ z) (hT : Even T) :
    roughOneSlot z T = 0 := by
  by_contra hn
  have hrough := roughOneSlot_support z T hn
  have htwo : (2 : ℝ) > z :=
    hrough 2 Nat.prime_two (even_iff_two_dvd.mp hT)
  exact (not_lt_of_ge hz) htwo

/-- All original HB group projectors are multiplied, without deleting
units or identifying repeated positions. For ANY number of groups,
the complete product T even forces the original projector product zero.
No upper bound on the number of groups is needed for this exact identity. -/
theorem original_group_projectors_target_zero
    (z : ℝ) (ns : List ℕ) (T : ℕ)
    (hz : (2 : ℝ) ≤ z) (hT : Even T) (hprod : ns.prod = T) :
    (ns.map (roughOneSlot z)).prod = 0 := by
  have hz0 : 0 ≤ z := by linarith
  rw [← roughOne_list_prod (z := z) hz0 ns, hprod]
  exact even_target_rough_slot_zero z T hz hT

/-- The ORIGINAL literal HB word at full product T includes the strict
rough projector on every one of its 2(j+1) positional slots. Thus each
ordered occurrence is zero, independently of y and of its Mobius sign.
The list factor fibre itself is not silently discarded. -/
theorem literal_occurrence_target_zero
    (z y : ℝ) (j T : ℕ)
    (hz : (2 : ℝ) ≤ z) (hT : Even T)
    (ps : List ℕ)
    (hps : ps ∈ factorTuples (2 * (j + 1)) T) :
    roughTupleWeight z y (roles j) ps = 0 := by
  have hz0 : 0 ≤ z := by linarith
  rw [actual_word_mask (z := z) hz0 y j T ps hps,
      even_target_rough_slot_zero z T hz hT]
  simp

/-- The actual complete signed order-three rough-HB expansion has NO
exact-even-target fibre, with the original binomial signs +3,-3,+1,
one log slot per word, and all ordered occurrences retained. This is
a literal source-level finite equality, not an analytic PP estimate. -/
theorem actual_three_signed_target_zero
    (z y : ℝ) (T : ℕ)
    (hz : (2 : ℝ) ≤ z) (hT : Even T) :
    (∑ j ∈ Finset.range 3,
      (((-1 : ℝ) ^ j * (Nat.choose 3 (j + 1) : ℝ) : ℝ) : ℂ) *
        ∑ ps ∈ factorTuples (2 * (j + 1)) T,
          roughTupleWeight z y (roles j) ps) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hjzero :
      (∑ ps ∈ factorTuples (2 * (j + 1)) T,
        roughTupleWeight z y (roles j) ps) = 0 := by
    apply Finset.sum_eq_zero
    intro ps hps
    exact literal_occurrence_target_zero z y j T hz hT ps hps
  simp [hjzero]

end
end ImbalancedChen.P3HBEvenRoughTarget
