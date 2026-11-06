import ImbalancedChen.P3ActualFineLabelThreeGammaTensor
import ImbalancedChen.ActualFrozenSelectedPairSlots
import Mathlib.Data.Nat.Choose.Basic

/-!
P3.6: split occurrences of an ORIGINAL repeated fine-prime label across
three groups. SOURCE_ONLY, UNCOMPILED, KERNEL_UNVERIFIED.

Unlike a partition of whole (label,multiplicity) blocks, this allows
one label's m occurrences to be split as m = m₀ + m₁ + m₂.
The full factorial remains m!, while each normalized gamma uses its
OWN group factorial mⱼ!. Zero-count blocks are retained (0! = 1).
The true fixed whole-box slot assignment must still supply its concrete
per-label group counts. No source dictionary, rho or discrepancy is assumed
proved by these finite identities.
-/

namespace ImbalancedChen.P3ActualSplitLabelMultinomial
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3ActualFineLabelThreeGammaTensor
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- All original labels remain in their given order. Only their
multiplicities are replaced by the number of occurrences in group j. -/
def splitBlocks (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (j : Fin 3) : List (ℕ × ℕ) :=
  blocks.map (fun b => (b.1, size b.1 j))

/-- Commuting the three front segments through three tails counts every
position, even if some label values or prime values coincide. -/
private theorem triple_shuffle {α : Type*}
    (a b c A B C : List α) :
    ((a ++ b ++ c) ++ (A ++ B ++ C)).Perm
      ((a ++ A) ++ (b ++ B) ++ (c ++ C)) := by
  calc
    ((a ++ b ++ c) ++ (A ++ B ++ C)).Perm
        (a ++ b ++ A ++ c ++ B ++ C) := by
      simpa only [List.append_assoc] using
        ((List.perm_append_comm (l₁ := c) (l₂ := A)).append_left (a ++ b)).append_right (B ++ C)
    _ ~ (a ++ A ++ b ++ c ++ B ++ C) := by
      simpa only [List.append_assoc] using
        ((List.perm_append_comm (l₁ := b) (l₂ := A)).append_left a).append_right (c ++ B ++ C)
    _ ~ (a ++ A ++ b ++ B ++ c ++ C) := by
      simpa only [List.append_assoc] using
        ((List.perm_append_comm (l₁ := c) (l₂ := B)).append_left (a ++ A ++ b)).append_right C
    _ = ((a ++ A) ++ (b ++ B) ++ (c ++ C)) := by
      simp only [List.append_assoc]

/-- Literal expansion of every original repeated-label block into its
three occurrence subblocks. No hperm premise is postulated; it follows
by induction from the elementary per-label count identity. -/
theorem split_blocks_word_perm
    (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (hs : ∀ b ∈ blocks,
      b.2 = size b.1 0 + size b.1 1 + size b.1 2) :
    (actualPrimeLabelBlocksWord blocks).Perm
      (actualPrimeLabelBlocksWord (splitBlocks blocks size 0) ++
       actualPrimeLabelBlocksWord (splitBlocks blocks size 1) ++
       actualPrimeLabelBlocksWord (splitBlocks blocks size 2)) := by
  induction blocks with
  | nil =>
      simp [actualPrimeLabelBlocksWord, splitBlocks]
  | cons hd tl ih =>
      rcases hd with ⟨i, m⟩
      have hm : m = size i 0 + size i 1 + size i 2 :=
        hs (i, m) (by simp)
      have htl : ∀ b ∈ tl,
          b.2 = size b.1 0 + size b.1 1 + size b.1 2 := by
        intro b hb
        exact hs b (List.mem_cons_of_mem (i, m) hb)
      have hih := ih htl
      let a := List.replicate (size i 0) i
      let b := List.replicate (size i 1) i
      let c := List.replicate (size i 2) i
      have hrep : List.replicate m i = a ++ b ++ c := by
        dsimp [a, b, c]
        rw [hm]
        simp only [List.replicate_add, List.append_assoc]
      change (List.replicate m i ++ actualPrimeLabelBlocksWord tl).Perm
        ((a ++ actualPrimeLabelBlocksWord (splitBlocks tl size 0)) ++
         (b ++ actualPrimeLabelBlocksWord (splitBlocks tl size 1)) ++
         (c ++ actualPrimeLabelBlocksWord (splitBlocks tl size 2)))
      rw [hrep]
      exact (hih.append_left (a ++ b ++ c)).trans
        (triple_shuffle a b c
          (actualPrimeLabelBlocksWord (splitBlocks tl size 0))
          (actualPrimeLabelBlocksWord (splitBlocks tl size 1))
          (actualPrimeLabelBlocksWord (splitBlocks tl size 2)))

/-- Elementary multinomial denominator payment for a single repeated
label, proved using the pinned binomial factorial divisibility lemma. -/
theorem factorial_three_le (a b c : ℕ) :
    a.factorial * b.factorial * c.factorial ≤ (a + b + c).factorial := by
  have h₁ : a.factorial * b.factorial ≤ (a + b).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add a b)
  have h₂ : (a + b).factorial * c.factorial ≤ (a + b + c).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _)
      (Nat.factorial_mul_factorial_dvd_factorial_add (a + b) c)
  exact (Nat.mul_le_mul_right c.factorial h₁).trans h₂

/-- A split never enlarges the ORIGINAL reciprocal label-factorial scalar.
Unlike using a total-slot factorial, this inequality is computed label
by label, keeping the exact original full-label denominator. -/
theorem split_factorial_le
    (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (hs : ∀ b ∈ blocks,
      b.2 = size b.1 0 + size b.1 1 + size b.1 2) :
    actualPrimeLabelBlocksFactorial (splitBlocks blocks size 0) *
      actualPrimeLabelBlocksFactorial (splitBlocks blocks size 1) *
      actualPrimeLabelBlocksFactorial (splitBlocks blocks size 2) ≤
    actualPrimeLabelBlocksFactorial blocks := by
  induction blocks with
  | nil => simp [splitBlocks, actualPrimeLabelBlocksFactorial]
  | cons hd tl ih =>
      rcases hd with ⟨i, m⟩
      have hm : m = size i 0 + size i 1 + size i 2 :=
        hs (i, m) (by simp)
      have htl : ∀ b ∈ tl,
          b.2 = size b.1 0 + size b.1 1 + size b.1 2 := by
        intro b hb
        exact hs b (List.mem_cons_of_mem (i, m) hb)
      have hlocal : (size i 0).factorial * (size i 1).factorial *
          (size i 2).factorial ≤ m.factorial := by
        rw [hm]
        exact factorial_three_le _ _ _
      have hrest := ih htl
      change ((size i 0).factorial *
          actualPrimeLabelBlocksFactorial (splitBlocks tl size 0)) *
        ((size i 1).factorial *
          actualPrimeLabelBlocksFactorial (splitBlocks tl size 1)) *
        ((size i 2).factorial *
          actualPrimeLabelBlocksFactorial (splitBlocks tl size 2)) ≤
        m.factorial * actualPrimeLabelBlocksFactorial tl
      calc
        _ = ((size i 0).factorial * (size i 1).factorial *
               (size i 2).factorial) *
            (actualPrimeLabelBlocksFactorial (splitBlocks tl size 0) *
             actualPrimeLabelBlocksFactorial (splitBlocks tl size 1) *
             actualPrimeLabelBlocksFactorial (splitBlocks tl size 2)) := by ring
        _ ≤ m.factorial * actualPrimeLabelBlocksFactorial tl :=
          Nat.mul_le_mul hlocal hrest

/-- The exact restoring scalar is nonnegative and at most one. No extra
coefficient bound on each full-product fibre is inferred from this fact. -/
theorem split_factorial_ratio_mem_Icc
    (blocks : List (ℕ × ℕ)) (size : ℕ → Fin 3 → ℕ)
    (hs : ∀ b ∈ blocks,
      b.2 = size b.1 0 + size b.1 1 + size b.1 2) :
    (((actualPrimeLabelBlocksFactorial (splitBlocks blocks size 0) : ℝ) *
       (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 1) : ℝ) *
       (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 2) : ℝ)) /
       (actualPrimeLabelBlocksFactorial blocks : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : (0 : ℝ) < (actualPrimeLabelBlocksFactorial blocks : ℝ) := by
    exact_mod_cast actualPrimeLabelBlocksFactorial_pos blocks
  have hnat := split_factorial_le blocks size hs
  have hreal :
      (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 0) : ℝ) *
      (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 1) : ℝ) *
      (actualPrimeLabelBlocksFactorial (splitBlocks blocks size 2) : ℝ) ≤
      (actualPrimeLabelBlocksFactorial blocks : ℝ) := by
    exact_mod_cast hnat
  exact ⟨div_nonneg (by positivity) hd.le,
    (div_le_iff₀ hd).mpr (by simpa only [one_mul] using hreal)⟩

/-- The ORIGINAL signed fine-label prime tensor for an arbitrary
per-label three-way occurrence split, including split repeated labels,
zero-count groups and exactly the M₀M₁M₂/M_all correction. -/
theorem actual_split_three_gamma_tensor
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (size : ℕ → Fin 3 → ℕ)
    (hs : ∀ b ∈ blocks,
      b.2 = size b.1 0 + size b.1 1 + size b.1 2)
    (c : ℝ) (H : ℕ → ℝ) :
    let B := actualPrimeFineLabelFinset N τ
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let T₀ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₀)
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    (c / (actualPrimeLabelBlocksFactorial blocks : ℝ)) *
      (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord blocks),
        H ps.prod) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℝ) *
       (actualPrimeLabelBlocksFactorial g₁ : ℝ) *
       (actualPrimeLabelBlocksFactorial g₂ : ℝ)) /
       (actualPrimeLabelBlocksFactorial blocks : ℝ))) *
      (∑ a ∈ T₀.image List.prod, ∑ b ∈ T₁.image List.prod,
        ∑ d ∈ T₂.image List.prod,
          gamma B g₀ a * gamma B g₁ b * gamma B g₂ d *
            H (a * b * d)) := by
  exact actual_label_three_gamma_tensor
    (actualPrimeFineLabelFinset N τ) blocks
    (splitBlocks blocks size 0) (splitBlocks blocks size 1)
    (splitBlocks blocks size 2)
    (split_blocks_word_perm blocks size hs) c H

/-- An actual whole-box selected-pair partition conserves each literal
label occurrence: its three group counts add to the ORIGINAL slot count.
This does not yet recover the original block multiplicities. -/
theorem frozen_occurrence_count_sum
    (D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ) (i : ℕ) :
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    (p 0 :: p 1 :: p 2 :: tail).count i =
      groups.1.count i + groups.2.1.count i + groups.2.2.count i := by
  have h := (actualFrozenSelectedPairSlots_perm D A yz upper p tail).count_eq i
  simpa only [List.count_append, Nat.add_assoc] using h.symm

end
end ImbalancedChen.P3ActualSplitLabelMultinomial
