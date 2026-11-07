import Mathlib
import ImbalancedChen.Part3BrunFactorialRecurrenceE1

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The missing elementary pair count for B2. A pair (p,A), with p in the
q-surviving prime alphabet and A an r-subset omitting p, is bijective
to (B,p), where B=A union {p} is an (r+1)-subset and p in B. Every B
is counted r+1 times. No final rough theorem or analytic input occurs.
-/

namespace ImbalancedChen.Part3.BrunSymmetricPairCount

open Finset
open scoped BigOperators
open ImbalancedChen.Part3.TwoLongBrunLiteralDensity
open ImbalancedChen.Part3.BrunFactorialRecurrenceE1

noncomputable section

def elementaryMass (R : Finset ℕ) (w : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ A ∈ R.powersetCard r, ∏ p ∈ A, w p

/-- Exact finite double count, before any inequality or q-deletion. -/
theorem elementaryMass_pair_count
    (R : Finset ℕ) (w : ℕ → ℝ) (r : ℕ) :
    ((r + 1 : ℕ) : ℝ) * elementaryMass R w (r + 1) =
      ∑ p ∈ R, w p * elementaryMass (R.erase p) w r := by
  classical
  let L := R.sigma (fun p => (R.erase p).powersetCard r)
  let U := (R.powersetCard (r + 1)).sigma (fun B => B)
  have hbij :
      (∑ t ∈ L, w t.1 * ∏ p ∈ t.2, w p) =
        ∑ u ∈ U, ∏ p ∈ u.1, w p := by
    apply Finset.sum_bij'
      (fun t _ => (⟨insert t.1 t.2, t.1⟩ : Σ B : Finset ℕ, ℕ))
      (fun u _ => (⟨u.2, u.1.erase u.2⟩ : Σ p : ℕ, Finset ℕ))
    · intro t ht
      obtain ⟨hp, hA⟩ := Finset.mem_sigma.mp ht
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hA
      have hnot : t.1 ∉ t.2 := by
        intro hmem
        exact (Finset.not_mem_erase t.1 R) (hsub hmem)
      have hsubset : insert t.1 t.2 ⊆ R := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hp
        · exact (Finset.erase_subset _ _) (hsub hx)
      have hcard' : (insert t.1 t.2).card = r + 1 := by
        simp [Finset.card_insert_of_not_mem hnot, hcard]
      exact Finset.mem_sigma.mpr
        ⟨Finset.mem_powersetCard.mpr ⟨hsubset, hcard'⟩,
          Finset.mem_insert_self _ _⟩
    · intro u hu
      obtain ⟨hB, hpB⟩ := Finset.mem_sigma.mp hu
      obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hB
      have hp : u.2 ∈ R := hsub hpB
      have herase : u.1.erase u.2 ⊆ R.erase u.2 := by
        intro x hx
        have hx' := Finset.mem_erase.mp hx
        exact Finset.mem_erase.mpr ⟨hx'.1, hsub hx'.2⟩
      have hcard' : (u.1.erase u.2).card = r := by
        rw [Finset.card_erase_of_mem hpB]
        omega
      exact Finset.mem_sigma.mpr
        ⟨hp, Finset.mem_powersetCard.mpr ⟨herase, hcard'⟩⟩
    · intro t ht
      obtain ⟨hp, hA⟩ := Finset.mem_sigma.mp ht
      have hnot : t.1 ∉ t.2 := by
        intro hmem
        exact (Finset.not_mem_erase t.1 R)
          ((Finset.mem_powersetCard.mp hA).1 hmem)
      apply Sigma.ext rfl
      simpa [hnot]
    · intro u hu
      have hpB := (Finset.mem_sigma.mp hu).2
      apply Sigma.ext
      · exact Finset.insert_erase hpB
      · simp
    · intro t ht
      obtain ⟨hp, hA⟩ := Finset.mem_sigma.mp ht
      have hnot : t.1 ∉ t.2 := by
        intro hmem
        exact (Finset.not_mem_erase t.1 R)
          ((Finset.mem_powersetCard.mp hA).1 hmem)
      simp [Finset.prod_insert hnot]
  calc
    ((r + 1 : ℕ) : ℝ) * elementaryMass R w (r + 1)
        = ∑ B ∈ R.powersetCard (r + 1), ∑ p ∈ B, ∏ a ∈ B, w a := by
          unfold elementaryMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro B hB
          have hcard := (Finset.mem_powersetCard.mp hB).2
          simp [Finset.sum_const, hcard, nsmul_eq_mul]
    _ = ∑ u ∈ U, ∏ p ∈ u.1, w p := by
      simp only [U, Finset.sum_sigma]
    _ = ∑ t ∈ L, w t.1 * ∏ p ∈ t.2, w p := hbij.symm
    _ = ∑ p ∈ R, w p * elementaryMass (R.erase p) w r := by
      simp only [L, Finset.sum_sigma, elementaryMass, Finset.mul_sum]

/-- Monotonicity when one prime is erased. -/
theorem elementaryMass_erase_le
    (R : Finset ℕ) (w : ℕ → ℝ) (r p : ℕ)
    (hw : ∀ x ∈ R, 0 ≤ w x) :
    elementaryMass (R.erase p) w r ≤ elementaryMass R w r := by
  unfold elementaryMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.powersetCard_mono (Finset.erase_subset p R)
  · intro A hA _
    apply Finset.prod_nonneg
    intro x hx
    exact hw x ((Finset.mem_powersetCard.mp hA).1 hx)

/-- The exact pair count plus nonnegative weights yields the recurrence
used in phase five, now without a recurrence hypothesis. -/
theorem elementaryMass_recurrence
    (R : Finset ℕ) (w : ℕ → ℝ) (r : ℕ)
    (hw : ∀ x ∈ R, 0 ≤ w x) :
    ((r + 1 : ℕ) : ℝ) * elementaryMass R w (r + 1) ≤
      (∑ p ∈ R, w p) * elementaryMass R w r := by
  rw [elementaryMass_pair_count]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left
    (elementaryMass_erase_le R w r p hw) (hw p hp)

/-- The q-deleted reciprocal masses satisfy the exact elementary
recurrence required by phase five, for every modulus q. -/
theorem reciprocalSymmetric_recurrence
    (P : Finset ℕ) (q r : ℕ) :
    ((r + 1 : ℕ) : ℝ) * reciprocalSymmetric P q (r + 1) ≤
      survivingHarmonic P q * reciprocalSymmetric P q r := by
  simpa only [elementaryMass, reciprocalSymmetric,
    reciprocalSubsetMass, survivingHarmonic] using
    elementaryMass_recurrence (survivingPrimes P q)
      (fun p => (p : ℝ)⁻¹) r
      (by intro p hp; positivity)

/-- Uniform B2 factorial gap, now without a target-shaped or recurrence
hypothesis. The only source is finite pair counting and positivity. -/
theorem reciprocalGap_le_B2_epsilon
    (j : ℕ) (P : Finset ℕ) (q : ℕ) :
    reciprocalUpper j P q - reciprocalLower j P q ≤
      chartHarmonic P ^ (2 * j + 1) /
        (Nat.factorial (2 * j + 1) : ℝ) := by
  apply reciprocalGap_le_B2_epsilon_from_pair_count
  intro r
  exact reciprocalSymmetric_recurrence P q r

end

end ImbalancedChen.Part3.BrunSymmetricPairCount
