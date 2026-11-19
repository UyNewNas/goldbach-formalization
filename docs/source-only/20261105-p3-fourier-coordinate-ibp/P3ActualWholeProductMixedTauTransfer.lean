import ImbalancedChen.P3ActualWholeProductFibreLedger
import ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
import Mathlib.Tactic

/-!
P3.6, frozen PP manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion section 4 (F), following exact full-product fibres.

NEW: nonnegative arithmetic tests can be pushed through the ORIGINAL
noninjective three-box full-product fibres without loss of multiplicity.
The actual HB positional coefficient then pays only its previously proved
literal rough-word tau(m) power. The mixed test is tau(B)^R *
tau(|N-B|)^S on B != N; the diagonal is excluded before shift divisors.

This is a finite source-side transfer, NOT the near-linear moment,
NOT a uniform W_T-class verification and NOT the full PP compiler.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualWholeProductMixedTauTransfer
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWholeProductFibreLedger
open ImbalancedChen.P3ActualFixedHBOffshiftSourceLedger
open ImbalancedChen.P3ActualFrozenWholeBoxHBFixedFibre
open ImbalancedChen.P3ActualFrozenTaggedPrimeBox
open ImbalancedChen.P5Z.LiteralHeathBrownOccurrenceWords

/-- A POSITIVE weighted push-forward of the exact source fibres.
The weight may depend on the entire nonzero physical shift. In contrast
with unweighted L1 nonexpansion, this can be used under a divisor moment. -/
theorem weighted_full_product_fibre_l1_le
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (c : α → ℂ) (F : β → ℝ)
    (hF : ∀ B ∈ S.image f, 0 ≤ F B) :
    (∑ B ∈ S.image f,
       ‖∑ x ∈ S.filter (fun x => f x = B), c x‖ * F B) ≤
      ∑ x ∈ S, ‖c x‖ * F (f x) := by
  classical
  calc
    _ ≤ ∑ B ∈ S.image f,
        (∑ x ∈ S.filter (fun x => f x = B), ‖c x‖) * F B := by
          apply Finset.sum_le_sum
          intro B hB
          exact mul_le_mul_of_nonneg_right (norm_sum_le _ _) (hF B hB)
    _ = ∑ B ∈ S.image f,
        ∑ x ∈ S.filter (fun x => f x = B), ‖c x‖ * F (f x) := by
          apply Finset.sum_congr rfl
          intro B hB
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          rw [(Finset.mem_filter.mp hx).2]
    _ = _ := sum_by_full_product_fibre S f (fun x => ‖c x‖ * F (f x))

/-- Only a pointwise SOURCE coefficient bound K is used. The proof does
not assume an estimate of the resulting arithmetic moment. -/
theorem weighted_full_product_fibre_le_constant
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (c : α → ℂ) (F : β → ℝ)
    (K : ℝ) (hF : ∀ B ∈ S.image f, 0 ≤ F B)
    (hC : ∀ x ∈ S, ‖c x‖ ≤ K) :
    (∑ B ∈ S.image f,
       ‖∑ x ∈ S.filter (fun x => f x = B), c x‖ * F B) ≤
      K * (∑ x ∈ S, F (f x)) := by
  calc
    _ ≤ ∑ x ∈ S, ‖c x‖ * F (f x) :=
      weighted_full_product_fibre_l1_le S f c F hF
    _ ≤ ∑ x ∈ S, K * F (f x) := by
          apply Finset.sum_le_sum
          intro x hx
          exact mul_le_mul_of_nonneg_right (hC x hx)
            (hF (f x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩))
    _ = _ := by rw [Finset.mul_sum]

/-- Exact off-diagonal complete-INTEGER mixed divisor test.
The zero shift is never passed to Nat.divisors. R and S are fixed
nonnegative integers, not source lengths or additional distribution data. -/
def offShiftMixedTau (N R S B : ℕ) : ℝ :=
  if B = N then 0 else
    (B.divisors.card : ℝ) ^ R *
      (((((N : ℤ) - (B : ℤ)).natAbs).divisors.card : ℝ) ^ S)

theorem offShiftMixedTau_nonneg (N R S B : ℕ) :
    0 ≤ offShiftMixedTau N R S B := by
  unfold offShiftMixedTau
  split_ifs <;> positivity

theorem offShiftMixedTau_target_zero (N R S : ℕ) :
    offShiftMixedTau N R S N = 0 := by
  simp [offShiftMixedTau]

/-- The actual complete-product B=N fibre is zero BEFORE an arithmetic
moment is used. This is specific to the genuine fine-prime + strictly
rough HB source, even N, and z >= 2; it says nothing about omitted
compiler branches or empty Gamma mother words. -/
theorem actualHBFullProductCoeff_target_zero
    (N m j : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (hz : (2 : ℝ) ≤ z) (hN : Even N) :
    actualHBFullProductCoeff N m j τ z y u v w W N = 0 := by
  unfold actualHBFullProductCoeff
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨hxsrc, htarget⟩ := Finset.mem_filter.mp hx
  change x ∈
      ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u).product
        (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v)).product
      (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w) at hxsrc
  obtain ⟨hxab, hd⟩ := Finset.mem_product.mp hxsrc
  obtain ⟨ha, hb⟩ := Finset.mem_product.mp hxab
  exact hbPositionalMass_zero_of_actual_target N m j τ z y
    u v w x.1.1 x.1.2 x.2 W ha hb hd hz hN
    (by simpa only [tripleFullProduct] using htarget)

/-- A genuinely MIXED, nonzero-shift arithmetic test on the exact
complete-product fibre. No extra factor is charged for merging different
ordered triples with the same B. The pointwise W bound is ordinary source
geometry and is NOT silently proved uniform over all manuscript W_T. -/
theorem actualHBFullProductCoeff_mixed_tau_le
    (N m j R S : ℕ) (τ z y : ℝ) (u v w : List ℕ)
    (W : List ℕ → List ℕ → List ℕ → List ℕ → ℂ)
    (A : ℝ) (hm : m ≠ 0) (hz : 0 ≤ z) (hA : 0 ≤ A)
    (hW :
      ∀ a ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u,
      ∀ b ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v,
      ∀ d ∈ actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w,
      ∀ h ∈ factorTuples (2 * (j + 1)) m, ‖W a b d h‖ ≤ A) :
    (∑ B ∈ (actualHBTriples N τ u v w).image (tripleFullProduct m),
       ‖actualHBFullProductCoeff N m j τ z y u v w W B‖ *
         offShiftMixedTau N R S B) ≤
      (A * (Real.log (m : ℝ) *
        (m.divisors.card : ℝ) ^ (2 * (j + 1)))) *
      (∑ x ∈ actualHBTriples N τ u v w,
        offShiftMixedTau N R S (tripleFullProduct m x)) := by
  have hC (x : (List ℕ × List ℕ) × List ℕ)
      (hx : x ∈ actualHBTriples N τ u v w) :
      ‖hbPositionalMass m j z y W x.1.1 x.1.2 x.2‖ ≤
        A * (Real.log (m : ℝ) *
          (m.divisors.card : ℝ) ^ (2 * (j + 1))) := by
    change x ∈
        ((actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) u).product
          (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) v)).product
        (actualPrimeSlotBox (actualPrimeFineLabelFinset N τ) w) at hx
    obtain ⟨hxab, hd⟩ := Finset.mem_product.mp hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hxab
    exact hbPositionalMass_norm_le_tau m j z y W
      x.1.1 x.1.2 x.2 A hm hz hA
      (by intro h hh; exact hW _ ha _ hb _ hd h hh)
  simpa only [actualHBFullProductCoeff] using
    (weighted_full_product_fibre_le_constant
      (actualHBTriples N τ u v w) (tripleFullProduct m)
      (fun x => hbPositionalMass m j z y W x.1.1 x.1.2 x.2)
      (offShiftMixedTau N R S)
      (A * (Real.log (m : ℝ) *
        (m.divisors.card : ℝ) ^ (2 * (j + 1))))
      (by intro B hB; exact offShiftMixedTau_nonneg N R S B)
      hC)

end
end ImbalancedChen.P3ActualWholeProductMixedTauTransfer
