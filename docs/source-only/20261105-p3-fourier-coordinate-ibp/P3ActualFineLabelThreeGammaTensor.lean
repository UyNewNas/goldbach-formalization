import ImbalancedChen.P5ActualNormalizedPrimeLabelCoefficient
import ImbalancedChen.ActualPrimeDisjointLabelProducts

/-!
P3.6 original fine-label source, pinned PP-completion §3 (T).
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Three groups keep the original per-label repeated-factorial M_j and
the original full-word M_all; no total-slot factorial replaces them.
The positional word permutation must later be provided by the actual
fixed whole-box partition. No claim about same-rho arithmetic payment.
-/
namespace ImbalancedChen.P3ActualFineLabelThreeGammaTensor
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Full integer product fibres retain every original ordered tuple. -/
theorem raw_three_fibre (T₁ T₂ T₃ : Finset (List ℕ)) (H : ℕ → ℝ) :
    (∑ ps ∈ T₁, ∑ qs ∈ T₂, ∑ rs ∈ T₃,
      H (ps.prod * qs.prod * rs.prod)) =
    ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
      ∑ d ∈ T₃.image List.prod,
        ((actualPrimeTupleCoefficient T₁ a : ℝ) *
          (actualPrimeTupleCoefficient T₂ b : ℝ) *
          (actualPrimeTupleCoefficient T₃ d : ℝ)) * H (a * b * d) := by
  simp_rw [actualPrimeTuple_sum_by_product, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Exact three-gamma tensor and ORIGINAL full prime-label normalization.
The only structural premise is a permutation of the original slot word,
not a coefficient bound, source approximation, or an error estimate. -/
theorem actual_label_three_gamma_tensor {ι : Type*}
    (B : ι → Finset ℕ) (original g₁ g₂ g₃ : List (ι × ℕ))
    (hperm : (actualPrimeLabelBlocksWord original).Perm
      (actualPrimeLabelBlocksWord g₁ ++
       actualPrimeLabelBlocksWord g₂ ++
       actualPrimeLabelBlocksWord g₃))
    (c : ℝ) (H : ℕ → ℝ) :
    let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
    let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
    let T₃ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₃)
    (c / (actualPrimeLabelBlocksFactorial original : ℝ)) *
      (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord original),
        H ps.prod) =
      (c * (((actualPrimeLabelBlocksFactorial g₁ : ℝ) *
        (actualPrimeLabelBlocksFactorial g₂ : ℝ) *
        (actualPrimeLabelBlocksFactorial g₃ : ℝ)) /
        (actualPrimeLabelBlocksFactorial original : ℝ))) *
      (∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
        ∑ d ∈ T₃.image List.prod,
          gamma B g₁ a * gamma B g₂ b * gamma B g₃ d *
            H (a * b * d)) := by
  dsimp
  let T₁ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₁)
  let T₂ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₂)
  let T₃ := actualPrimeSlotBox B (actualPrimeLabelBlocksWord g₃)
  have hM₀ : (actualPrimeLabelBlocksFactorial original : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos original)
  have hM₁ : (actualPrimeLabelBlocksFactorial g₁ : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos g₁)
  have hM₂ : (actualPrimeLabelBlocksFactorial g₂ : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos g₂)
  have hM₃ : (actualPrimeLabelBlocksFactorial g₃ : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos g₃)
  have hsplit :
      (∑ ps ∈ actualPrimeSlotBox B (actualPrimeLabelBlocksWord original),
        H ps.prod) =
      ∑ ps ∈ T₁, ∑ qs ∈ T₂, ∑ rs ∈ T₃,
        H (ps.prod * qs.prod * rs.prod) := by
    rw [actualPrimeSlotBox_product_sum_perm B hperm H]
    rw [actualPrimeSlotBox_product_sum_append]
    simp_rw [actualPrimeSlotBox_product_sum_append]
    simp only [mul_assoc]
  have hscalar (a b d : ℕ) :
      (c / (actualPrimeLabelBlocksFactorial original : ℝ)) *
        (((actualPrimeTupleCoefficient T₁ a : ℝ) *
          (actualPrimeTupleCoefficient T₂ b : ℝ) *
          (actualPrimeTupleCoefficient T₃ d : ℝ)) * H (a * b * d)) =
      (c * (((actualPrimeLabelBlocksFactorial g₁ : ℝ) *
        (actualPrimeLabelBlocksFactorial g₂ : ℝ) *
        (actualPrimeLabelBlocksFactorial g₃ : ℝ)) /
        (actualPrimeLabelBlocksFactorial original : ℝ))) *
        (gamma B g₁ a * gamma B g₂ b * gamma B g₃ d *
          H (a * b * d)) := by
    dsimp [gamma]
    field_simp [hM₀, hM₁, hM₂, hM₃]
    <;> ring
  calc
    _ = (c / (actualPrimeLabelBlocksFactorial original : ℝ)) *
        (∑ ps ∈ T₁, ∑ qs ∈ T₂, ∑ rs ∈ T₃,
          H (ps.prod * qs.prod * rs.prod)) := by rw [hsplit]
    _ = (c / (actualPrimeLabelBlocksFactorial original : ℝ)) *
        (∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
          ∑ d ∈ T₃.image List.prod,
            ((actualPrimeTupleCoefficient T₁ a : ℝ) *
              (actualPrimeTupleCoefficient T₂ b : ℝ) *
              (actualPrimeTupleCoefficient T₃ d : ℝ)) * H (a * b * d)) := by
          rw [raw_three_fibre]
    _ = ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
          ∑ d ∈ T₃.image List.prod,
            (c / (actualPrimeLabelBlocksFactorial original : ℝ)) *
              (((actualPrimeTupleCoefficient T₁ a : ℝ) *
                (actualPrimeTupleCoefficient T₂ b : ℝ) *
                (actualPrimeTupleCoefficient T₃ d : ℝ)) * H (a * b * d)) := by
          simp_rw [Finset.mul_sum]
    _ = ∑ a ∈ T₁.image List.prod, ∑ b ∈ T₂.image List.prod,
          ∑ d ∈ T₃.image List.prod,
            (c * (((actualPrimeLabelBlocksFactorial g₁ : ℝ) *
              (actualPrimeLabelBlocksFactorial g₂ : ℝ) *
              (actualPrimeLabelBlocksFactorial g₃ : ℝ)) /
              (actualPrimeLabelBlocksFactorial original : ℝ))) *
              (gamma B g₁ a * gamma B g₂ b * gamma B g₃ d *
                H (a * b * d)) := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro b hb
          apply Finset.sum_congr rfl
          intro d hd
          exact hscalar a b d
    _ = _ := by simp_rw [Finset.mul_sum]

/-- Actual disjoint half-open labels give each genuine gamma its one-bound
on all integers. This uses existing original prime arithmetic, not a new
one-bounded coefficient premise. -/
theorem fine_gamma_mem_Icc
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (blocks : List (ℕ × ℕ))
    (hlabels : blocks.Pairwise (fun b d => b.1 ≠ d.1)) (n : ℕ) :
    gamma (actualPrimeFineLabelFinset N τ) blocks n ∈
      Set.Icc (0 : ℝ) 1 := by
  apply gamma_mem_Icc
  · intro bl hbl p hp
    exact (mem_actualPrimeFineLabelFinset.mp hp).1
  · exact hlabels.imp (fun h => actualPrimeFineLabelFinset_disjoint hN hτ h)

/-- The three real normalized gamma factors have product absolute value
at most one; no sum over full-product collisions is discarded. -/
theorem fine_three_gamma_product_abs_le_one
    (N : ℕ) (hN : 1 ≤ N) (τ : ℝ) (hτ : 0 ≤ τ)
    (g₁ g₂ g₃ : List (ℕ × ℕ))
    (h₁ : g₁.Pairwise (fun b d => b.1 ≠ d.1))
    (h₂ : g₂.Pairwise (fun b d => b.1 ≠ d.1))
    (h₃ : g₃.Pairwise (fun b d => b.1 ≠ d.1))
    (a b d : ℕ) :
    |gamma (actualPrimeFineLabelFinset N τ) g₁ a *
      gamma (actualPrimeFineLabelFinset N τ) g₂ b *
      gamma (actualPrimeFineLabelFinset N τ) g₃ d| ≤ 1 := by
  have ha := fine_gamma_mem_Icc N hN τ hτ g₁ h₁ a
  have hb := fine_gamma_mem_Icc N hN τ hτ g₂ h₂ b
  have hd := fine_gamma_mem_Icc N hN τ hτ g₃ h₃ d
  have hab : gamma (actualPrimeFineLabelFinset N τ) g₁ a *
      gamma (actualPrimeFineLabelFinset N τ) g₂ b ≤ 1 := by
    calc
      _ ≤ 1 * gamma (actualPrimeFineLabelFinset N τ) g₂ b :=
        mul_le_mul_of_nonneg_right ha.2 hb.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb.2 (by norm_num)
      _ = 1 := by ring
  have hab_nonneg : 0 ≤ gamma (actualPrimeFineLabelFinset N τ) g₁ a *
      gamma (actualPrimeFineLabelFinset N τ) g₂ b :=
    mul_nonneg ha.1 hb.1
  calc
    _ = gamma (actualPrimeFineLabelFinset N τ) g₁ a *
        gamma (actualPrimeFineLabelFinset N τ) g₂ b *
        gamma (actualPrimeFineLabelFinset N τ) g₃ d :=
          abs_of_nonneg (mul_nonneg hab_nonneg hd.1)
    _ ≤ 1 * gamma (actualPrimeFineLabelFinset N τ) g₃ d :=
          mul_le_mul_of_nonneg_right hab hd.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hd.2 (by norm_num)
    _ = 1 := by ring

end
end ImbalancedChen.P3ActualFineLabelThreeGammaTensor
