import ImbalancedChen.P3ActualFrozenComplexGroupGamma

/-!
P3.6: exact THREE physical ordered-group complex Fourier-mode tensor.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
The group multiplier remains on its ACTUAL ordered physical tuple word:
neither a permutation of a positional multiplier nor a fictitious
product-only dependency is used. Exact original group factorials
and full original factorial are kept.

This file performs finite algebra only. It does NOT derive Fourier
separation of the original W_T, the physical rho_T source dictionary,
an arithmetic distribution bound, or the product=T exception payment.
-/

namespace ImbalancedChen.P3ActualFrozenComplexThreeTensor
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualComplexModeFibreTransport
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Three independent ordered group weights are pushed forward through
their individual COMPLETE integer products. All tuple collisions stay
inside their genuine weighted fibres. This is a finite Fubini identity,
not a premise that W_T has already separated. -/
theorem complex_three_weighted_fibre
    (S₀ S₁ S₂ : Finset (List ℕ))
    (v₀ v₁ v₂ : List ℕ → ℂ) (H : ℕ → ℂ) :
    (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
      v₀ ps * (v₁ qs * (v₂ rs *
        H (ps.prod * qs.prod * rs.prod)))) =
    ∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
      ∑ d ∈ S₂.image List.prod,
        (∑ ps ∈ S₀.filter (fun ps => ps.prod = a), v₀ ps) *
          ((∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs) *
            ((∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
              H (a * b * d))) := by
  have hmiddle (a : ℕ) :
      (∑ qs ∈ S₁, ∑ rs ∈ S₂,
        v₁ qs * (v₂ rs * H (a * qs.prod * rs.prod))) =
      ∑ b ∈ S₁.image List.prod, ∑ d ∈ S₂.image List.prod,
        (∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs) *
          ((∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
            H (a * b * d)) := by
    calc
      _ = ∑ qs ∈ S₁, v₁ qs *
            (∑ rs ∈ S₂, v₂ rs * H (a * qs.prod * rs.prod)) := by
              simp_rw [Finset.mul_sum]
      _ = ∑ qs ∈ S₁, v₁ qs *
            (∑ d ∈ S₂.image List.prod,
              (∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
                H (a * qs.prod * d)) := by
              apply Finset.sum_congr rfl
              intro qs hqs
              exact congrArg (fun z : ℂ => v₁ qs * z)
                (complex_weighted_sum_by_product S₂ v₂
                  (fun d => H (a * qs.prod * d)))
      _ = ∑ b ∈ S₁.image List.prod,
            (∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs) *
              (∑ d ∈ S₂.image List.prod,
                (∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
                  H (a * b * d)) :=
              complex_weighted_sum_by_product S₁ v₁
                (fun b => ∑ d ∈ S₂.image List.prod,
                  (∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
                    H (a * b * d))
      _ = _ := by simp_rw [Finset.mul_sum]
  calc
    _ = ∑ ps ∈ S₀, v₀ ps *
          (∑ qs ∈ S₁, ∑ rs ∈ S₂,
            v₁ qs * (v₂ rs * H (ps.prod * qs.prod * rs.prod))) := by
              simp_rw [Finset.mul_sum]
    _ = ∑ ps ∈ S₀, v₀ ps *
          (∑ b ∈ S₁.image List.prod, ∑ d ∈ S₂.image List.prod,
            (∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs) *
              ((∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
                H (ps.prod * b * d))) := by
              apply Finset.sum_congr rfl
              intro ps hps
              exact congrArg (fun z : ℂ => v₀ ps * z) (hmiddle ps.prod)
    _ = ∑ a ∈ S₀.image List.prod,
          (∑ ps ∈ S₀.filter (fun ps => ps.prod = a), v₀ ps) *
            (∑ b ∈ S₁.image List.prod, ∑ d ∈ S₂.image List.prod,
              (∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs) *
                ((∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
                  H (a * b * d))) :=
            complex_weighted_sum_by_product S₀ v₀
              (fun a => ∑ b ∈ S₁.image List.prod,
                ∑ d ∈ S₂.image List.prod,
                  (∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs) *
                    ((∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs) *
                      H (a * b * d)))
    _ = _ := by simp_rw [Finset.mul_sum]

/-- Literal three physical frozen groups with original M_all and
M₀ M₁ M₂ correction, not an arbitrary split surrogate. There is
NO assumption of symmetry for any of the three ordered multipliers. -/
theorem actual_frozen_three_complex_tensor
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ)) (c : ℂ)
    (v₀ v₁ v₂ : List ℕ → ℂ) (H : ℕ → ℂ) :
    let B := actualPrimeFineLabelFinset N τ
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    let size := actualFrozenSplitSize D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let S₀ := actualPrimeSlotBox B groups.1
    let S₁ := actualPrimeSlotBox B groups.2.1
    let S₂ := actualPrimeSlotBox B groups.2.2
    (c / (actualPrimeLabelBlocksFactorial blocks : ℂ)) *
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        v₀ ps * (v₁ qs * (v₂ rs *
          H (ps.prod * qs.prod * rs.prod)))) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℂ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℂ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℂ)) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
      (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
        ∑ d ∈ S₂.image List.prod,
          physicalComplexLabelGamma B groups.1 g₀ v₀ a *
            (physicalComplexLabelGamma B groups.2.1 g₁ v₁ b *
              (physicalComplexLabelGamma B groups.2.2 g₂ v₂ d *
                H (a * b * d)))) := by
  dsimp only
  let B := actualPrimeFineLabelFinset N τ
  let groups := actualFrozenSelectedPairSlots D A yz upper p tail
  let size := actualFrozenSplitSize D A yz upper p tail
  let g₀ := splitBlocks blocks size 0
  let g₁ := splitBlocks blocks size 1
  let g₂ := splitBlocks blocks size 2
  let S₀ := actualPrimeSlotBox B groups.1
  let S₁ := actualPrimeSlotBox B groups.2.1
  let S₂ := actualPrimeSlotBox B groups.2.2
  let M₀ : ℂ := actualPrimeLabelBlocksFactorial g₀
  let M₁ : ℂ := actualPrimeLabelBlocksFactorial g₁
  let M₂ : ℂ := actualPrimeLabelBlocksFactorial g₂
  let Mall : ℂ := actualPrimeLabelBlocksFactorial blocks
  have hM₀ : M₀ ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos g₀)
  have hM₁ : M₁ ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos g₁)
  have hM₂ : M₂ ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (actualPrimeLabelBlocksFactorial_pos g₂)
  let F₀ : ℕ → ℂ := fun a =>
    ∑ ps ∈ S₀.filter (fun ps => ps.prod = a), v₀ ps
  let F₁ : ℕ → ℂ := fun b =>
    ∑ qs ∈ S₁.filter (fun qs => qs.prod = b), v₁ qs
  let F₂ : ℕ → ℂ := fun d =>
    ∑ rs ∈ S₂.filter (fun rs => rs.prod = d), v₂ rs
  let Γ₀ : ℕ → ℂ := physicalComplexLabelGamma B groups.1 g₀ v₀
  let Γ₁ : ℕ → ℂ := physicalComplexLabelGamma B groups.2.1 g₁ v₁
  let Γ₂ : ℕ → ℂ := physicalComplexLabelGamma B groups.2.2 g₂ v₂
  have h₀ (a : ℕ) : F₀ a = M₀ * Γ₀ a := by
    change F₀ a = M₀ * (F₀ a / M₀)
    field_simp [hM₀]
  have h₁ (b : ℕ) : F₁ b = M₁ * Γ₁ b := by
    change F₁ b = M₁ * (F₁ b / M₁)
    field_simp [hM₁]
  have h₂ (d : ℕ) : F₂ d = M₂ * Γ₂ d := by
    change F₂ d = M₂ * (F₂ d / M₂)
    field_simp [hM₂]
  have hpoint (a b d : ℕ) :
      (F₀ a * (F₁ b * (F₂ d * H (a * b * d)))) / Mall =
        ((M₀ * M₁ * M₂) / Mall) *
          (Γ₀ a * (Γ₁ b * (Γ₂ d * H (a * b * d)))) := by
    rw [h₀ a, h₁ b, h₂ d]
    ring
  have hnormalized :
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        v₀ ps * (v₁ qs * (v₂ rs *
          H (ps.prod * qs.prod * rs.prod)))) / Mall =
      ((M₀ * M₁ * M₂) / Mall) *
        (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            Γ₀ a * (Γ₁ b * (Γ₂ d * H (a * b * d)))) := by
    calc
      _ = (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            F₀ a * (F₁ b * (F₂ d * H (a * b * d)))) / Mall := by
              exact congrArg (fun z : ℂ => z / Mall)
                (complex_three_weighted_fibre S₀ S₁ S₂ v₀ v₁ v₂ H)
      _ = ∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            (F₀ a * (F₁ b * (F₂ d * H (a * b * d)))) / Mall := by
              simp_rw [← Finset.sum_div]
      _ = ∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            ((M₀ * M₁ * M₂) / Mall) *
              (Γ₀ a * (Γ₁ b * (Γ₂ d * H (a * b * d)))) := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro b hb
              apply Finset.sum_congr rfl
              intro d hd
              exact hpoint a b d
      _ = _ := by simp_rw [Finset.mul_sum]
  change (c / Mall) *
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        v₀ ps * (v₁ qs * (v₂ rs *
          H (ps.prod * qs.prod * rs.prod)))) =
      (c * ((M₀ * M₁ * M₂) / Mall)) *
        (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            Γ₀ a * (Γ₁ b * (Γ₂ d * H (a * b * d))))
  calc
    _ = c * ((∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        v₀ ps * (v₁ qs * (v₂ rs *
          H (ps.prod * qs.prod * rs.prod)))) / Mall) := by ring
    _ = c * (((M₀ * M₁ * M₂) / Mall) *
        (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            Γ₀ a * (Γ₁ b * (Γ₂ d * H (a * b * d))))) := by
              rw [hnormalized]
    _ = _ := by ring

/-- EXACT physical count-minus-coprime-mean tensor at each modulus.
The SAME integer rho multiplies the two sides; it is still a parameter,
not yet identified with every actual physical PP atom's rho_T. -/
theorem actual_frozen_three_complex_same_rho
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ)) (c : ℂ)
    (v₀ v₁ v₂ : List ℕ → ℂ)
    (Q : Finset ℕ) (rho : ℕ → ℤ) (T : ℕ) :
    let B := actualPrimeFineLabelFinset N τ
    let groups := actualFrozenSelectedPairSlots D A yz upper p tail
    let size := actualFrozenSplitSize D A yz upper p tail
    let g₀ := splitBlocks blocks size 0
    let g₁ := splitBlocks blocks size 1
    let g₂ := splitBlocks blocks size 2
    let S₀ := actualPrimeSlotBox B groups.1
    let S₁ := actualPrimeSlotBox B groups.2.1
    let S₂ := actualPrimeSlotBox B groups.2.2
    (∑ q ∈ Q, (rho q : ℂ) *
      ((c / (actualPrimeLabelBlocksFactorial blocks : ℂ)) *
        (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
          v₀ ps * (v₁ qs * (v₂ rs *
            ((fineKernel T q (ps.prod * qs.prod * rs.prod) : ℝ) : ℂ)))))) =
    ∑ q ∈ Q, (rho q : ℂ) *
      ((c * (((actualPrimeLabelBlocksFactorial g₀ : ℂ) *
          (actualPrimeLabelBlocksFactorial g₁ : ℂ) *
          (actualPrimeLabelBlocksFactorial g₂ : ℂ)) /
          (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
        (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            physicalComplexLabelGamma B groups.1 g₀ v₀ a *
              (physicalComplexLabelGamma B groups.2.1 g₁ v₁ b *
                (physicalComplexLabelGamma B groups.2.2 g₂ v₂ d *
                  ((fineKernel T q (a * b * d) : ℝ) : ℂ))))) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro q hq
  exact congrArg (fun z : ℂ => (rho q : ℂ) * z)
    (actual_frozen_three_complex_tensor N τ D A yz upper p tail
      blocks c v₀ v₁ v₂
      (fun n => ((fineKernel T q n : ℝ) : ℂ)))

end
end ImbalancedChen.P3ActualFrozenComplexThreeTensor
