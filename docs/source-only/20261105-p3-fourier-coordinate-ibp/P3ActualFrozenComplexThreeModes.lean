import ImbalancedChen.P3ActualFrozenComplexThreeTensor

/-!
P3.6 — finite COMPLEX Fourier modes on the THREE actual frozen physical
ordered-group words, with the exact original factorial and SAME rho.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
This establishes the finite trilinear mode interchange and uses the
already supplied actual-physical-group tensor.  A Fourier mode is a
literal product of three positional group multipliers; there is NO
assumption that the original geometry W_T already has this form.
In particular no continuous inversion, uniform truncation, actual
PP-atom rho_T identification, arithmetic estimate or (M) is proved.
-/

namespace ImbalancedChen.P3ActualFrozenComplexThreeModes
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualFrozenComplexGroupGamma
open ImbalancedChen.P3ActualFrozenComplexThreeTensor
open ImbalancedChen.P3ActualFrozenSlotLabelCounts
open ImbalancedChen.P3ActualSplitLabelMultinomial
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P5Z.ActualNormalizedPrimeLabelCoefficient

/-- Finite Fubini: move a common mode index across the THREE genuine
ordered group sums, without permuting any positional multiplier. -/
theorem triple_mode_sum_comm
    {α β γ κ : Type*}
    (S₀ : Finset α) (S₁ : Finset β) (S₂ : Finset γ)
    (K : Finset κ) (F : κ → α → β → γ → ℂ) :
    (∑ x ∈ S₀, ∑ y ∈ S₁, ∑ z ∈ S₂,
      ∑ k ∈ K, F k x y z) =
    ∑ k ∈ K, ∑ x ∈ S₀, ∑ y ∈ S₁, ∑ z ∈ S₂,
      F k x y z := by
  classical
  calc
    _ = ∑ x ∈ S₀, ∑ y ∈ S₁, ∑ k ∈ K, ∑ z ∈ S₂,
          F k x y z := by
            apply Finset.sum_congr rfl
            intro x hx
            apply Finset.sum_congr rfl
            intro y hy
            exact Finset.sum_comm
    _ = ∑ x ∈ S₀, ∑ k ∈ K, ∑ y ∈ S₁, ∑ z ∈ S₂,
          F k x y z := by
            apply Finset.sum_congr rfl
            intro x hx
            exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- The literal finite trilinear weight separates a COMMON Fourier mode
before the three physical boxes are pushed through their product fibres.
This identity remains true for positional weights and empty groups. -/
theorem finite_modes_three_sum_transport
    {α β γ κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (S₀ : Finset α) (S₁ : Finset β) (S₂ : Finset γ)
    (v₀ : κ → α → ℂ) (v₁ : κ → β → ℂ)
    (v₂ : κ → γ → ℂ) (H : α → β → γ → ℂ) :
    (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
      (∑ k ∈ K, amp k *
        (v₀ k ps * (v₁ k qs * v₂ k rs))) * H ps qs rs) =
    ∑ k ∈ K, amp k *
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        v₀ k ps * (v₁ k qs * (v₂ k rs * H ps qs rs))) := by
  classical
  calc
    _ = ∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
          ∑ k ∈ K, amp k *
            (v₀ k ps * (v₁ k qs *
              (v₂ k rs * H ps qs rs))) := by
          apply Finset.sum_congr rfl
          intro ps hps
          apply Finset.sum_congr rfl
          intro qs hqs
          apply Finset.sum_congr rfl
          intro rs hrs
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ k ∈ K, ∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
          amp k * (v₀ k ps * (v₁ k qs *
            (v₂ k rs * H ps qs rs))) :=
      triple_mode_sum_comm S₀ S₁ S₂ K _
    _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          simp_rw [← Finset.mul_sum]

/-- For an ACTUAL frozen three-word source, a genuine FINITE sum of
separated positional modes can be transported through all three original
prime-product fibres at once. The ORIGINAL M_all and M_0 M_1 M_2 ratio
are retained exactly, as are every repeated-label tuple occurrence.

No equality with a general continuous physical W_T is postulated. -/
theorem actual_frozen_three_finite_modes_tensor
    {κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ)) (c : ℂ)
    (v₀ v₁ v₂ : κ → List ℕ → ℂ) (H : ℕ → ℂ) :
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
        (∑ k ∈ K, amp k *
          (v₀ k ps * (v₁ k qs * v₂ k rs))) *
            H (ps.prod * qs.prod * rs.prod)) =
    (c * (((actualPrimeLabelBlocksFactorial g₀ : ℂ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℂ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℂ)) /
      (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
      (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
        ∑ d ∈ S₂.image List.prod,
          (∑ k ∈ K, amp k *
            (physicalComplexLabelGamma B groups.1 g₀ (v₀ k) a *
              (physicalComplexLabelGamma B groups.2.1 g₁ (v₁ k) b *
                physicalComplexLabelGamma B groups.2.2 g₂ (v₂ k) d))) *
              H (a * b * d)) := by
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
  let Mall : ℂ := actualPrimeLabelBlocksFactorial blocks
  let Mratio : ℂ :=
    (actualPrimeLabelBlocksFactorial g₀ : ℂ) *
      (actualPrimeLabelBlocksFactorial g₁ : ℂ) *
      (actualPrimeLabelBlocksFactorial g₂ : ℂ) / Mall
  let G₀ : κ → ℕ → ℂ :=
    fun k => physicalComplexLabelGamma B groups.1 g₀ (v₀ k)
  let G₁ : κ → ℕ → ℂ :=
    fun k => physicalComplexLabelGamma B groups.2.1 g₁ (v₁ k)
  let G₂ : κ → ℕ → ℂ :=
    fun k => physicalComplexLabelGamma B groups.2.2 g₂ (v₂ k)
  let physical (k : κ) : ℂ :=
    ∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
      v₀ k ps * (v₁ k qs *
        (v₂ k rs * H (ps.prod * qs.prod * rs.prod)))
  let tensor (k : κ) : ℂ :=
    ∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
      ∑ d ∈ S₂.image List.prod,
        G₀ k a * (G₁ k b * (G₂ k d * H (a * b * d)))
  have hphysical :
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        (∑ k ∈ K, amp k *
          (v₀ k ps * (v₁ k qs * v₂ k rs))) *
            H (ps.prod * qs.prod * rs.prod)) =
      ∑ k ∈ K, amp k * physical k :=
    finite_modes_three_sum_transport K amp S₀ S₁ S₂ v₀ v₁ v₂
      (fun ps qs rs => H (ps.prod * qs.prod * rs.prod))
  have htensor :
      (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
        ∑ d ∈ S₂.image List.prod,
          (∑ k ∈ K, amp k *
            (G₀ k a * (G₁ k b * G₂ k d))) *
              H (a * b * d)) =
      ∑ k ∈ K, amp k * tensor k :=
    finite_modes_three_sum_transport K amp
      (S₀.image List.prod) (S₁.image List.prod) (S₂.image List.prod)
      G₀ G₁ G₂ (fun a b d => H (a * b * d))
  have hbase (k : κ) :
      (c / Mall) * physical k = (c * Mratio) * tensor k := by
    exact actual_frozen_three_complex_tensor
      N τ D A yz upper p tail blocks c (v₀ k) (v₁ k) (v₂ k) H
  change (c / Mall) *
      (∑ ps ∈ S₀, ∑ qs ∈ S₁, ∑ rs ∈ S₂,
        (∑ k ∈ K, amp k *
          (v₀ k ps * (v₁ k qs * v₂ k rs))) *
            H (ps.prod * qs.prod * rs.prod)) =
    (c * Mratio) *
      (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
        ∑ d ∈ S₂.image List.prod,
          (∑ k ∈ K, amp k *
            (G₀ k a * (G₁ k b * G₂ k d))) * H (a * b * d))
  calc
    _ = (c / Mall) * (∑ k ∈ K, amp k * physical k) := by
      rw [hphysical]
    _ = ∑ k ∈ K, amp k * ((c / Mall) * physical k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ k ∈ K, amp k * ((c * Mratio) * tensor k) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hbase k]
    _ = (c * Mratio) * (∑ k ∈ K, amp k * tensor k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = _ := by rw [htensor]

/-- Finite Fourier mode tensor with the exact SAME integer rho(q) on the
entire congruence-minus-coprime-mean kernel at each literal modulus.
Q and rho remain PARAMETERS; their identification with all actual PP
atoms is a separate, still-open internal compiler obligation. -/
theorem actual_frozen_three_finite_modes_same_rho
    {κ : Type*} (K : Finset κ) (amp : κ → ℂ)
    (N : ℕ) (τ D A : ℝ) (yz : Bool) (upper : ℕ → ℕ)
    (p : Fin 3 → ℕ) (tail : List ℕ)
    (blocks : List (ℕ × ℕ)) (c : ℂ)
    (v₀ v₁ v₂ : κ → List ℕ → ℂ)
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
          (∑ k ∈ K, amp k *
            (v₀ k ps * (v₁ k qs * v₂ k rs))) *
              ((fineKernel T q (ps.prod * qs.prod * rs.prod) : ℝ) : ℂ)))) =
    ∑ q ∈ Q, (rho q : ℂ) *
      ((c * (((actualPrimeLabelBlocksFactorial g₀ : ℂ) *
          (actualPrimeLabelBlocksFactorial g₁ : ℂ) *
          (actualPrimeLabelBlocksFactorial g₂ : ℂ)) /
          (actualPrimeLabelBlocksFactorial blocks : ℂ))) *
        (∑ a ∈ S₀.image List.prod, ∑ b ∈ S₁.image List.prod,
          ∑ d ∈ S₂.image List.prod,
            (∑ k ∈ K, amp k *
              (physicalComplexLabelGamma B groups.1 g₀ (v₀ k) a *
                (physicalComplexLabelGamma B groups.2.1 g₁ (v₁ k) b *
                  physicalComplexLabelGamma B groups.2.2 g₂ (v₂ k) d))) *
                ((fineKernel T q (a * b * d) : ℝ) : ℂ))) := by
  dsimp only
  apply Finset.sum_congr rfl
  intro q hq
  exact congrArg (fun z : ℂ => (rho q : ℂ) * z)
    (actual_frozen_three_finite_modes_tensor K amp
      N τ D A yz upper p tail blocks c v₀ v₁ v₂
      (fun n => ((fineKernel T q n : ℝ) : ℂ)))

end
end ImbalancedChen.P3ActualFrozenComplexThreeModes
