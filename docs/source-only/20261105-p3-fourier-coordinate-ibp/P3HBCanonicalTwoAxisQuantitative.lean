import ImbalancedChen.P3HBCanonicalGeometryDerivative
import Mathlib.Tactic

/-!
P3.6, frozen manuscript @9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F), literal original six HB log slots.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

Quantitative pointwise cost of the GENUINE two-axis derivative of one
common nonseparable complex geometry W times EVERY original labelled HB
smooth child. The four Leibniz branches, including repeated axes, are
charged separately. The ordinary M0/M1/M2 geometry jet envelopes must
still be proved for actual physical W_T, U5 and trim uniformly in T,m(N).
No integrated 2S, Fourier-H estimate, PP estimate or external (M) is used.
-/

namespace ImbalancedChen.P3HBCanonicalTwoAxisQuantitative
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBWeightedTwoAxisLeibniz
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- Raising the order at one original position costs at most one,
including when this is the same position as a previous derivative. -/
private theorem raiseOrder_le_succ (orders : Fin 6 → ℕ) (i j : Fin 6) :
    (raiseOrder orders i) j ≤ orders j + 1 := by
  by_cases hij : j = i
  · subst j
    simp [raiseOrder]
  · simp [raiseOrder, Function.update_noteq hij]

/-- Both occurrences at the same position are paid: no assumption i ≠ j. -/
private theorem twice_raised_le_two (orders : Fin 6 → ℕ)
    (i j k : Fin 6) :
    (raiseOrder (raiseOrder orders i) j) k ≤ orders k + 2 := by
  calc
    (raiseOrder (raiseOrder orders i) j) k ≤
        (raiseOrder orders i) k + 1 := raiseOrder_le_succ _ _ _
    _ ≤ (orders k + 1) + 1 := Nat.add_le_add_right
      (raiseOrder_le_succ orders i k) 1
    _ = orders k + 2 := by omega

/-- Real finite-order bound for the ORIGINAL ordered six-slot HB tensor;
the three-way label is never summed away or merged. -/
private theorem tensor_norm_le
    (chi : ℝ → ℂ) (K : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (horders : ∀ k, orders k ≤ K) :
    ‖logTensorMixed chi orders child u‖ ≤ C ^ 6 := by
  rw [logTensorMixed, norm_prod]
  calc
    (∏ k : Fin 6, ‖iteratedDeriv (orders k)
        (logChild chi (child k)) (u k)‖) ≤
      ∏ _k : Fin 6, C := by
        apply Finset.prod_le_prod
        · intro k _
          exact norm_nonneg _
        · intro k _
          exact hC (orders k) (child k) (u k) (horders k)
    _ = C ^ 6 := by simp

/-- All four ORIGINAL HB order arrays in the literal two-axis Leibniz
identity remain under the same finite derivative ceiling K. -/
private theorem all_two_axis_tensors_le
    (chi : ℝ → ℂ) (K : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (u : Fin 6 → ℝ) (i j : Fin 6)
    (hk : ∀ k, orders k + 2 ≤ K) :
    ‖logTensorMixed chi orders child u‖ ≤ C^6 ∧
    ‖logTensorMixed chi (raiseOrder orders j) child u‖ ≤ C^6 ∧
    ‖logTensorMixed chi (raiseOrder orders i) child u‖ ≤ C^6 ∧
    ‖logTensorMixed chi (raiseOrder (raiseOrder orders i) j) child u‖ ≤ C^6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply tensor_norm_le chi K C hC0 hC orders child u
    intro k
    omega
  · apply tensor_norm_le chi K C hC0 hC (raiseOrder orders j) child u
    intro k
    exact (raiseOrder_le_succ orders j k).trans (by omega)
  · apply tensor_norm_le chi K C hC0 hC (raiseOrder orders i) child u
    intro k
    exact (raiseOrder_le_succ orders i k).trans (by omega)
  · apply tensor_norm_le chi K C hC0 hC
      (raiseOrder (raiseOrder orders i) j) child u
    intro k
    exact (twice_raised_le_two orders i j k).trans (hk k)

/-- Pointwise TWO-axis derivative budget for the actual same geometry W.
The M2 term is D_j D_i W, not a free coefficient or target PP input.
No derivative commutation is invoked. All i=j multiplicities survive. -/
theorem actual_two_axis_child_norm_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (K : ℕ) (C M0 M1 M2 : ℝ)
    (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (hk : ∀ k, orders k + 2 ≤ K)
    (child : Fin 6 → Fin 3) (W : (Fin 6 → ℝ) → ℂ)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (u : Fin 6 → ℝ) (i j : Fin 6)
    (hDi : DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (h0 : ‖W u‖ ≤ M0)
    (hi : ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ‖actualAxisDeriv W j u‖ ≤ M1)
    (hji : ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    ‖actualAxisDeriv
        (actualAxisDeriv
          (fun v => W v * logTensorMixed chi orders child v) i) j u‖ ≤
      (M2 + 2*M1 + M0)*C^6 := by
  obtain ⟨hG0,hGj,hGi,hGij⟩ :=
    all_two_axis_tensors_le chi K C hC0 hC orders child u i j hk
  let G0 := logTensorMixed chi orders child u
  let Gj := logTensorMixed chi (raiseOrder orders j) child u
  let Gi := logTensorMixed chi (raiseOrder orders i) child u
  let Gij := logTensorMixed chi
    (raiseOrder (raiseOrder orders i) j) child u
  have hA : ‖actualAxisDeriv (actualAxisDeriv W i) j u * G0‖ ≤ M2*C^6 := by
    rw [norm_mul]
    exact mul_le_mul hji hG0 (norm_nonneg _) hM2
  have hB : ‖actualAxisDeriv W i u * Gj‖ ≤ M1*C^6 := by
    rw [norm_mul]
    exact mul_le_mul hi hGj (norm_nonneg _) hM1
  have hD : ‖actualAxisDeriv W j u * Gi‖ ≤ M1*C^6 := by
    rw [norm_mul]
    exact mul_le_mul hj hGi (norm_nonneg _) hM1
  have hE : ‖W u * Gij‖ ≤ M0*C^6 := by
    rw [norm_mul]
    exact mul_le_mul h0 hGij (norm_nonneg _) hM0
  rw [actualTwoAxisDeriv_weightedChild chi hchi orders child u i j W hW hDi]
  calc
    ‖((actualAxisDeriv (actualAxisDeriv W i) j u * G0 +
        actualAxisDeriv W i u * Gj) +
       (actualAxisDeriv W j u * Gi + W u * Gij))‖ ≤
      (‖actualAxisDeriv (actualAxisDeriv W i) j u * G0‖ +
        ‖actualAxisDeriv W i u * Gj‖) +
      (‖actualAxisDeriv W j u * Gi‖ + ‖W u * Gij‖) := by
        calc
          _ ≤ ‖actualAxisDeriv (actualAxisDeriv W i) j u * G0 +
                    actualAxisDeriv W i u * Gj‖ +
                ‖actualAxisDeriv W j u * Gi + W u * Gij‖ := norm_add_le _ _
          _ ≤ _ := add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ (M2*C^6+M1*C^6)+(M1*C^6+M0*C^6) :=
      add_le_add (add_le_add hA hB) (add_le_add hD hE)
    _ = (M2 + 2*M1 + M0)*C^6 := by ring

/-- Sum over the literal complete 3^6 positional children, retaining
multiplicity. The same W and its actual jets occur in EVERY summand. -/
theorem all_actual_two_axis_children_norm_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (K : ℕ) (C M0 M1 M2 : ℝ)
    (hC0 : 0 ≤ C) (hM0 : 0 ≤ M0)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hC : ∀ (k : ℕ) (a : Fin 3) (t : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) t‖ ≤ C)
    (orders : Fin 6 → ℕ) (hk : ∀ k, orders k + 2 ≤ K)
    (W : (Fin 6 → ℝ) → ℂ)
    (hW : ∀ (v : Fin 6 → ℝ) (k : Fin 6),
      DifferentiableAt ℝ
        (fun t : ℝ => W (Function.update v k t)) (v k))
    (u : Fin 6 → ℝ) (i j : Fin 6)
    (hDi : DifferentiableAt ℝ
      (fun t : ℝ => actualAxisDeriv W i (Function.update u j t)) (u j))
    (h0 : ‖W u‖ ≤ M0)
    (hi : ‖actualAxisDeriv W i u‖ ≤ M1)
    (hj : ‖actualAxisDeriv W j u‖ ≤ M1)
    (hji : ‖actualAxisDeriv (actualAxisDeriv W i) j u‖ ≤ M2) :
    (∑ child ∈ smoothChildren,
      ‖actualAxisDeriv
        (actualAxisDeriv
          (fun v => W v * logTensorMixed chi orders child v) i) j u‖) ≤
      (smoothChildren.card : ℝ) * ((M2 + 2*M1 + M0)*C^6) := by
  calc
    (∑ child ∈ smoothChildren,
      ‖actualAxisDeriv
        (actualAxisDeriv
          (fun v => W v * logTensorMixed chi orders child v) i) j u‖) ≤
      ∑ _child ∈ smoothChildren, (M2 + 2*M1 + M0)*C^6 := by
        apply Finset.sum_le_sum
        intro child _
        exact actual_two_axis_child_norm_le chi hchi K C M0 M1 M2
          hC0 hM0 hM1 hM2 hC orders hk child W hW u i j hDi h0 hi hj hji
    _ = (smoothChildren.card : ℝ) * ((M2 + 2*M1 + M0)*C^6) := by simp

end
end ImbalancedChen.P3HBCanonicalTwoAxisQuantitative
