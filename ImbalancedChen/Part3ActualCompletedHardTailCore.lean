import ImbalancedChen.Part3PhysicalCommonHardFrequencyWindow
import ImbalancedChen.Part3LiteralReciprocalSource

/-!
# Recovered common completed-frequency tail supplier

Source-preserving intake, 2026-11-27, from the original Part3ActualCompletedHardTailMass.lean,
Git blob b23e2e000301008244372e076411750ad4daa2bb.
Each marked declaration retains its original namespace and statement.
The receipt records mechanical proof-expression repairs against the original bytes.
The actual completed kernel and finite source use their current existing owners.
Only the generic kernel/source tail is recovered; actual mode norm suppliers are separate.
The source-fragment receipt records original bytes and wrapper import changes.
This module concerns the 1106 manuscript, analytic appendix lines 700-703.
It does not supply the full source-family x budget, zero-frequency payment or spectral J/A.
-/

namespace ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open scoped BigOperators

-- BEGIN recovered hard_completed_kernel
def hardCompletedKernel (M N C R : ℝ) (a : ℤ) (zy : Output) : ℂ :=
  ∑ c ∈ Ioc 0 (Nat.floor (10*C)), if c.Coprime zy.1 then
    (scaledDyadicCutoff N c : ℂ) *
      ∑ m ∈ commonHardWindow C M R, frequency M c a zy.2 (zy.1 : ℤ) m else 0
-- END recovered hard_completed_kernel

-- BEGIN recovered hard_source_piece
def hardSourcePiece (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (M N C R : ℝ) (a : ℤ) : ℂ :=
  ∑ s ∈ U, weight lambda omega s * hardCompletedKernel M N C R a (output s)
-- END recovered hard_source_piece

-- BEGIN recovered source_abs_mass
def sourceAbsMass (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ) : ℝ :=
  ∑ s ∈ U, ‖weight lambda omega s‖
-- END recovered source_abs_mass

-- BEGIN recovered completed_kernel_common_hard_tail
theorem completedKernel_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ R : ℝ, 0 < R → ∀ N : ℝ, ∀ a : ℤ, ∀ zy : Output,
        ‖completedKernel M N C a zy - hardCompletedKernel M N C R a zy‖ ≤
          A*C^2/R^(r-1) := by
  obtain ⟨A,hA,htail⟩ := frequency_common_hard_window_tail_cap r hr
  refine ⟨100*A,by positivity,fun C hC M hM R hR N a zy => ?_⟩
  unfold completedKernel hardCompletedKernel
  rw [← Finset.sum_sub_distrib]
  have hpoint (c : ℕ) (hc : c ∈ Ioc 0 (Nat.floor (10*C))) :
      ‖(if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
          ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0) -
        (if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
          ∑ m ∈ commonHardWindow C M R, frequency M c a zy.2 (zy.1 : ℤ) m else 0)‖ ≤
        10*A*C/R^(r-1) := by
    have hcpos := (Finset.mem_Ioc.mp hc).1
    have hcap : (c : ℝ) ≤ 10*C :=
      (show (c : ℝ) ≤ (Nat.floor (10*C) : ℝ) by
        exact_mod_cast (Finset.mem_Ioc.mp hc).2).trans (Nat.floor_le (by positivity))
    by_cases hunit : c.Coprime zy.1
    · simp only [if_pos hunit,← mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (scaledDyadicCutoff_nonneg N c)]
      have he := htail C hC M hM R hR c hcpos hcap a zy.2 (zy.1 : ℤ)
      calc
        _ ≤ (scaledDyadicCutoff N c)*(10*A*C/R^(r-1)) :=
          mul_le_mul_of_nonneg_left he (scaledDyadicCutoff_nonneg N c)
        _ ≤ 1*(10*A*C/R^(r-1)) :=
          mul_le_mul_of_nonneg_right (scaledDyadicCutoff_le_one N c) (by positivity)
        _ = _ := one_mul _
    · simp [hunit]; positivity
  have hcard : ((Ioc 0 (Nat.floor (10*C))).card : ℝ) ≤ 10*C := by
    simpa only [Nat.card_Ioc,Nat.sub_zero] using (Nat.floor_le (by positivity : 0 ≤ 10*C))
  calc
    _ ≤ ∑ c ∈ Ioc 0 (Nat.floor (10*C)),
        ‖(if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
          ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0) -
          (if c.Coprime zy.1 then (scaledDyadicCutoff N c : ℂ) *
            ∑ m ∈ commonHardWindow C M R, frequency M c a zy.2 (zy.1 : ℤ) m else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ Ioc 0 (Nat.floor (10*C)), 10*A*C/R^(r-1) := Finset.sum_le_sum hpoint
    _ = ((Ioc 0 (Nat.floor (10*C))).card : ℝ)*(10*A*C/R^(r-1)) := by simp
    _ ≤ (10*C)*(10*A*C/R^(r-1)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (100*A)*C^2/R^(r-1) := by ring
-- END recovered completed_kernel_common_hard_tail

-- BEGIN recovered source_common_hard_tail
/-- The signed coefficient stays inside the source before norms. -/
theorem source_common_hard_tail (r : ℕ) (hr : 2 ≤ r) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : ℝ, 0 < C → ∀ M : ℝ, 0 < M →
      ∀ R : ℝ, 0 < R → ∀ N : ℝ, ∀ a : ℤ,
      ∀ (U : Finset Source) (lambda : ℕ → ℂ) (omega : ℤ → ℂ),
        ‖(∑ s ∈ U, weight lambda omega s * completedKernel M N C a (output s)) -
          hardSourcePiece U lambda omega M N C R a‖ ≤
            (A*C^2/R^(r-1))*sourceAbsMass U lambda omega := by
  obtain ⟨A,hA,hkernel⟩ := completedKernel_common_hard_tail r hr
  refine ⟨A,hA,fun C hC M hM R hR N a U lambda omega => ?_⟩
  unfold hardSourcePiece sourceAbsMass
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ s ∈ U, ‖weight lambda omega s * completedKernel M N C a (output s) -
        weight lambda omega s * hardCompletedKernel M N C R a (output s)‖ := norm_sum_le _ _
    _ ≤ ∑ s ∈ U, ‖weight lambda omega s‖*(A*C^2/R^(r-1)) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [← mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (hkernel C hC M hM R hR N a (output s)) (norm_nonneg _)
    _ = (A*C^2/R^(r-1))*(∑ s ∈ U, ‖weight lambda omega s‖) := by
      rw [← Finset.sum_mul]
      ring
-- END recovered source_common_hard_tail

end
end ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
