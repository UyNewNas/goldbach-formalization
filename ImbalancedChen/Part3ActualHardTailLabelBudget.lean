import ImbalancedChen.Part3ActualCompletedHardTailCore

/-!
# The original ordered-label budget for the completed source

The two marked declarations were initially recovered byte-for-byte from original
Part3ActualCompletedHardTailMass.lean lines 107-138, Git blob
b23e2e000301008244372e076411750ad4daa2bb. Their original namespace is retained.
The existing sourceAbsMass, rawCarrier, carrier and coefficient definitions
are imported from their current owners. Only finite mass monotonicity is new.
The current proof removes one redundant trailing tactic after strict-lint feedback;
the original fragment and exact repair are recorded in the intake receipt.

The budget keeps the closed signed f interval and both ordered inner labels.
It supplies no growth bound in x and adds no primary-block count factor.
-/

namespace ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b

noncomputable section
open Classical Finset CommonSmoothCutoff
open ActualReciprocalSquarePoissonSourceOnly ActualCompletedSquarePushforwardSourceOnly
open scoped BigOperators

-- BEGIN recovered raw_label_budget_and_mass_bound
def rawLabelBudget (T : Finset ℕ) (H : ℕ) (F : ℝ) : ℝ :=
  ((Icc (Int.ceil (-F)) (Int.floor F)).card : ℝ) *
    (((T.card : ℝ)*((poissonNonzeroFrequencyWindow H).card : ℝ))^2)

theorem sourceAbsMass_le_rawLabelBudget
    (A : ℕ) (a : ℤ) (T : Finset ℕ) (H : ℕ) (F : ℝ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ t ∈ T, ‖lambda t‖ ≤ 1)
    (homega : ∀ h ∈ poissonNonzeroFrequencyWindow H, ‖omega h‖ ≤ 1) :
    sourceAbsMass (carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))) lambda omega ≤
      rawLabelBudget T H F := by
  have hweight (s : Source) (hs : s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))) :
      ‖weight lambda omega s‖ ≤ 1 := by
    have hr := (Finset.mem_filter.mp hs).1
    have hp := Finset.mem_product.mp (Finset.mem_product.mp hr).2
    have h1 := Finset.mem_product.mp hp.1
    have h2 := Finset.mem_product.mp hp.2
    have hu : ‖atomCoeff lambda omega s.2.1‖ ≤ 1 := by
      rw [atomCoeff,norm_mul]
      exact (mul_le_mul (hlambda _ h1.1) (homega _ h1.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    have hv : ‖atomCoeff lambda omega s.2.2‖ ≤ 1 := by
      rw [atomCoeff,norm_mul]
      exact (mul_le_mul (hlambda _ h2.1) (homega _ h2.2) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
    rw [weight,norm_mul,norm_star]
    exact (mul_le_mul hu hv (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  calc
    _ ≤ ∑ _s ∈ carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F)), (1 : ℝ) := Finset.sum_le_sum hweight
    _ = ((carrier A a T H (Icc (Int.ceil (-F)) (Int.floor F))).card : ℝ) := by simp
    _ ≤ ((rawCarrier T H (Icc (Int.ceil (-F)) (Int.floor F))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = rawLabelBudget T H F := by
      simp only [rawCarrier,finiteInnerCarrier,Finset.card_product,Nat.cast_mul,rawLabelBudget,pow_two]
-- END recovered raw_label_budget_and_mass_bound

/-- The absolute source mass increases under finite carrier inclusion. -/
theorem sourceAbsMass_mono {U V : Finset Source} (hUV : U ⊆ V)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    sourceAbsMass U lambda omega ≤ sourceAbsMass V lambda omega := by
  unfold sourceAbsMass
  exact Finset.sum_le_sum_of_subset_of_nonneg hUV (fun _ _ _ => norm_nonneg _)

/-- Removing the y=0 source cannot increase the sum of coefficient norms. -/
theorem sourceAbsMass_nonzero_le (U : Finset Source)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) :
    sourceAbsMass (nonzeroSource U) lambda omega ≤ sourceAbsMass U lambda omega :=
  sourceAbsMass_mono (Finset.filter_subset _ _) lambda omega

end

end ImbalancedChen.Part3.ActualCompletedHardTailMass20261026b
