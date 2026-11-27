import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3PoissonNonzeroDecayCore

/-!
# Recovered common completed-frequency tail supplier

Source-preserving intake, 2026-11-27, from the original Part3PhysicalCompletedFrequencyDecay.lean,
Git blob 626e6417fbf7505307e958201f933b15eb672d82.
Each marked declaration retains its original namespace and statement.
The receipt records mechanical proof-expression repairs against the original bytes.
The original progression-error import is replaced by its six-declaration decay core.
The source-fragment receipt records original bytes and wrapper import changes.
This module concerns the 1106 manuscript, analytic appendix lines 700-703.
It does not supply the full source-family x budget, zero-frequency payment or spectral J/A.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
noncomputable section
open Classical CommonSmoothCutoff
open scoped BigOperators SchwartzMap FourierTransform

-- BEGIN recovered frequency_norm_rapid_decay
theorem frequency_norm_rapidDecay (k : ℕ) :
    ∃ A : ℝ, 0 < A ∧ ∀ M : ℝ, 0 < M → ∀ q : ℕ, 0 < q →
      ∀ a y z m : ℤ,
      ‖frequency M q a y z m‖ ≤ A * M / (1 + |(M / (q : ℝ)) * (m : ℝ)|) ^ k := by
  obtain ⟨A, hA, hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) k
  refine ⟨A, hA, ?_⟩
  intro M hM q hq a y z m
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have ht : 0 < M / (q : ℝ) := div_pos hM hqR
  have hden : 0 < 1 + |(M / (q : ℝ)) * (m : ℝ)| := by positivity
  simp only [frequency, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  calc
    _ ≤ ((M / (q : ℝ)) * (A / (1 + |(M / (q : ℝ)) * (m : ℝ)|) ^ k)) * (q : ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hdecay _) ht.le)
        (kloosterman_norm_le q _ _) (norm_nonneg _) (by positivity)
    _ = _ := by field_simp [hqR.ne', (pow_pos hden k).ne']
-- END recovered frequency_norm_rapid_decay

-- BEGIN recovered frequency_summable_norm
/-- True completed-series norm summability, for all integer z including
nonunits. The zero mode is handled by a finite singleton majorant. -/
theorem frequency_summable_norm (M : ℝ) (hM : 0 < M) (q : ℕ) (hq : 0 < q)
    (a y z : ℤ) : Summable (fun m : ℤ => ‖frequency M q a y z m‖) := by
  obtain ⟨A, hA, hrapid⟩ := frequency_norm_rapidDecay 2
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let t := M / (q : ℝ)
  have ht : 0 < t := div_pos hM hqR
  obtain ⟨hDs, _⟩ := poissonNonzeroDecay_summable_tsum_le ht
  let delta : ℤ → ℝ := fun m => if m = 0 then A * M else 0
  have hdelta : Summable delta := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset ℤ))
    intro m hm
    have hm0 : m ≠ 0 := by simpa only [Finset.mem_singleton] using hm
    exact if_neg hm0
  have hmajor : Summable (fun m : ℤ => delta m + (A * (q : ℝ)) * poissonNonzeroDecay t m) :=
    hdelta.add (hDs.mul_left _)
  have hpoint (m : ℤ) : ‖frequency M q a y z m‖ ≤
      delta m + (A * (q : ℝ)) * poissonNonzeroDecay t m := by
    by_cases hm : m = 0
    · subst m
      simpa [delta, poissonNonzeroDecay] using
        hrapid M hM q hq a y z 0
    · calc
        _ ≤ A * M / (1 + |(M / (q : ℝ)) * (m : ℝ)|) ^ 2 := hrapid M hM q hq a y z m
        _ = _ := by
          simp only [delta, if_neg hm, poissonNonzeroDecay, zero_add]
          dsimp [t]
          have hden : 0 < 1 + |(M / (q : ℝ)) * (m : ℝ)| := by positivity
          field_simp [hqR.ne', hden.ne']
  exact hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint
-- END recovered frequency_summable_norm

-- BEGIN recovered frequency_summable
theorem frequency_summable (M : ℝ) (hM : 0 < M) (q : ℕ) (hq : 0 < q)
    (a y z : ℤ) : Summable (frequency M q a y z) :=
  (frequency_summable_norm M hM q hq a y z).of_norm
-- END recovered frequency_summable

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
