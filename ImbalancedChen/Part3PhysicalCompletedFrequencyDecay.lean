import ImbalancedChen.Part3PhysicalSmoothReciprocalPoisson
import ImbalancedChen.Part3SmoothProgressionError

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual completed frequency: (M/q) Fhat((M/q)m) K_q(m*inverse(z),a*y).
The true trivial Kloosterman bound needs no unit condition on z. Every
constant precedes M,q,a,y,z,m; the actual inverse(z) remains unchanged.
Absolute summability includes m=0, rather than deleting its exact term.
-/

namespace ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
noncomputable section
open Classical CommonSmoothCutoff
open scoped BigOperators SchwartzMap FourierTransform

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
    _ = _ := by field_simp [hqR.ne', (pow_pos hden k).ne'] <;> ring

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
      simpa only [delta, if_pos rfl, poissonNonzeroDecay, if_pos rfl,
        Int.cast_zero, mul_zero, abs_zero, add_zero, one_pow, div_one, zero_add] using
        hrapid M hM q hq a y z 0
    · calc
        _ ≤ A * M / (1 + |(M / (q : ℝ)) * (m : ℝ)|) ^ 2 := hrapid M hM q hq a y z m
        _ = _ := by
          simp only [delta, if_neg hm, poissonNonzeroDecay, if_neg hm, zero_add]
          dsimp [t]
          have hden : 0 < 1 + |(M / (q : ℝ)) * (m : ℝ)| := by positivity
          field_simp [hqR.ne', hden.ne'] <;> ring
  exact hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint

theorem frequency_summable (M : ℝ) (hM : 0 < M) (q : ℕ) (hq : 0 < q)
    (a y z : ℤ) : Summable (frequency M q a y z) :=
  (frequency_summable_norm M hM q hq a y z).of_norm

end
end ImbalancedChen.Part3.OriginalSmoothPoissonTail.HardCompletedSchwartz20261026b
