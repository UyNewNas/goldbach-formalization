import ImbalancedChen.Part3OriginalMaskedWShortModulusBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26, phase 6.

Every fixed k is chosen BEFORE the physical scale, residue or coefficient
family. Actual Schwartz decay of order k+2 and the existing true quadratic
decay sum imply C_k/t^k for the COMPLETE nonzero frequency series. The
original normalization is t=V/lcm on the transposed source, so this is
C_k*(lcm/V)^k, not a power of a substituted physical scale. Existing
general tail exponents concern a truncated tail and are not this estimate.
-/

namespace ImbalancedChen.Part3.OriginalPoissonAllInversePowers20261026b
noncomputable section
open Classical CommonSmoothCutoff
open scoped BigOperators SchwartzMap FourierTransform

theorem original_poisson_nonzero_all_inverse_powers (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ x : ℝ,
      ‖∑' h : ℤ, poissonNonzeroFrequency t x h‖ ≤ C/t^k := by
  obtain ⟨C,hC,hdecay⟩ := schwartz_norm_le_rapidDecay (𝓕 dyadicCutoffSchwartz) (k+2)
  refine ⟨2*C,by positivity,fun t ht x => ?_⟩
  obtain ⟨hDs,hDb⟩ := poissonNonzeroDecay_summable_tsum_le ht
  have hpoint (h : ℤ) :
      ‖poissonNonzeroFrequency t x h‖ ≤ (C/t^k)*poissonNonzeroDecay t h := by
    by_cases hh : h = 0
    · simp [poissonNonzeroFrequency,poissonNonzeroDecay,hh]
    · have hhR : (1 : ℝ) ≤ |(h : ℝ)| := by
        rw [← Int.cast_one,← Int.cast_abs,Int.cast_le]
        exact Int.one_le_abs hh
      let A : ℝ := 1+|t*(h : ℝ)|
      have hA : 0 < A := by dsimp [A]; positivity
      have htA : t ≤ A := by
        dsimp [A]
        rw [abs_mul,abs_of_pos ht]
        nlinarith
      have hratio : C/A^k ≤ C/t^k := div_le_div_of_nonneg_left hC.le
        (pow_pos ht k) (pow_le_pow_left₀ ht.le htA k)
      simp only [poissonNonzeroFrequency,poissonNonzeroDecay,if_neg hh,
        norm_mul,norm_smul,Real.norm_eq_abs,abs_of_pos ht,
        fourier_apply,Circle.norm_coe,mul_one]
      calc
        _ ≤ t*(C/A^(k+2)) := mul_le_mul_of_nonneg_left (hdecay (t*h)) ht.le
        _ = (C/A^k)*(t/A^2) := by rw [pow_add]; field_simp [hA.ne']; ring
        _ ≤ (C/t^k)*(t/A^2) := mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = _ := rfl
  have hnorm := poissonNonzeroFrequency_summable_norm ht x
  calc
    _ ≤ ∑' h : ℤ, ‖poissonNonzeroFrequency t x h‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' h : ℤ, (C/t^k)*poissonNonzeroDecay t h :=
      hnorm.tsum_le_tsum hpoint (hDs.mul_left (C/t^k))
    _ = (C/t^k)*∑' h : ℤ, poissonNonzeroDecay t h := tsum_mul_left
    _ ≤ (C/t^k)*2 := mul_le_mul_of_nonneg_left hDb (by positivity)
    _ = (2*C)/t^k := by ring

end
end ImbalancedChen.Part3.OriginalPoissonAllInversePowers20261026b
