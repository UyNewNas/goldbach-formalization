import ImbalancedChen.P4AOriginalFourPositiveEndpoints
import ImbalancedChen.Part4ActualThirdFiniteDensityReserve

/-!
SOURCE ONLY / UNCOMPILED / KERNEL UNVERIFIED / ZERO FORMAL CREDIT.

The actual original ordinary root and actual finite third functional fit
the original four positive endpoints plus the already allocated u_d/4.
S13 supplies the sharp first and complete compact-third endpoints; the
production finite-third supplier inserts Tnew once. There is no old first
coarse excess, compact excess, numerical endpoint or approximation premise.

This is the actual positive side of the intended density ledger. It is
not an all22 signed ledger or a bound for any compiled physical coefficient.
-/

namespace ImbalancedChen.P4AActualFinitePositiveEndpoint

noncomputable section
open scoped BigOperators
open P4AAll22OriginalKLedger20261024zSourceOnly
open P4AAll22AdditionalActualSuppliers20261024zSourceOnly
open P4AAll22ActualCompactPositiveBindingSourceOnly
open P4AOrdinaryRootAll22Dictionary20261024zSourceOnly
open P4AOriginalFourPositiveEndpoints OriginalThirdFiniteReserveSourceOnly

/-- The actual compact term and original selected tail endpoint are the
exact positive endpoint used after the finite-third approximation. The
actual first integral is bounded by its selected source, not its old coarse
allowance. The tail endpoint is inserted exactly once. -/
theorem original_root_compact_Tnew_le_original_positive_sum :
    P4ASameRhoCompact.originalOrdinaryRoot + originalCompactThirdCorrection +
      (319683857488126290909150567 / 2^111 : ℝ) ≤
        ∑ i, currentUpperEighteenPositive i := by
  have hfirst := P4AActualFirstIntegralSelectedK.actual_first_integral_le_original_slot
  have hcompact : originalCompactThirdCorrection ≤
      (144590669409566793572719 / 2^80 : ℝ) :=
    actual_compact_third_le_original_slot
  have hsum : (∑ i, currentUpperEighteenPositive i) =
      (2000 / 299 + 7179974843999672947 / 2^73 +
        144590669409566793572719 / 2^80 +
        319683857488126290909150567 / 2^111 : ℝ) := by
    norm_num [currentUpperEighteenPositive, Fin.sum_univ_succ]
  rw [originalOrdinaryRoot_eq_constant_add_all22_actualFirstIntegral,
    ordinary_root_normalization, hsum]
  linarith only [hfirst, hcompact]

/-- One positive buffer ceiling and one mesh threshold work for EVERY
later e,m. The quarter is inherited from the existing actual supplier,
not proved or charged a second time. The first conjunct keeps the source
estimate available for the joint common-schedule assembly. -/
theorem exists_original_finite_positive_endpoint :
    ∃ e0 : ℝ, 0 < e0 ∧ e0 ≤ 1 / 384 ∧ ∃ m0 : ℕ,
      ∀ e : ℝ, 0 ≤ e → e ≤ e0 → ∀ m : ℕ, m0 ≤ m →
        (actualExtendedThirdFiniteFunctional e m ≤ originalCompactThirdCorrection +
          (319683857488126290909150567 / 2^111 : ℝ) + originalDensityReserve / 4) ∧
        (P4ASameRhoCompact.originalOrdinaryRoot + actualExtendedThirdFiniteFunctional e m ≤
          (∑ i, currentUpperEighteenPositive i) + originalDensityReserve / 4) := by
  obtain ⟨e0, he0, he0max, m0, hfinite⟩ :=
    finiteFunctional_le_compact_add_Tnew_add_original_density_quarter
  refine ⟨e0, he0, he0max, m0, ?_⟩
  intro e he0' he m hm
  have h := hfinite e he0' he m hm
  exact ⟨h, by linarith only [h,
    original_root_compact_Tnew_le_original_positive_sum]⟩

end
end ImbalancedChen.P4AActualFinitePositiveEndpoint
