import ImbalancedChen.Part3TransposedZeroPayment
import ImbalancedChen.Part3TransposedPrimitiveVPayment

/-!
# The actual centered energy after zero, U and V have been paid

The literal common-smoothed centered energy is compared with the real part
of its complete signed nonzero Poisson remainder. The primitive zero term,
literal U-P0 and literal V-P0 are all paid by proved family estimates after
multiplication by the actual original-beta L2 moment.

The complete nonzero remainder remains unchanged in the final signed-error
reduction. No bound for that remainder or RestrictedMediumObligation is
assumed or asserted. The displayed four-logarithm budget is a conclusion
of the three actual paid discrepancies, not a caller premise.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical
open scoped BigOperators
open TransposedZeroCovariance TransposedZeroPayment TransposedPrimitiveVPayment

namespace TransposedZeroUVPayment

theorem actual_energy_sub_nonzero_abs_le
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    |(∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      d.transposedAtom.commonSmoothWeight m *
        ‖d.transposedAtom.complexCenteredRow m‖ ^ 2) -
          d.transposedAtom.complexCRTSmoothNonzeroPart.re| ≤
      ‖d.transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain d‖ +
        2 * ‖(d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
          d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ +
            ‖(d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
              d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d‖ := by
  let E : ℝ := ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
    d.transposedAtom.commonSmoothWeight m * ‖d.transposedAtom.complexCenteredRow m‖ ^ 2
  let Z : ℂ := d.transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain d
  let V : ℂ := (d.transposedAtom.complexDispersionV d.transposedAtom.commonSmoothCarrier
    d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d
  let U : ℂ := (d.transposedAtom.complexDispersionU d.transposedAtom.commonSmoothCarrier
    d.transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain d
  let N : ℂ := d.transposedAtom.complexCRTSmoothNonzeroPart
  have he : (E : ℂ) = Z - 2 * V + U + N := actual_centered_identity_with_primitive hd
  have hre : E = (Z - 2 * V + U).re + N.re := by
    simpa only [Complex.ofReal_re, Complex.add_re] using congrArg Complex.re he
  have hsub : E - N.re = (Z - 2 * V + U).re := sub_eq_iff_eq_add.mpr hre
  change |E - N.re| ≤ ‖Z‖ + 2 * ‖V‖ + ‖U‖
  rw [hsub]
  apply (Complex.abs_re_le_norm _).trans
  calc
    _ ≤ ‖Z - 2 * V‖ + ‖U‖ := norm_add_le _ _
    _ ≤ (‖Z‖ + ‖(2 : ℂ) * V‖) + ‖U‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by
      rw [norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]

/-- Every actual primitive-center error has been paid. All family indices
are quantified after the one common threshold and original SW constants. -/
theorem actual_betaL2_mul_zero_UV_log_payment {ι : Type*} (F : ι → MediumAtom)
    (B C0 : ℕ) (sigma kappa c0 A : ℝ) (hA : 0 < A) (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
        (‖(F i).transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain (F i)‖ +
          2 * ‖((F i).transposedAtom.complexDispersionV
            (F i).transposedAtom.commonSmoothCarrier
              (F i).transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain (F i)‖ +
            ‖((F i).transposedAtom.complexDispersionU
              (F i).transposedAtom.commonSmoothCarrier
                (F i).transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain (F i)‖) ≤
                  4 * ((F i).scale ^ 2 / Real.log (F i).scale ^ A) := by
  obtain ⟨xZ, hxZ, hZ⟩ :=
    actual_betaL2_mul_rawZero_log_payment F B C0 sigma kappa c0 A hA hsigma
      hadmissible hSW
  obtain ⟨xUV, _hxUV, hUV⟩ :=
    actual_betaL2_mul_UV_error_log_payment B sigma kappa c0 A hsigma
  refine ⟨max xZ xUV, lt_of_lt_of_le hxZ (le_max_left _ _), fun i hx ↦ ?_⟩
  have hz := hZ i ((le_max_left _ _).trans hx)
  have huv := hUV (F i) (hadmissible i) ((le_max_right _ _).trans hx)
  calc
    _ = (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
        ‖(F i).transposedAtom.complexCRTSmoothZeroPart - primitiveZeroMain (F i)‖ +
          (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
            (‖((F i).transposedAtom.complexDispersionU
              (F i).transposedAtom.commonSmoothCarrier
                (F i).transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain (F i)‖ +
                  2 * ‖((F i).transposedAtom.complexDispersionV
                    (F i).transposedAtom.commonSmoothCarrier
                      (F i).transposedAtom.commonSmoothWeight : ℂ) - primitiveZeroMain (F i)‖) :=
      by ring
    _ ≤ (F i).scale ^ 2 / Real.log (F i).scale ^ A +
        3 * ((F i).scale ^ 2 / Real.log (F i).scale ^ A) := add_le_add hz huv
    _ = _ := by ring

theorem actual_betaL2_mul_energy_sub_nonzero_log_payment {ι : Type*}
    (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 A : ℝ)
    (hA : 0 < A) (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
        |(∑ m ∈ (F i).transposedAtom.commonSmoothCarrier,
          (F i).transposedAtom.commonSmoothWeight m *
            ‖(F i).transposedAtom.complexCenteredRow m‖ ^ 2) -
              (F i).transposedAtom.complexCRTSmoothNonzeroPart.re| ≤
                4 * ((F i).scale ^ 2 / Real.log (F i).scale ^ A) := by
  obtain ⟨x0, hx0, hbound⟩ :=
    actual_betaL2_mul_zero_UV_log_payment F B C0 sigma kappa c0 A hA hsigma
      hadmissible hSW
  refine ⟨x0, hx0, fun i hx ↦ ?_⟩
  exact (mul_le_mul_of_nonneg_left (actual_energy_sub_nonzero_abs_le (hadmissible i))
    (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))).trans (hbound i hx)

/-- A genuine reduction for the original signed error. Its full signed
nonzero remainder is the only term left on the right besides a proved
logarithmic error; no bound for that remainder is inserted as a premise. -/
theorem actual_signedError_sq_le_nonzero_add_log_payment {ι : Type*}
    (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 A : ℝ)
    (hA : 0 < A) (hsigma : 0 < sigma)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      ‖(F i).signedError‖ ^ 2 ≤
        (∑ n ∈ (F i).betaCarrier, ‖(F i).beta n‖ ^ 2) *
          (F i).transposedAtom.complexCRTSmoothNonzeroPart.re +
            4 * ((F i).scale ^ 2 / Real.log (F i).scale ^ A) := by
  obtain ⟨x0, hx0, hbound⟩ :=
    actual_betaL2_mul_energy_sub_nonzero_log_payment F B C0 sigma kappa c0 A hA
      hsigma hadmissible hSW
  refine ⟨x0, hx0, fun i hx ↦ ?_⟩
  let d : MediumAtom := F i
  let b : ℝ := ∑ n ∈ d.betaCarrier, ‖d.beta n‖ ^ 2
  let E : ℝ := ∑ m ∈ d.transposedAtom.commonSmoothCarrier,
    d.transposedAtom.commonSmoothWeight m * ‖d.transposedAtom.complexCenteredRow m‖ ^ 2
  let N : ℝ := d.transposedAtom.complexCRTSmoothNonzeroPart.re
  have hb : 0 ≤ b := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hc : ‖d.signedError‖ ^ 2 ≤ b * E := by
    have h := d.signedError_norm_sq_le_transposedCommonSmoothDispersion (hadmissible i).2.1
    rw [← d.transposedAtom.complex_dispersion_identity
      d.transposedAtom.commonSmoothCarrier d.transposedAtom.commonSmoothWeight] at h
    exact h
  have hdiff : b * (E - N) ≤ 4 * (d.scale ^ 2 / Real.log d.scale ^ A) :=
    (mul_le_mul_of_nonneg_left (le_abs_self (E - N)) hb).trans (hbound i hx)
  calc
    _ ≤ b * E := hc
    _ = b * N + b * (E - N) := by ring
    _ ≤ _ := add_le_add le_rfl hdiff

end TransposedZeroUVPayment

end

end ImbalancedChen.Part3
