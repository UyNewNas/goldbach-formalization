import ImbalancedChen.Part3SharedFirstFactorZeroCovariancePayment
import ImbalancedChen.Part3SharedFirstFactorPrimitiveUVPayment

/-!
# The actual shared energy after zero and primitive U/V payment

All sums retain the original primitive first-factor carrier, original-V
common smoothing and actual complex point-mass slices. The exact finite
identity cancels the same slice's primitive center before any norm.

Both actual outside L2 factors have already been paid by the two parents.
The uniform constant is CZero+3 and its threshold precedes every atom.
The final squared-error reduction retains the real part of the complete
sum of the same-p nonzero Poisson terms. No estimate of that term is
assumed or proved here. A later final error budget A requires both the
energy remainder and the genuine nonzero estimate at budget 2*A.
-/

namespace ImbalancedChen.Part3

noncomputable section

open Classical Finset
open scoped BigOperators

/-- The full complex energy minus the full same-p nonzero sum is exactly
the actual zero covariance plus the parenthesized primitive U/V sum. -/
theorem MediumAtom.sharedFirstFactorEnergy_sub_nonzero_eq_zeroCovariance_add_UV
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) :
    ((∑ p ∈ d.primitiveFirstFactorCarrier,
      (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
        (d.transposedAtom.commonSmoothWeight m *
          ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2)) : ℝ) : ℂ) -
        (∑ p ∈ d.primitiveFirstFactorCarrier,
          ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart)) =
      (∑ p ∈ d.primitiveFirstFactorCarrier,
        ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
          TransposedZeroCovariance.primitiveZeroMain (d.q1SliceAtom p))) +
        d.sharedPrimitiveUVError := by
  rw [d.sharedFirstFactor_centered_identity hd]
  unfold MediumAtom.sharedPrimitiveUVError
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A proved family payment for energy minus the actual nonzero part.
No energy estimate or nonzero-frequency estimate is a caller premise. -/
theorem uniformAuxiliarySW_sharedFirstFactorEnergy_sub_nonzero_log_payment
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1 / 100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma / 100)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale →
          ((∑ n ∈ (F i).betaCarrier, (‖(F i).beta n‖ ^ 2)) *
            (∑ p ∈ (F i).primitiveFirstFactorCarrier, (‖(F i).gamma1 p‖ ^ 2))) *
            ‖((∑ p ∈ (F i).primitiveFirstFactorCarrier,
                (∑ m ∈ (F i).transposedAtom.commonSmoothCarrier,
                  ((F i).transposedAtom.commonSmoothWeight m *
                    ‖((F i).q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2)) : ℝ) : ℂ) -
              (∑ p ∈ (F i).primitiveFirstFactorCarrier,
                (((F i).q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart))‖ ≤
              C * (F i).scale ^ 2 / (Real.log (F i).scale) ^ A := by
  intro A hA
  obtain ⟨CZ, hCZ, xZ, hxZ, hZero⟩ :=
    uniformAuxiliarySW_sharedFirstFactorZeroCovariance F B C0 sigma kappa c0
      hsigma hsigma_small hc0 hkappa hkappa_small hadmissible hSW A hA
  obtain ⟨xUV, _hxUV, hUV⟩ :=
    actual_betaL2_gamma1L2_sharedPrimitiveUV_log_payment B sigma kappa c0 A hsigma
  refine ⟨CZ + 3, by linarith, max xZ xUV, hxZ.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  let d := F i
  let W : ℝ := (∑ n ∈ d.betaCarrier, (‖d.beta n‖ ^ 2)) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, (‖d.gamma1 p‖ ^ 2))
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hz := hZero i ((le_max_left xZ xUV).trans hx)
  have huv := hUV d (hadmissible i) ((le_max_right xZ xUV).trans hx)
  rw [d.sharedFirstFactorEnergy_sub_nonzero_eq_zeroCovariance_add_UV (hadmissible i)]
  calc
    _ ≤ W * (‖∑ p ∈ d.primitiveFirstFactorCarrier,
          ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
            TransposedZeroCovariance.primitiveZeroMain (d.q1SliceAtom p))‖ +
        ‖d.sharedPrimitiveUVError‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) hW
    _ = W * ‖∑ p ∈ d.primitiveFirstFactorCarrier,
          ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothZeroPart -
            TransposedZeroCovariance.primitiveZeroMain (d.q1SliceAtom p))‖ +
        W * ‖d.sharedPrimitiveUVError‖ := mul_add _ _ _
    _ ≤ CZ * d.scale ^ 2 / (Real.log d.scale) ^ A +
        3 * (d.scale ^ 2 / (Real.log d.scale) ^ A) := add_le_add hz huv
    _ = _ := by ring

/-- The remaining term is the real part of the full sum of the actual
same-p Poisson remainders, with both original outside moments retained. -/
theorem uniformAuxiliarySW_sharedFirstFactor_signedError_sq_le_nonzero_add_log_payment
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (sigma kappa c0 : ℝ)
    (hsigma : 0 < sigma) (hsigma_small : sigma < 1 / 100)
    (hc0 : 0 < c0) (hkappa : 0 ≤ kappa) (hkappa_small : kappa ≤ sigma / 100)
    (hadmissible : ∀ i, MediumAdmissible B sigma kappa c0 (F i))
    (hSW : UniformAuxiliarySW F C0) :
    ∀ A : ℝ, 0 < A →
      ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧
        ∀ i : ι, x0 ≤ (F i).scale →
          ‖(F i).signedError‖ ^ 2 ≤
            ((∑ n ∈ (F i).betaCarrier, (‖(F i).beta n‖ ^ 2)) *
              (∑ p ∈ (F i).primitiveFirstFactorCarrier, (‖(F i).gamma1 p‖ ^ 2))) *
              (∑ p ∈ (F i).primitiveFirstFactorCarrier,
                (((F i).q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart)).re +
                C * (F i).scale ^ 2 / (Real.log (F i).scale) ^ A := by
  intro A hA
  obtain ⟨C, hC, x0, hx0, hbound⟩ :=
    uniformAuxiliarySW_sharedFirstFactorEnergy_sub_nonzero_log_payment
      F B C0 sigma kappa c0 hsigma hsigma_small hc0 hkappa hkappa_small hadmissible hSW A hA
  refine ⟨C, hC, x0, hx0, ?_⟩
  intro i hx
  let d := F i
  let W : ℝ := (∑ n ∈ d.betaCarrier, (‖d.beta n‖ ^ 2)) *
    (∑ p ∈ d.primitiveFirstFactorCarrier, (‖d.gamma1 p‖ ^ 2))
  let E : ℝ := ∑ p ∈ d.primitiveFirstFactorCarrier,
    (∑ m ∈ d.transposedAtom.commonSmoothCarrier,
      (d.transposedAtom.commonSmoothWeight m *
        ‖(d.q1SliceAtom p).transposedAtom.complexCenteredRow m‖ ^ 2))
  let N : ℂ := ∑ p ∈ d.primitiveFirstFactorCarrier,
    ((d.q1SliceAtom p).transposedAtom.complexCRTSmoothNonzeroPart)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hc : ‖d.signedError‖ ^ 2 ≤ W * E :=
    d.signedError_norm_sq_le_sharedFirstFactorSmoothRows (hadmissible i)
  have hre : |E - N.re| ≤ ‖(E : ℂ) - N‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm ((E : ℂ) - N)
  have hdiff : W * (E - N.re) ≤ C * d.scale ^ 2 / (Real.log d.scale) ^ A := by
    calc
      _ ≤ W * |E - N.re| := mul_le_mul_of_nonneg_left (le_abs_self _) hW
      _ ≤ W * ‖(E : ℂ) - N‖ := mul_le_mul_of_nonneg_left hre hW
      _ ≤ _ := hbound i hx
  calc
    _ ≤ W * E := hc
    _ = W * N.re + W * (E - N.re) := by ring
    _ ≤ _ := add_le_add le_rfl hdiff

end

end ImbalancedChen.Part3
