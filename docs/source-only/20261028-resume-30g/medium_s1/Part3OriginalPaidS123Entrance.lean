import ImbalancedChen.Part3OriginalAllKeyS2GramPayment
import ImbalancedChen.Part3OriginalEntranceExactProductPayment
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Put the independently paid S1/P, actual S2 Gram mismatch and original
linear exact-product entrance correction into ONE original source bound.
The physical S3/S2/spectral packets and smooth discard remain literally.
No remaining-packet estimate or bare restricted-medium bound is assumed.
-/

namespace ImbalancedChen.Part3.OriginalPaidS123Entrance20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open ActualRoughContourParameters20261026b ActualMediumVarianceAtomBindingSourceOnly
open MediumReceiverCutoffArithmetic20261028 MediumActualPreliminaryCauchy20261028
open MediumGlobalDyadicOwnership20261028 MediumActualS3ZeroCentering20261028
open OriginalS1OuterCauchy20261028 OriginalCompleteS123Ledger20261028
open OriginalAllKeyS2GramPayment20261028 OriginalEntranceExactProductPayment20261028
open OriginalPrincipalVarianceInOuterCauchy20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary

/-- Remove exactly the actual S2 Gram mismatch from the true ledger,
using its norm with the original coefficient 2. Every other packet keeps
its original sign and original common q/d/alpha/lambda/profile source. -/
theorem actualResidualFunctional_le_without_Gram_add_paid_budget
    {B : ℕ} {σ κ c0 : ℝ} (atom : MediumAtom)
    (hA : MediumAdmissible B σ κ c0 atom) :
    let z := roughZ atom.scale
    let receiver := strictReceiverCutoff z
    let y := originalSmoothTrim atom
    let K := originalNumericKeys atom z
    actualResidualFunctional atom z ≤ (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
      ((retainedSourceKey atom z y k).re + (remainingCorrectionKey atom z y k).re +
        (roughReplacementCorrection atom receiver y k).re -
        (genuineDiagonalZero atom receiver y k).re -
        2 * ((actualS2NonzeroModes atom receiver y k).re -
          (otherRoughCorrection atom receiver y k).re -
          (singleZeroCorrection atom receiver y k).re)) + actualOuterZeroGramBudget atom := by
  dsimp only
  rw [actualResidualFunctional_eq_complete_original_packets atom _ hA]
  let z := roughZ atom.scale
  let receiver := strictReceiverCutoff z
  let y := originalSmoothTrim atom
  let K := originalNumericKeys atom z
  calc
    _ ≤ (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
        (((retainedSourceKey atom z y k).re + (remainingCorrectionKey atom z y k).re +
          (roughReplacementCorrection atom receiver y k).re -
          (genuineDiagonalZero atom receiver y k).re -
          2 * ((actualS2NonzeroModes atom receiver y k).re -
            (otherRoughCorrection atom receiver y k).re -
            (singleZeroCorrection atom receiver y k).re)) +
          2 * ‖actualZeroGramError atom receiver y k‖) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (outerL2_nonneg atom k)
      have hn : -(actualZeroGramError atom receiver y k).re ≤
          ‖actualZeroGramError atom receiver y k‖ := by
        simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm
          (-actualZeroGramError atom receiver y k)
      linarith
    _ = _ := by
      unfold actualOuterZeroGramBudget
      simp only [mul_add, sum_add_distrib, mul_sum]
      ring

/-- One common threshold, chosen before every atom/residue/key, combines
all already paid original contributions. The RHS still exposes the
genuine unestimated S2/S3/Poisson/spectral packets and linear discard;
there is deliberately no RestrictedMediumTarget conclusion. -/
theorem uniformAuxiliarySW_original_signed_source_with_paid_entrance
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (σ κ c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hc0 : 0 < c0)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      let atom := F i
      let z := roughZ atom.scale
      let receiver := strictReceiverCutoff z
      let y := originalSmoothTrim atom
      let K := originalNumericKeys atom z
      ‖atom.signedError‖ ^ 2 ≤ 3 * (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
        ((retainedSourceKey atom z y k).re + (remainingCorrectionKey atom z y k).re +
          (roughReplacementCorrection atom receiver y k).re -
          (genuineDiagonalZero atom receiver y k).re -
          2 * ((actualS2NonzeroModes atom receiver y k).re -
            (otherRoughCorrection atom receiver y k).re -
            (singleZeroCorrection atom receiver y k).re)) +
        C * atom.scale ^ 2 / Real.log atom.scale ^ A +
          3 * ‖discardedSource atom receiver y‖ ^ 2 := by
  obtain ⟨Cp, hCp, xp, hxp, hP⟩ :=
    uniformAuxiliarySW_original_source_sq_le_residual_add_log_error F B C0 σ κ c0
      hadmissible hSW hσ A hA
  obtain ⟨Cg, hCg, xg, hxg, hG⟩ := original_all_key_S2_Gram_log_payment B A hA.le
  obtain ⟨xe, hxe, hE⟩ := original_exactProductCorrection_log_payment B σ κ c0 (A / 2) hσ hc0
  refine ⟨3 * (Cp + Cg + 1), by positivity,
    max (max xp xg) (max xe (Real.exp 1)),
    hxp.trans_le ((le_max_left xp xg).trans (le_max_left _ _)), ?_⟩
  intro i hx
  dsimp only
  let atom := F i
  let z := roughZ atom.scale
  let receiver := strictReceiverCutoff z
  let y := originalSmoothTrim atom
  let K := originalNumericKeys atom z
  have hxl : max xp xg ≤ atom.scale := (le_max_left _ _).trans hx
  have hxr : max xe (Real.exp 1) ≤ atom.scale := (le_max_right _ _).trans hx
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hxr)
  have hlogpos : 0 < Real.log atom.scale := by linarith
  have hxpos : 0 < atom.scale := zero_lt_one.trans_le
    (TransposedPrimitiveUPayment.one_le_scale (hadmissible i))
  have hz : 0 ≤ z := Real.rpow_nonneg hxpos.le _
  have hp := hP i ((le_max_left _ _).trans hxl) z hz
  have hg := hG σ κ c0 atom (hadmissible i) hσ.le hc0 ((le_max_right _ _).trans hxl)
  have he := hE atom (hadmissible i) ((le_max_left _ _).trans hxr)
  have heSq : ‖exactProductCorrection atom‖ ^ 2 ≤
      atom.scale ^ 2 / Real.log atom.scale ^ A := by
    have hpow : (Real.log atom.scale ^ (A / 2)) ^ 2 = Real.log atom.scale ^ A := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le]
      congr 1
      ring
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr he
    simpa only [div_pow, hpow] using hs
  have hr := actualResidualFunctional_le_without_Gram_add_paid_budget atom (hadmissible i)
  have hentrance := original_signedError_norm_sq_le_entrance_terms atom z y hz
  nlinarith

end
end ImbalancedChen.Part3.OriginalPaidS123Entrance20261028
