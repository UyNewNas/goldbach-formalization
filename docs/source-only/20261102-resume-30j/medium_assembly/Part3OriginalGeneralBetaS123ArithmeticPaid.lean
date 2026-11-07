import ImbalancedChen.Part3OriginalS123GeneralBetaPaidLinearEntrance
import ImbalancedChen.Part3OriginalS123CombinedArithmeticPayment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Consume the frozen I general-B physical LINEAR discard and the distinct
all-key S2/S3 arithmetic payments in the original signed S123 entrance.
No residual, retained-source or spectral bound is a hypothesis.
-/

namespace ImbalancedChen.Part3.OriginalGeneralBetaS123ArithmeticPaid20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open OriginalS123GeneralBetaPaidLinearEntrance20261102
open OriginalS123CombinedArithmeticPayment20261102
open ActualRoughContourParameters20261026b
open ActualMediumVarianceAtomBindingSourceOnly OriginalS1OuterCauchy20261028
open MediumReceiverCutoffArithmetic20261028 MediumGlobalDyadicOwnership20261028
open MediumActualPreliminaryCauchy20261028 MediumActualS3ZeroCentering20261028
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open MediumPrimitiveShiuWindow20261028

/-- Every fixed original B now has one family-uniform entrance paying
S1/P, zero-Gram, exact products, the physical LINEAR discard, the distinct
mean-weighted S2 single zero, and the S3 diagonal/two-single-zero packet.
All remaining signed terms, outer weights and the factor two on S2 are
literal original sources. This theorem does not prove their smallness. -/
theorem uniformAuxiliarySW_general_beta_original_signed_source_arithmetic_paid
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (σ κ c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hσsmall : σ < 1 / 100)
    (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ x0 : ℝ, 1 < x0 ∧ ∀ i, x0 ≤ (F i).scale →
      let atom := F i
      let z := roughZ atom.scale
      let receiver := strictReceiverCutoff z
      let y := originalSmoothTrim atom
      let K := originalNumericKeys atom z
      ‖atom.signedError‖ ^ 2 ≤ 3 * (K.card : ℝ) * ∑ k ∈ K, outerL2 atom k *
        ((retainedSourceKey atom z y k).re + (offDiagonalOmitted atom z y k).re -
          (diagonalRetained atom z y k).re + (roughReplacementCorrection atom receiver y k).re -
          (genuineDiagonalZero atom receiver y k).re -
          2 * ((actualS2NonzeroModes atom receiver y k).re -
            (otherRoughCorrection atom receiver y k).re)) +
        C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Ce, hCe, Xe, hXe, hentrance⟩ :=
    uniformAuxiliarySW_general_beta_original_signed_source_paid_linear_entrance
      F B C0 σ κ c0 hadmissible hSW hσ hc0 hShiu A hA
  obtain ⟨Cc, hCc, Xc, hXc, hcorrections⟩ :=
    original_all_key_S2_S3_correction_log_payment B σ κ A hσ hσsmall
  refine ⟨Ce + 3 * Cc, by positivity, max Xe Xc,
    hXe.trans_le (le_max_left _ _), ?_⟩
  intro i hx
  dsimp only
  let atom := F i
  let z := roughZ atom.scale
  have hxpos : 0 < atom.scale := zero_lt_one.trans_le
    (TransposedPrimitiveUPayment.one_le_scale (hadmissible i))
  have hz : 0 ≤ z := Real.rpow_nonneg hxpos.le _
  have he := hentrance i ((le_max_left _ _).trans hx)
  have hc := hcorrections c0 atom (hadmissible i) hc0
    ((le_max_right _ _).trans hx) z hz
  have hs := original_signed_packets_le_after_S2_S3_split atom z (fun _ => 0)
  simp only [add_zero] at hs
  nlinarith

end
end ImbalancedChen.Part3.OriginalGeneralBetaS123ArithmeticPaid20261102
