import ImbalancedChen.Part3OriginalLinearGeneralBetaPayment
import ImbalancedChen.Part3OriginalPaidS123Entrance
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Arbitrary fixed original beta divisor order at the actual signed S123
entrance. The G source/ledger is retained literally. No estimate of the
remaining Poisson/spectral/rough/restoration packets is assumed here.
-/

namespace ImbalancedChen.Part3.OriginalS123GeneralBetaPaidLinearEntrance20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open ActualRoughContourParameters20261026b ActualMediumVarianceAtomBindingSourceOnly
open MediumReceiverCutoffArithmetic20261028 MediumActualPreliminaryCauchy20261028
open MediumGlobalDyadicOwnership20261028 MediumActualS3ZeroCentering20261028
open OriginalS1OuterCauchy20261028 OriginalPaidS123Entrance20261028
open OriginalLinearGeneralBetaPayment20261102
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open MediumPrimitiveShiuWindow20261028

/-- S1/P, S2 zero-Gram, exact-product entrance and the physical LINEAR
smooth discard share one threshold for EVERY fixed original B. The
unchanged residual retains each signed packet, outerL2, key multiplicity
and the factor two on S2. This is not RestrictedMediumTarget. -/
theorem uniformAuxiliarySW_general_beta_original_signed_source_paid_linear_entrance
    {ι : Type*} (F : ι → MediumAtom) (B C0 : ℕ) (σ κ c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible B σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary (B + 1) (1 / 10 : ℝ) (1 / 10 : ℝ))
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
        C * atom.scale ^ 2 / Real.log atom.scale ^ A := by
  obtain ⟨Ce, hCe, Xe, hXe, hentrance⟩ :=
    uniformAuxiliarySW_original_signed_source_with_paid_entrance F B C0 σ κ c0
      hadmissible hSW hσ hc0 A hA
  obtain ⟨Cd, hCd, Xd, hXd, hdiscard⟩ :=
    original_general_beta_linear_discard_log_payment B hShiu (A / 2) (by linarith)
  refine ⟨Ce + 3 * Cd ^ 2, by positivity, max (max Xe Xd) (Real.exp 1),
    hXe.trans_le ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro i hx
  dsimp only
  let atom := F i
  have hleft : max Xe Xd ≤ atom.scale := (le_max_left _ _).trans hx
  have he := hentrance i ((le_max_left _ _).trans hleft)
  have hd := hdiscard σ κ c0 atom (hadmissible i) hσ.le hc0 ((le_max_right _ _).trans hleft)
  have hlog : 1 ≤ Real.log atom.scale := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
      ((le_max_right _ _).trans hx)
  have hlogpos : 0 < Real.log atom.scale := by linarith
  have hxpos : 0 < atom.scale := zero_lt_one.trans_le
    (TransposedPrimitiveUPayment.one_le_scale (hadmissible i))
  have hpow : (Real.log atom.scale ^ (A / 2)) ^ 2 = Real.log atom.scale ^ A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlogpos.le]
    congr 1
    ring
  have hdSq : ‖discardedSource atom (strictReceiverCutoff (roughZ atom.scale))
      (originalSmoothTrim atom)‖ ^ 2 ≤ Cd ^ 2 * atom.scale ^ 2 / Real.log atom.scale ^ A := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hd
    simpa only [originalSmoothTrim, div_pow, mul_pow, hpow] using hs
  nlinarith

end
end ImbalancedChen.Part3.OriginalS123GeneralBetaPaidLinearEntrance20261102
