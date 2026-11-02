import ImbalancedChen.Part3OriginalLinearDiscardCountPayment
import ImbalancedChen.Part3OriginalPaidS123Entrance
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Consume the actual linear discard payment in G's independently defined
complete S1/S2/S3 entrance. No remaining spectral, Poisson, rough or
restoration estimate is assumed. The B=0 branch and every unpaid packet
are explicit. This is not a RestrictedMediumTarget theorem.
-/

namespace ImbalancedChen.Part3.OriginalS123PaidLinearEntrance20261102
noncomputable section
open Classical Finset
open scoped BigOperators
open ActualRoughContourParameters20261026b ActualMediumVarianceAtomBindingSourceOnly
open MediumReceiverCutoffArithmetic20261028 MediumActualPreliminaryCauchy20261028
open MediumGlobalDyadicOwnership20261028 MediumActualS3ZeroCentering20261028
open OriginalS1OuterCauchy20261028 OriginalPaidS123Entrance20261028
open OriginalLinearDiscardCountPayment20261102
open OriginalPoissonSourceCorrections20261028 OriginalPoissonZeroCenteringCaller20261028
open OriginalWholePoissonCarrierReindex20261028
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open MediumPrimitiveShiuWindow20261028

/-- S1/P, S2 zero-Gram, exact-product entrance and the actual LINEAR
smooth discard now share one threshold in the original B=0 branch.
Original outerL2, the second owner-bank cardinality, all signs and the
factor two on S2 remain unchanged. Every unpaid residual remains literal. -/
theorem uniformAuxiliarySW_one_bounded_original_signed_source_paid_linear_entrance
    {ι : Type*} (F : ι → MediumAtom) (C0 : ℕ) (σ κ c0 : ℝ)
    (hadmissible : ∀ i, MediumAdmissible 0 σ κ c0 (F i))
    (hSW : UniformAuxiliarySW F C0) (hσ : 0 < σ) (hc0 : 0 < c0)
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
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
    uniformAuxiliarySW_original_signed_source_with_paid_entrance F 0 C0 σ κ c0
      hadmissible hSW hσ hc0 A hA
  obtain ⟨Cd, hCd, Xd, hXd, hdiscard⟩ :=
    original_one_bounded_linear_discard_log_payment hShiu (A / 2) (by linarith)
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
end ImbalancedChen.Part3.OriginalS123PaidLinearEntrance20261102
