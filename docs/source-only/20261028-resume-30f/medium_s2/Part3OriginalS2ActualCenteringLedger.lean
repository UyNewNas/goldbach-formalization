import ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
import ImbalancedChen.Part3OriginalS2NativeZeroGramBudget
import ImbalancedChen.Part3OriginalS1NativeMain
import Mathlib.Tactic

/-! Actual S2 source ledger and the paid smooth/zero-Gram part.
The genuine other-rough and single-zero corrections are kept in the
primitive S2 identity. Neither those corrections nor a finite E1 spectral
estimate are assumed negligible. SOURCE ONLY / UNCOMPILED / ZERO CREDIT. -/

namespace ImbalancedChen.Part3OriginalS2ActualCenteringLedger

open ImbalancedChen.Part3
open ImbalancedChen.Part3.ActualRoughContourParameters20261026b
open ImbalancedChen.Part3OriginalS2PaperBlockEmbedding
open ImbalancedChen.Part3OriginalS2PrimitiveLiteralDictionary
open ImbalancedChen.Part3OriginalS2ActualPoissonZeroMode
open ImbalancedChen.Part3OriginalS2SameSourcePrincipal
open ImbalancedChen.Part3OriginalS2NativePhysicalRange
open ImbalancedChen.Part3OriginalS2NativeZeroGramBudget
open ImbalancedChen.Part3OriginalS2FixedDMixedTail
open ImbalancedChen.Part3.MediumNativePrincipalSource20261028
open ImbalancedChen.Part3.MediumLiteralS3Stages20261028
open ImbalancedChen.Part3.MediumGlobalDyadicOwnership20261028
open ImbalancedChen.Part3.MediumReceiverCutoffArithmetic20261028
open ImbalancedChen.Part3.MediumPrimitiveShiuWindow20261028
open ImbalancedChen.Part3.OriginalS1NativeMain20261028
open ImbalancedChen.Part3.OriginalPrimitiveS1Atlas
open Classical

noncomputable section

/-- Same source MT, with every genuine unestimated S2 correction visible. -/
theorem actual_primitive_S2_centered_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    primitiveS2 d z y k - (nativeMT d z y k).re =
      (actualS2NonzeroModes d z y k).re + (actualZeroGramError d z y k).re -
        (otherRoughCorrection d z y k).re - (singleZeroCorrection d z y k).re := by
  have hp := actual_preliminary_S2_zero_mode_identity hd z y k
  rw [actualS2ZeroMode_eq_nativeMT_add_error hd, Complex.add_re] at hp
  linarith

/-- Finite same-source centering with the independently defined actual
S1 and independently centered S3 principal model. No variance bound is
used, and the full restored S3 model is not called its clean/offdiag part. -/
theorem actual_S1_S2zero_restoredS3_model_centering
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z y : ℝ) (k : Key) :
    primitiveS1 d z y k - 2 * (actualS2ZeroMode d z y k).re +
        (nativeRestoredZero d z y k).re =
      nativeP d z y k + (primitiveAtlasRemainder d z y k hd).re -
        2 * (actualZeroGramError d z y k).re := by
  have hS1 := congrArg Complex.re (original_S1_eq_nativeMT_add_remainder d z y k hd)
  simp only [Complex.ofReal_re, Complex.add_re] at hS1
  have hS2 := congrArg Complex.re (actualS2ZeroMode_eq_nativeMT_add_error hd z y k)
  simp only [Complex.add_re] at hS2
  have hS3 := nativeRestoredZero_re_eq_MT_add_P d z y k (zero_lt_one.trans_le hd.2.2.1)
  linarith

def paidSmoothAndGram (d : MediumAtom) (z : ℝ) (k : Key) : ℂ :=
  actualZeroGramError d (strictReceiverCutoff z) (roughY d.scale) k +
    keyMixedTailSum d d.scale z k

theorem actual_full_receiver_Poisson_centered_identity
    {B : ℕ} {sigma kappa c0 : ℝ} {d : MediumAtom}
    (hd : MediumAdmissible B sigma kappa c0 d) (z : ℝ) (hz : 0 ≤ z) (k : Key) :
    (keyFullRestoredSum d d.scale z k).re =
      (nativeMT d (strictReceiverCutoff z) (roughY d.scale) k).re +
        (actualS2NonzeroModes d (strictReceiverCutoff z) (roughY d.scale) k).re +
          (paidSmoothAndGram d z k).re := by
  rw [keyFullRestoredSum_eq_actual_kept_add_tail hd d.scale z hz k, Complex.add_re,
    restoredSum_eq_actual_zero_add_nonzero hd,
    actualS2ZeroMode_eq_nativeMT_add_error hd]
  simp only [Complex.add_re, paidSmoothAndGram]
  ring

/-- Both paid errors have their actual source dictionaries. Their
uniform arbitrary-log budget keeps one whole d~D family and V(D). -/
theorem exists_paidSmoothAndGram_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → X ≤ d.scale →
        ‖paidSmoothAndGram d (roughZ d.scale) k‖ ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨Cg, Xg, hCg, hXg, hg⟩ := exists_actualZeroGramError_arbitrary_log A hA
  obtain ⟨Ct, Xt, hCt, hXt, ht⟩ := exists_actual_mixedTail_payment_original_range hShiu A hA
  refine ⟨Cg + Ct, max Xg Xt, by linarith,
    hXg.trans_le (le_max_left _ _), ?_⟩
  intro B sigma kappa c0 d k hd hsigma hc0 hx
  have hg' := hg B sigma kappa c0 d k hd hsigma hc0 ((le_max_left _ _).trans hx)
  have ht' := ht B sigma kappa c0 d k hd hsigma hc0 ((le_max_right _ _).trans hx)
  exact (norm_add_le _ _).trans (by
    dsimp [paidSmoothAndGram]
    nlinarith [hg', ht'])

/-- The full receiver source minus its exact MT and complete nonzero
Poisson packet now has the original arbitrary-log scale. The separately
named primitive-source rough/single-zero corrections are still required
when this is inserted into the original dispersion inequality. -/
theorem exists_actual_full_receiver_centered_arbitrary_log
    (hShiu : PrimitiveShiuTauBoundary 1 (1 / 10 : ℝ) (1 / 10 : ℝ))
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C X : ℝ, 0 < C ∧ Real.exp (Real.exp 1) < X ∧
      ∀ (B : ℕ) (sigma kappa c0 : ℝ) (d : MediumAtom) (k : Key),
        MediumAdmissible B sigma kappa c0 d → 0 ≤ sigma → 0 < c0 → X ≤ d.scale →
        |(keyFullRestoredSum d d.scale (roughZ d.scale) k).re -
          ((nativeMT d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re +
            (actualS2NonzeroModes d (strictReceiverCutoff (roughZ d.scale)) (roughY d.scale) k).re)| ≤
          C * (fixedDScale d ((2 : ℝ) ^ k.d) * (Real.log d.scale) ^ (-A)) := by
  obtain ⟨C, X, hC, hX, hbound⟩ := exists_paidSmoothAndGram_arbitrary_log hShiu A hA
  refine ⟨C, X, hC, hX, ?_⟩
  intro B sigma kappa c0 d k hd hsigma hc0 hx
  have hz : 0 ≤ roughZ d.scale := Real.rpow_nonneg (by
    dsimp [MediumAtom.scale]
    have hU : 0 ≤ d.U := by linarith [hd.1]
    have hV : 0 ≤ d.V := by linarith [hd.2.1]
    positivity) _
  rw [actual_full_receiver_Poisson_centered_identity hd (roughZ d.scale) hz k,
    add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans (hbound B sigma kappa c0 d k hd hsigma hc0 hx)

end
end ImbalancedChen.Part3OriginalS2ActualCenteringLedger
