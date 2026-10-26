import ImbalancedChen.Part3GammaActualCutoffCoreUniformEnergy

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Literal multiplication by the actual modular cutoff is a contraction on
the SAME physical Gamma0 quotient L2. Its representative identity is
proved, so a completed-form extension can be identified with the actual
cutoff product by dense-core continuity, rather than only by a name.
-/

namespace ImbalancedChen.Part3.GammaActualQuotientCutoffMultiplier20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open GammaSmoothMultiplierPeriodization20261026a GammaSmoothMultiplierLegalTests20261026a
open ActualModularCutoffMaassBudget20261025a GammaActualCutoffNativeGradientBudget20261026b

theorem quotientCutoffComplex_norm_le_one (N : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (q : Gamma0OrbitSpace N) :
    ‖quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) q‖ ≤ 1 :=
  Quotient.inductionOn q (fun z => actualCutoff_norm_le_one Y hY z)

private theorem quotientCutoffProduct_memLp (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : MemLp
      (fun q => quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) q * f q)
      2 (carrierPushforward N) := by
  apply (Lp.memLp f).of_le_mul
    ((quotientMultiplier_measurable N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y)
      (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (fun q => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (quotientCutoffComplex_norm_le_one N Y hY.le q) (norm_nonneg _))

def quotientCutoffProduct (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : QuotientL2 N :=
  (quotientCutoffProduct_memLp N Y hY f).toLp
    (fun q => quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) q * f q)

theorem quotientCutoffProduct_coe_ae (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) :
    quotientCutoffProduct N Y hY f =ᵐ[carrierPushforward N]
      quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) * f :=
  (quotientCutoffProduct_memLp N Y hY f).coeFn_toLp

def quotientCutoffProductLinear (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    QuotientL2 N →ₗ[ℂ] QuotientL2 N where
  toFun := quotientCutoffProduct N Y hY
  map_add' f g := by
    apply Lp.ext
    filter_upwards [quotientCutoffProduct_coe_ae N Y hY (f+g),Lp.coeFn_add f g,
      Lp.coeFn_add (quotientCutoffProduct N Y hY f) (quotientCutoffProduct N Y hY g),
      quotientCutoffProduct_coe_ae N Y hY f,quotientCutoffProduct_coe_ae N Y hY g]
      with q hleft hin hright hf hg
    simp only [Pi.mul_apply] at hleft hf hg
    rw [hleft,hright,hf,hg,hin]
    ring
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [quotientCutoffProduct_coe_ae N Y hY (c • f),Lp.coeFn_smul c f,
      Lp.coeFn_smul c (quotientCutoffProduct N Y hY f),quotientCutoffProduct_coe_ae N Y hY f]
      with q hleft hin hright hf
    simp only [Pi.mul_apply] at hleft hf
    rw [hleft,hright,hf,hin]
    simp only [smul_eq_mul]
    ring

theorem quotientCutoffProduct_norm_le (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y)
    (f : QuotientL2 N) : ‖quotientCutoffProduct N Y hY f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [quotientCutoffProduct_coe_ae N Y hY f] with q hq
  rw [hq,Pi.mul_apply,norm_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (quotientCutoffComplex_norm_le_one N Y hY.le q) (norm_nonneg (f q))

def actualQuotientCutoffMultiplier (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) :
    QuotientL2 N →L[ℂ] QuotientL2 N :=
  (quotientCutoffProductLinear N Y hY).mkContinuous 1
    (fun f => by simpa only [one_mul] using quotientCutoffProduct_norm_le N Y hY f)

theorem actualQuotientCutoffMultiplier_coe_ae
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    actualQuotientCutoffMultiplier N Y hY f =ᵐ[carrierPushforward N]
      quotientMultiplier N (complexGlobalH Y) (actualCutoff_isGammaInvariant N Y) * f :=
  quotientCutoffProduct_coe_ae N Y hY f

theorem actualQuotientCutoffMultiplier_norm_le
    (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    ‖actualQuotientCutoffMultiplier N Y hY f‖ ≤ ‖f‖ := quotientCutoffProduct_norm_le N Y hY f

end
end ImbalancedChen.Part3.GammaActualQuotientCutoffMultiplier20261026b
