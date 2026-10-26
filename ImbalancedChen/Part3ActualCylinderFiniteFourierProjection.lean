import ImbalancedChen.Part3ActualZeroMeanCylinderFourierUnitary

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Actual bounded, idempotent finite nonzero Fourier projections on the
weighted cylinder. Their coefficients and literal representatives are
computed. Convergence and contraction CONSUME the existing actual
cylinder Fourier unitary and its lp finite-single norm formula. This
does not repeat a Parseval, density, completeness, or onto proof.
-/
namespace ImbalancedChen.Part3.ActualCylinderFiniteFourierProjection20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
open CuspCylinderMeasure20261024z ActualCylinderModeEmbeddings20261026a
open ActualCylinderFourierCoefficients20261026a
open ActualZeroMeanCylinderFourierUnitary20261026a
open NonzeroCircleFourierUnitary20261026a (NonzeroMode)

def finiteFourierProjection (s : Finset NonzeroMode) : CylinderL2 →L[ℂ] CylinderL2 :=
  ∑ n ∈ s, (modeEmbedding (n : ℤ)).toContinuousLinearMap.comp (cylinderCoefficient n)

theorem finiteFourierProjection_apply (s : Finset NonzeroMode) (F : CylinderL2) :
    finiteFourierProjection s F = ∑ n ∈ s, modeEmbedding n (cylinderCoefficient n F) := by
  simp only [finiteFourierProjection, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]

theorem finiteFourierProjection_coefficient (s : Finset NonzeroMode)
    (F : CylinderL2) (n : NonzeroMode) :
    cylinderCoefficient n (finiteFourierProjection s F) =
      if n ∈ s then cylinderCoefficient n F else 0 := by
  classical
  rw [finiteFourierProjection_apply, map_sum]
  simp only [cylinderCoefficient_mode, Subtype.val_injective.eq_iff]
  simp [Finset.sum_ite_eq', eq_comm]

theorem finiteFourierProjection_zero_mean (s : Finset NonzeroMode) (F : CylinderL2) :
    finiteFourierProjection s F ∈ zeroMeanCylinder := by
  change cylinderCoefficient 0 (finiteFourierProjection s F) = 0
  rw [finiteFourierProjection_apply, map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [cylinderCoefficient_mode]
  simp [Ne.symm n.property]

theorem finiteFourierProjection_idempotent (s : Finset NonzeroMode) (F : CylinderL2) :
    finiteFourierProjection s (finiteFourierProjection s F) = finiteFourierProjection s F := by
  classical
  simp only [finiteFourierProjection_apply]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← finiteFourierProjection_apply, finiteFourierProjection_coefficient, if_pos hn]

theorem finiteFourierProjection_eq_inverse (s : Finset NonzeroMode)
    (F : zeroMeanCylinder) :
    finiteFourierProjection s (F : CylinderL2) =
      (actualCylinderFourier.symm
        (∑ n ∈ s, lp.single 2 n (actualCylinderFourier F n)) : CylinderL2) := by
  rw [map_sum]
  simp only [actualCylinderFourier_inverse_single, Submodule.coe_sum,
    nonzeroCylinderMode_coe, actualCylinderFourier_apply, finiteFourierProjection_apply]

/-- Exact finite-projection norm, derived from the existing native lp model. -/
theorem finiteFourierProjection_norm_sq (s : Finset NonzeroMode) (F : zeroMeanCylinder) :
    ‖finiteFourierProjection s (F : CylinderL2)‖ ^ 2 =
      ∑ n ∈ s, ‖cylinderCoefficient n (F : CylinderL2)‖ ^ 2 := by
  rw [finiteFourierProjection_eq_inverse]
  change ‖actualCylinderFourier.symm
    (∑ n ∈ s, lp.single 2 n (actualCylinderFourier F n))‖ ^ 2 = _
  rw [actualCylinderFourier.symm.norm_map]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, actualCylinderFourier_apply] using
    (lp.norm_sum_single (p := (2 : ℝ≥0∞)) (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (actualCylinderFourier F) s)

theorem finiteFourierProjection_norm_le (s : Finset NonzeroMode) (F : zeroMeanCylinder) :
    ‖finiteFourierProjection s (F : CylinderL2)‖ ≤ ‖(F : CylinderL2)‖ := by
  have he := actualCylinderFourier_hasSum_energy F
  have hb := he.summable.sum_le_tsum s (fun n hn => sq_nonneg
    (‖cylinderCoefficient n (F : CylinderL2)‖))
  rw [he.tsum_eq, ← finiteFourierProjection_norm_sq] at hb
  nlinarith [norm_nonneg (finiteFourierProjection s (F : CylinderL2)),
    norm_nonneg (F : CylinderL2)]

/-- Native convergence of the ACTUAL bounded projections, as a finite-set
net. This is directly the already proved Fourier reconstruction theorem. -/
theorem finiteFourierProjection_tendsto (F : zeroMeanCylinder) :
    Tendsto (fun s : Finset NonzeroMode => finiteFourierProjection s (F : CylinderL2))
      atTop (𝓝 (F : CylinderL2)) := by
  simpa only [finiteFourierProjection_apply] using actualCylinderFourier_hasSum_reconstruction F

private theorem sum_mode_ae (s : Finset NonzeroMode) (F : CylinderL2) :
    ((∑ n ∈ s, modeEmbedding n (cylinderCoefficient n F) : CylinderL2) : CuspCylinder → ℂ)
      =ᵐ[cylinderMeasure]
        (fun z => ∑ n ∈ s, AddCircle.fourier (n : ℤ) z.1 *
          (cylinderCoefficient n F) z.2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℂ 2 cylinderMeasure
  | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      filter_upwards [Lp.coeFn_add (modeEmbedding n (cylinderCoefficient n F))
        (∑ m ∈ s, modeEmbedding m (cylinderCoefficient m F)),
        modeEmbedding_ae n (cylinderCoefficient n F), ih] with z hz hn hs
      simpa only [Pi.add_apply, hn, hs, modeFunction] using hz

/-- Literal slice-integral formula, including the required common AE joins. -/
theorem finiteFourierProjection_ae (s : Finset NonzeroMode) (F : CylinderL2) :
    (finiteFourierProjection s F : CuspCylinder → ℂ) =ᵐ[cylinderMeasure]
      (fun z => ∑ n ∈ s, AddCircle.fourier (n : ℤ) z.1 * sliceCoefficient n F z.2) := by
  classical
  have hc : ∀ᵐ y ∂heightMeasure, ∀ n : NonzeroMode,
      cylinderCoefficient n F y = sliceCoefficient n F y :=
    ae_all_iff.mpr (fun n => cylinderCoefficient_ae n F)
  have hz := (quasiMeasurePreserving_snd (μ := AddCircle.haarAddCircle)
    (ν := heightMeasure)).ae hc
  rw [finiteFourierProjection_apply]
  filter_upwards [sum_mode_ae s F, hz] with z hp hc
  rw [hp]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hc n]

end
end ImbalancedChen.Part3.ActualCylinderFiniteFourierProjection20261026b
