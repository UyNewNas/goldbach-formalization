import ImbalancedChen.Part3OriginalPeterssonHighStrip
import ImbalancedChen.Part3OriginalHighStripPacketBudget
import Batteries.Tactic.OpenPrivate

/-! A moving Petersson strip for the original two observed cusps.  The
pointwise count from the signed packet proof applies to the invariant
Petersson density in every weight; no sum over weights has been taken. -/
noncomputable section
namespace ImbalancedChen.Part3.OriginalRegularPeterssonStrip20261113
open Set MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups UpperHalfPlane ENNReal ModularForm Pointwise
open ActualContinuousPoincarePairing20261110 ActualCuspStripCutoff20261025a
open OriginalHolomorphicCuspFrames20261110 OriginalHolomorphicPeterssonSpace20261112
open scoped OriginalHolomorphicPeterssonSpace20261112
open OriginalPeterssonHighStrip20261112 OriginalCuspHitPacking20261112
open Gamma0GeneralCuspUnitPeriod20261025a Gamma0GeneralCuspWidth20261025a
open Gamma0EffectiveFiniteUnfolding20261025a Gamma0EffectiveActionKernel20261024z
open Gamma0CarrierAESection20261025a Gamma0NonnegativePoincareUnfolding20261025a
open private energy_invariant from ImbalancedChen.Part3OriginalPeterssonHighStrip

/-- Petersson mass above Y in the normalized frame is at most
(2+4/(NY)) times the actual Petersson norm squared.  This is especially
useful at Y comparable to 1/L, below the standard height-one cell. -/
theorem moving_strip (N r : ℕ) [NeZero N] (one : Bool) {Y : ℝ} (hY : 0<Y)
    (f : Forms N r) :
    (∫⁻ w in highWidthStrip 1 Y,frameEnergy f (originalFrame one) w) ≤
      ENNReal.ofReal (2+4/((N:ℝ)*Y))*ENNReal.ofReal (‖f‖^2) := by
  classical
  let g := originalFrame one
  let σ := normalizedScaling N (NeZero.pos N) g
  let S := highWidthStrip 1 Y
  let U := (fun w : ℍ => σ⁻¹ • w) ⁻¹' S
  let F := U.indicator (energy f)
  let c := ENNReal.ofReal (2+4/((N:ℝ)*Y))
  have Sm : MeasurableSet S := highWidthStrip_measurable 1 Y
  have Um : MeasurableSet U :=
    (show Continuous (fun w : ℍ => σ⁻¹ • w) from continuous_const_smul _).measurable Sm
  have em : Measurable (energy f) :=
    ENNReal.measurable_ofReal.comp (((section_continuous f).norm.pow 2).measurable)
  have fm : Measurable F := em.indicator Um
  have image : (fun w : ℍ => σ • w) '' S=U := by
    ext w
    constructor
    · rintro ⟨u,hu,rfl⟩
      simpa [U] using hu
    · intro h
      exact ⟨σ⁻¹ • w,h,smul_inv_smul σ w⟩
  have reindex : (∫⁻ w in S,frameEnergy f g w)=∫⁻ w : ℍ,F w := by
    simp_rw [frame_energy_eq]
    change (∫⁻ w in S,energy f (σ • w))=_
    calc
      _ = ∫⁻ w in (fun u : ℍ => σ • u) '' S,energy f w :=
        (measurePreserving_smul (mapGL ℝ σ) (volume : Measure ℍ)).setLIntegral_comp_emb
          (measurableEmbedding_const_smul _) _ S
      _ = _ := by rw [image,←lintegral_indicator Um]
  have bd (w : ℍ) : fullSeedTrace N F w≤c*energy f w := by
    let P := hits_finite N (NeZero.pos N) one hY w
    let T := P.toFinset
    have equiv (i : effectiveGamma0 N) :
        effectiveMatrixAction N i w∈U ↔ i∈T := P.mem_toFinset.symm
    have tr : fullSeedTrace N F w=∑ i∈T,F (effectiveMatrixAction N i w) :=
      tsum_eq_sum (fun i hi => indicator_of_notMem (fun h => hi ((equiv i).mp h)) _)
    have card := count_hits N (NeZero.pos N) one hY w T (fun _ h => P.mem_toFinset.mp h)
    have ec : (T.card:ℝ≥0∞)≤c := by simpa [c] using ENNReal.ofReal_le_ofReal card
    rw [tr]
    calc
      _ = ∑ _i∈T,energy f w := Finset.sum_congr rfl (fun i hi =>
        (indicator_of_mem ((equiv i).mpr hi) _).trans (energy_invariant f (effectiveRepresentative N i) w))
      _ = (T.card:ℝ≥0∞)*energy f w := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_right' ec _
  calc
    _ = ∫⁻ w : ℍ,F w := reindex
    _ = ∫⁻ w in reducedCarrier N,fullSeedTrace N F w := lintegral_fullSeedTrace N F fm
    _ ≤ ∫⁻ w in reducedCarrier N,c*energy f w := lintegral_mono bd
    _ = c*∫⁻ w in reducedCarrier N,energy f w := lintegral_const_mul c em
    _ = _ := by rw [Measure.restrict_congr_set (reducedCarrier_ae_eq_carrier N),energy_carrier]

end ImbalancedChen.Part3.OriginalRegularPeterssonStrip20261113
end
