import ImbalancedChen.Part3GammaRawCutoffLeibnizFiber

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
True STRONG convergence of raw cutoff Leibniz fibres in the original
native carrier L2. Both squared errors are literal weighted integrals:
(1-chi)^2 norm(W)^2 and cutoffEnergyH norm(f pullback)^2. The proved raw
carrier dominated-convergence suppliers kill them without scalar descent
of W, form membership, a desired gradient-limit or weak compactness.
-/

namespace ImbalancedChen.Part3.GammaRawLeibnizCarrierConvergence20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped Topology UpperHalfPlane
open Gamma0ActualSmoothQuotientCore20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CompactCoreGradient20261025a Gamma0CarrierGradientHilbertMap20261026b
open GammaRawWeightedFiberL220261026b GammaRawCutoffLeibnizFiber20261026b
open GammaRawCarrierWeightedCutoffLimits20261026b Gamma0WeightedCutoffDefectLimit20261026a
open ActualModularCutoffMaassBudget20261025a ActualModularCutoffGradient20261025a

theorem cutoffMainFiber_difference_norm_sq (Y : ℝ) (W : UpperHalfPlane → GradientFiber)
    (z : UpperHalfPlane) :
    ‖cutoffMainFiber Y W z-W z‖^2=(1-ActualModularSmoothCuspCutoff20261025a.globalCutoff Y z)^2*‖W z‖^2 := by
  have he : cutoffMainFiber Y W z-W z=
      (((ActualModularSmoothCuspCutoff20261025a.globalCutoff Y z-1 : ℝ) : ℂ)) • W z := by
    simp only [cutoffMainFiber,complexGlobalH,Complex.ofReal_sub,Complex.ofReal_one,sub_smul,one_smul]
  rw [he,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  ring

theorem cutoffMainFiberL2_sub_norm_sq (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1<Y)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) :
    ‖cutoffMainFiberL2 N Y hY hW-hW.toLp W‖^2=
      ∫ z,(1-ActualModularSmoothCuspCutoff20261025a.globalCutoff Y z)^2*‖W z‖^2 ∂carrierVolume N := by
  rw [carrierGradientL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (cutoffMainFiberL2 N Y hY hW) (hW.toLp W),
    (cutoffMainFiber_memLp N Y hY hW).coeFn_toLp,hW.coeFn_toLp] with z hz hm hw
  rw [hz,hm,hw,cutoffMainFiber_difference_norm_sq]

theorem cutoffErrorFiberL2_norm_sq (N : ℕ) [NeZero N] (f : QuotientL2 N) (Y : ℝ) (hY : 1<Y) :
    ‖cutoffErrorFiberL2 N f Y hY‖^2=
      ∫ z,cutoffEnergyH Y z*‖f (orbitProjection N z)‖^2 ∂carrierVolume N := by
  rw [carrierGradientL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [(cutoffErrorFiber_memLp N f Y hY).coeFn_toLp] with z hz
  rw [hz,cutoffErrorFiber_norm_sq]

private theorem tendsto_zero_of_norm_sq_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    (u : ℕ → E) (hu : Tendsto (fun n => ‖u n‖^2) atTop (𝓝 (0 : ℝ))) :
    Tendsto u atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hu
  simpa only [Real.sqrt_zero,Real.sqrt_sq (norm_nonneg _)] using hs

theorem cutoffMainFiberL2_strong (N : ℕ) [NeZero N]
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) :
    Tendsto (fun n => cutoffMainFiberL2 N (cutoffHeight n) (cutoffHeight_gt_one n) hW)
      atTop (𝓝 (hW.toLp W)) := by
  have hs : Tendsto (fun n =>
      ‖cutoffMainFiberL2 N (cutoffHeight n) (cutoffHeight_gt_one n) hW-hW.toLp W‖^2)
      atTop (𝓝 (0 : ℝ)) := by
    simp_rw [cutoffMainFiberL2_sub_norm_sq]
    exact raw_weighted_cutoff_defect_tendsto (carrierVolume N) (fun z => ‖W z‖^2)
      (hW.integrable_norm_pow (by decide : (2 : ℕ)≠0))
      (Eventually.of_forall fun z => sq_nonneg _)
  have hz := tendsto_zero_of_norm_sq_tendsto_zero _ hs
  simpa only [sub_add_cancel,zero_add] using hz.add
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => hW.toLp W) atTop (𝓝 (hW.toLp W)))

theorem cutoffErrorFiberL2_strong_zero (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    Tendsto (fun n => cutoffErrorFiberL2 N f (cutoffHeight n) (cutoffHeight_gt_one n)) atTop (𝓝 0) := by
  apply tendsto_zero_of_norm_sq_tendsto_zero
  simp_rw [cutoffErrorFiberL2_norm_sq]
  exact raw_weighted_cutoff_gradient_error_tendsto (carrierVolume N)
    (fun z => ‖f (orbitProjection N z)‖^2)
    ((actualCarrierPullback_memLp N f).integrable_norm_pow (by decide : (2 : ℕ)≠0))
    (Eventually.of_forall fun z => sq_nonneg _)

/-- No form, invariance of the coordinate fields, or claimed gradient
convergence premise occurs: the convergence is proved in CarrierGradientL2. -/
theorem rawLeibnizFiberL2_strong (N : ℕ) [NeZero N] (f : QuotientL2 N)
    {W : UpperHalfPlane → GradientFiber} (hW : MemLp W 2 (carrierVolume N)) :
    Tendsto (rawLeibnizFiberL2 N f hW) atTop (𝓝 (hW.toLp W)) := by
  change Tendsto (fun n => rawLeibnizFiberL2 N f hW n) atTop (𝓝 (hW.toLp W))
  simp_rw [rawLeibnizFiberL2_eq_add]
  simpa only [add_zero] using (cutoffMainFiberL2_strong N hW).add (cutoffErrorFiberL2_strong_zero N f)

/-- Sobolev-converse supplier with only whole-chart LOCAL L2 and finite
literal carrier energy for the given raw ordinary derivative fields. -/
theorem raw_coordinate_Leibniz_strong (N : ℕ) [NeZero N] (f : QuotientL2 N)
    (Gx Gy : ℝ×ℝ → ℂ) (hx : LocallyL2OnUpperChart Gx) (hy : LocallyL2OnUpperChart Gy)
    (hfinite : (∫⁻ z,ENNReal.ofReal (rawCarrierEnergy Gx Gy z) ∂carrierVolume N)<∞) :
    Tendsto (rawLeibnizFiberL2 N f (rawWeightedFiber_carrier_memLp N Gx Gy hx hy hfinite))
      atTop (𝓝 (rawWeightedFiberL2 N Gx Gy hx hy hfinite)) :=
  rawLeibnizFiberL2_strong N f (rawWeightedFiber_carrier_memLp N Gx Gy hx hy hfinite)

end
end ImbalancedChen.Part3.GammaRawLeibnizCarrierConvergence20261026b
