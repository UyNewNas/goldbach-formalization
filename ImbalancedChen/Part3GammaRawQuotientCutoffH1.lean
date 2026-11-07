import ImbalancedChen.Part3UpperChartLocalSmoothMultiplierH1
import ImbalancedChen.Part3GammaActualQuotientCutoffMultiplier
import ImbalancedChen.Part3Gamma0QuotientCoreRepresentativeFaithfulness
import ImbalancedChen.Part3CanonicalPlanarL2Unitary

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Literal actual quotient cutoff multiplication preserves raw whole-chart
H1_loc for arbitrary physical quotient L2 inputs, without form membership.
The quotient Lp representative identity is transported through the true
canonical quotient/upper-plane/chart AE maps. The noncompact modular
cutoff uses the proved LOCAL smooth multiplier test rule; no global
compact-support or desired product-weak-gradient premise is introduced.
-/

namespace ImbalancedChen.Part3.GammaRawQuotientCutoffH120261026b
noncomputable section
open Set Filter MeasureTheory
open scoped UpperHalfPlane
open Gamma0QuotientCellPushforward20261025a Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCoreRepresentativeFaithfulness20261025a
open CanonicalTensorHyperbolicLaplacianForm20261024z MaassWeakOperatorCore20261024zz
open MaassWeightedCoordinateL220261024zz CanonicalPlanarL2UnitarySourceOnly
open CompactC2ProductMollifier20261026a LocalWeakH1CutoffProduct20261026b
open ActualPullbackLocalH1Transfer20261026b WholeUpperChartWeakH1Patching20261026b
open ActualModularCutoffMaassBudget20261025a GammaSmoothMultiplierLegalTests20261026a
open GammaSmoothMultiplierPeriodization20261026a GammaActualQuotientCutoffMultiplier20261026b
open UpperChartLocalSmoothMultiplierH120261026b

def rawCutoffPlane (Y : ℝ) : Plane → ℂ := extendUpper (complexGlobalH Y)

def rawCutoffDx (Y : ℝ) (F Gx : Plane → ℂ) : Plane → ℂ :=
  productDerivative (rawCutoffPlane Y) F Gx ex

def rawCutoffDy (Y : ℝ) (F Gy : Plane → ℂ) : Plane → ℂ :=
  productDerivative (rawCutoffPlane Y) F Gy ey

/-- Canonical AE transport removes the y^-1 unitary factor using strict
positive height; it does not assume a converse chart QMP theorem. -/
theorem upper_ae_to_chart_raw_ae {F G : UpperHalfPlane → ℂ}
    (h : F =ᵐ[(volume : Measure UpperHalfPlane)] G) :
    chartPullback F =ᵐ[(volume : Measure Plane)] chartPullback G := by
  have hu := forwardFunction_congr_ae h
  filter_upwards [hu] with p hp
  by_cases hpos : p ∈ upperChart
  · simp only [forwardFunction,unweightChart,dif_pos hpos] at hp
    have hm := congrArg (fun w : ℂ => p.2 • w) hp
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hpos),one_smul] using hm
  · simp only [chartPullback,dif_neg hpos]

theorem actual_quotient_cutoff_raw_pullback_ae (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1 < Y) (f : QuotientL2 N) :
    actualPlanePullback N (actualQuotientCutoffMultiplier N Y hY f) =ᵐ[(volume : Measure Plane)]
      (fun p => rawCutoffPlane Y p*actualPlanePullback N f p) := by
  have hQ := actualQuotientCutoffMultiplier_coe_ae N Y hY f
  have hH0 := quotient_ae_pullback_full N hQ
  have hH : (fun z : UpperHalfPlane =>
      (actualQuotientCutoffMultiplier N Y hY f) (orbitProjection N z)) =ᵐ[volume]
      (fun z => complexGlobalH Y z*f (orbitProjection N z)) := by
    filter_upwards [hH0] with z hz
    simpa only [Function.comp_def,Pi.mul_apply,quotientMultiplier_projection] using hz
  have hP := upper_ae_to_chart_raw_ae hH
  filter_upwards [hP] with p hp
  by_cases hpos : 0 < p.2
  · simpa only [actualPlanePullback,chartPullback,rawCutoffPlane,extendUpper,
      dif_pos hpos] using hp
  · simp only [actualPlanePullback,rawCutoffPlane,extendUpper,dif_neg hpos,mul_zero]

/-- The named raw product derivatives form a genuine whole-upper-chart
weak-gradient packet of the native actual quotient cutoff product. -/
theorem actual_quotient_cutoff_raw_H1_packet (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (Gx Gy : Plane → ℂ)
    (hb : ∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp (actualPlanePullback N f) 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gx 2 ((volume : Measure Plane).restrict K) ∧
      MemLp Gy 2 ((volume : Measure Plane).restrict K))
    (hw : ∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p)*Gx p) = -(∫ p, star (directional ex ψ p)*actualPlanePullback N f p)) ∧
      ((∫ p, star (ψ p)*Gy p) = -(∫ p, star (directional ey ψ p)*actualPlanePullback N f p)))
    (Y : ℝ) (hY : 1 < Y) :
    (∀ K : Set Plane, IsCompact K → K ⊆ upperChart →
      MemLp (actualPlanePullback N (actualQuotientCutoffMultiplier N Y hY f)) 2
        ((volume : Measure Plane).restrict K) ∧
      MemLp (rawCutoffDx Y (actualPlanePullback N f) Gx) 2 ((volume : Measure Plane).restrict K) ∧
      MemLp (rawCutoffDy Y (actualPlanePullback N f) Gy) 2 ((volume : Measure Plane).restrict K)) ∧
    (∀ ψ : Plane → ℂ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ upperChart →
      ((∫ p, star (ψ p)*rawCutoffDx Y (actualPlanePullback N f) Gx p) =
        -(∫ p, star (directional ex ψ p)*
          actualPlanePullback N (actualQuotientCutoffMultiplier N Y hY f) p)) ∧
      ((∫ p, star (ψ p)*rawCutoffDy Y (actualPlanePullback N f) Gy p) =
        -(∫ p, star (directional ey ψ p)*
          actualPlanePullback N (actualQuotientCutoffMultiplier N Y hY f) p))) := by
  obtain ⟨hlocal,hweak⟩ := upperChart_H1_local_smooth_multiplier (actualPlanePullback N f)
    Gx Gy (rawCutoffPlane Y) hb hw (actualCutoff_cinfty Y (lt_trans (by norm_num) hY))
  have hae := actual_quotient_cutoff_raw_pullback_ae N Y hY f
  constructor
  · intro K hK hs
    obtain ⟨hF,hX,hGy⟩ := hlocal K hK hs
    exact ⟨hF.ae_eq (ae_restrict_of_ae hae.symm),hX,hGy⟩
  · intro ψ hψ hc hs
    have hm (v : Plane) : (∫ p, star (directional v ψ p)*
        (rawCutoffPlane Y p*actualPlanePullback N f p)) =
        ∫ p, star (directional v ψ p)*actualPlanePullback N (actualQuotientCutoffMultiplier N Y hY f) p := by
      apply integral_congr_ae
      filter_upwards [hae] with p hp
      rw [hp]
    obtain ⟨hx,hy⟩ := hweak ψ hψ hc hs
    exact ⟨by simpa only [hm ex] using hx,by simpa only [hm ey] using hy⟩

theorem actual_quotient_cutoff_preserves_upperChart_H1 (N : ℕ) [NeZero N]
    (f : QuotientL2 N) (hf : HasUpperChartWeakH1 (actualPlanePullback N f))
    (Y : ℝ) (hY : 1 < Y) :
    HasUpperChartWeakH1 (actualPlanePullback N (actualQuotientCutoffMultiplier N Y hY f)) := by
  obtain ⟨Gx,Gy,hb,hw⟩ := hf
  obtain ⟨hbY,hwY⟩ := actual_quotient_cutoff_raw_H1_packet N f Gx Gy hb hw Y hY
  exact ⟨rawCutoffDx Y (actualPlanePullback N f) Gx,
    rawCutoffDy Y (actualPlanePullback N f) Gy,hbY,hwY⟩

end
end ImbalancedChen.Part3.GammaRawQuotientCutoffH120261026b
