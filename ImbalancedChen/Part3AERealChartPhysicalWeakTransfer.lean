import ImbalancedChen.Part3ActualQuotientCuspValuePeriodization

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The real-chart weak equation is independent of AE local representative
choices. Actual compact test support and support of its ordinary
horizontal derivative justify every replacement. Compact raw chart L²
regularity supplies local L1; native physical L² representatives may then
be matched to arbitrary coherent raw chart witnesses only AE. The full
physical circle weak equation and graph inclusion follow without assuming
any chart derivative of an Lp representative.
-/
namespace ImbalancedChen.Part3.AERealChartPhysicalWeakTransfer20261026b
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ContDiff
open ProductConvolutionSecondDerivatives20261026a PeriodicCompactChartTests20261026b
open CuspCylinderMeasure20261024z ClosedHorizontalCuspTail20261026a
open RealChartToPhysicalCuspWeak20261026b CuspRawWeakDerivativeBridge20261026b

attribute [local instance] Measure.Subtype.measureSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem locallyIntegrableOn_of_compact_memLp {Ω : Set Plane} (hΩ : IsOpen Ω)
    {H : Plane → ℂ}
    (hH : ∀ K : Set Plane, IsCompact K → K ⊆ Ω → MemLp H 2 ((volume : Measure Plane).restrict K)) :
    LocallyIntegrableOn H Ω volume := by
  rw [locallyIntegrableOn_iff hΩ.isLocallyClosed]
  intro K hKΩ hK
  letI : IsFiniteMeasure ((volume : Measure Plane).restrict K) :=
    ⟨by simpa using hK.measure_lt_top⟩
  exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (hH K hK hKΩ)

/-- Genuine arbitrary-test local weak differentiation transfers under
local AE equality of the value and derivative witnesses. -/
theorem real_chart_weak_congr_ae {Ω : Set Plane} (hΩ : MeasurableSet Ω)
    {F D U V : Plane → ℂ}
    (hF : F =ᵐ[(volume : Measure Plane).restrict Ω] U)
    (hD : D =ᵐ[(volume : Measure Plane).restrict Ω] V)
    (hw : HasRealChartHorizontalWeakDerivative Ω F D) :
    HasRealChartHorizontalWeakDerivative Ω U V := by
  have hf := (ae_restrict_iff' hΩ).mp hF
  have hd := (ae_restrict_iff' hΩ).mp hD
  intro Ψ hΨ hc hs
  have hleft : (∫ p : Plane, star (Ψ p) * V p) = ∫ p : Plane, star (Ψ p) * D p := by
    apply integral_congr_ae
    filter_upwards [hd] with p hp
    by_cases hpin : p ∈ Ω
    · rw [hp hpin]
    · have hn : p ∉ tsupport Ψ := fun h => hpin (hs h)
      simp [image_eq_zero_of_notMem_tsupport hn]
  have hright : (∫ p : Plane, star (directional xDirection Ψ p) * U p) =
      ∫ p : Plane, star (directional xDirection Ψ p) * F p := by
    apply integral_congr_ae
    filter_upwards [hf] with p hp
    by_cases hpin : p ∈ Ω
    · rw [hp hpin]
    · have hn : p ∉ tsupport Ψ := fun h => hpin (hs h)
      have hd0 : directional xDirection Ψ p = 0 := by
        simp only [directional, fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply]
      simp [hd0]
  rw [hleft, hright]
  exact hw Ψ hΨ hc hs

/-- Exact minimal ABI for coherent real-chart derivative witnesses and
native physical mixed-L² classes. Their real lifts need only match AE. -/
theorem ae_real_chart_implies_physical_raw_weak {w a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (F D : Plane → ℂ)
    (hF : LocallyIntegrableOn F {p : Plane | a < p.2} volume)
    (hD : LocallyIntegrableOn D {p : Plane | a < p.2} volume)
    (hchart : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D)
    (hvalue : F =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift u)
    (hderivative : D =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      realCylinderLift (fun z => (w : ℂ) * d z)) :
    HasRawWeakPhysicalTailDerivative w a u d := by
  have hΩ : MeasurableSet {p : Plane | a < p.2} :=
    (isOpen_lt continuous_const continuous_snd).measurableSet
  exact real_chart_implies_physical_raw_weak ha u d
    (hF.congr hvalue) (hD.congr hderivative)
    (real_chart_weak_congr_ae hΩ hvalue hderivative hchart)

/-- Ordinary compact raw H1 regularity is sufficient for the local
integrability ABI; global chart L² is never asserted. -/
theorem compact_L2_chart_implies_physical_raw_weak {w a : ℝ} (ha : 0 < a)
    (u : FunctionL2 a) (d : DerivativeL2 a) (F D : Plane → ℂ)
    (hlocal : ∀ K : Set Plane, IsCompact K → K ⊆ {p : Plane | a < p.2} →
      MemLp F 2 ((volume : Measure Plane).restrict K) ∧
      MemLp D 2 ((volume : Measure Plane).restrict K))
    (hchart : HasRealChartHorizontalWeakDerivative {p : Plane | a < p.2} F D)
    (hvalue : F =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}] realCylinderLift u)
    (hderivative : D =ᵐ[(volume : Measure Plane).restrict {p : Plane | a < p.2}]
      realCylinderLift (fun z => (w : ℂ) * d z)) :
    HasRawWeakPhysicalTailDerivative w a u d := by
  have hΩ : IsOpen {p : Plane | a < p.2} := isOpen_lt continuous_const continuous_snd
  exact ae_real_chart_implies_physical_raw_weak ha u d F D
    (locallyIntegrableOn_of_compact_memLp hΩ (fun K hK hs => (hlocal K hK hs).1))
    (locallyIntegrableOn_of_compact_memLp hΩ (fun K hK hs => (hlocal K hK hs).2))
    hchart hvalue hderivative

end
end ImbalancedChen.Part3.AERealChartPhysicalWeakTransfer20261026b
