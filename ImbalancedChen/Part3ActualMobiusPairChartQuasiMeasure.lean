import ImbalancedChen.Part3ActualMobiusPairChartL2Transport
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Actual restricted planar measure domination for the real rational Mobius
chart. The native complex Jacobian supplier yields a bound for arbitrary
nonnegative measurable mass, hence quasi-measure-preservation and transport
of almost-everywhere identities of raw values and first jets. These are
geometric statements; no weak chain rule or transported PDE is assumed.
-/

namespace ImbalancedChen.Part3.ActualMobiusPairChartQuasiMeasure20261026b
noncomputable section
open Set Filter MeasureTheory
open scoped MatrixGroups UpperHalfPlane
open Gamma0CompactTensorPoincareC2Core20261025a ActualMobiusMaassEquivariance20261025a
open ActualMobiusCompactLpTransport20261026b ActualMobiusPairChartL2Transport20261026b

theorem mobiusChart_measurable (g : SL(2, ℤ)) : Measurable (mobiusChart g) := by
  unfold mobiusChart mobiusComplex UpperHalfPlane.num UpperHalfPlane.denom complexOfPair
  fun_prop

/-- Domination applies to every nonnegative integrand, including indicators
of null sets; it is stronger than the special squared-L2 error bound. -/
theorem pairchart_compact_lintegral_le (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in K, f (mobiusChart g p)) ≤
      ENNReal.ofReal (compactCompositionConstant g (complexSet K) (complexSet_isCompact hK)) *
        ∫⁻ q in mobiusChart g '' K, f q := by
  have h := compact_composition_lintegral_le g (complexSet_isCompact hK)
    (complexSet_positive hKp) (fun z => f (pairOfComplex z))
  rw [complexSet_mobius_image g hKp,complexSet_lintegral,complexSet_lintegral] at h
  simp only [pair_complexOfPair] at h
  apply le_trans (le_of_eq ?_) h
  apply setLIntegral_congr_fun hK.measurableSet
  intro p hp
  rw [pair_actualMobius g (complexSet_positive hKp (complexOfPair p) ⟨p,hp,rfl⟩),
    pair_complexOfPair]

/-- The literal real chart pushforward is bounded by an explicitly produced
finite multiple of volume on its image. -/
theorem pairchart_compact_map_le (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) :
    (((volume : Measure (ℝ × ℝ)).restrict K).map (mobiusChart g)) ≤
      ENNReal.ofReal (compactCompositionConstant g (complexSet K) (complexSet_isCompact hK)) •
        ((volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K)) := by
  apply Measure.le_iff.mpr
  intro A hA
  have h := pairchart_compact_lintegral_le g hK hKp
    (A.indicator (fun _ => (1 : ℝ≥0∞)))
  have hm := lintegral_map (μ := (volume : Measure (ℝ × ℝ)).restrict K)
    (measurable_const.indicator hA) (mobiusChart_measurable g)
  rw [← hm] at h
  simpa only [lintegral_indicator_one hA,Measure.smul_apply,smul_eq_mul] using h

/-- Native quasi-measure-preservation, derived from the actual local
Jacobian bound rather than supplied by a weak-gradient transport record. -/
theorem pairchart_compact_quasiMeasurePreserving (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) :
    Measure.QuasiMeasurePreserving (mobiusChart g)
      ((volume : Measure (ℝ × ℝ)).restrict K)
      ((volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K)) :=
  ⟨mobiusChart_measurable g,
    Measure.absolutelyContinuous_of_le_smul (pairchart_compact_map_le g hK hKp)⟩

/-- Both raw transformed jets are independent of the representatives of
the target L2 classes. This uses actual geometric null-set transport. -/
theorem pairchart_rawJet_ae_congr (g : SL(2, ℤ)) {K : Set (ℝ × ℝ)}
    (hK : IsCompact K) (hKp : ∀ p ∈ K, 0 < p.2) {U V P Q : ℝ × ℝ → ℂ}
    (hU : U =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K)] P)
    (hV : V =ᵐ[(volume : Measure (ℝ × ℝ)).restrict (mobiusChart g '' K)] Q) :
    (pairRawJetX g U V =ᵐ[(volume : Measure (ℝ × ℝ)).restrict K] pairRawJetX g P Q) ∧
    (pairRawJetY g U V =ᵐ[(volume : Measure (ℝ × ℝ)).restrict K] pairRawJetY g P Q) := by
  have hmap := pairchart_compact_quasiMeasurePreserving g hK hKp
  have hUc := hmap.ae hU
  have hVc := hmap.ae hV
  constructor
  · filter_upwards [hUc,hVc] with p hp hq
    simp only [pairRawJetX,hp,hq]
  · filter_upwards [hUc,hVc] with p hp hq
    simp only [pairRawJetY,hp,hq]

end
end ImbalancedChen.Part3.ActualMobiusPairChartQuasiMeasure20261026b
