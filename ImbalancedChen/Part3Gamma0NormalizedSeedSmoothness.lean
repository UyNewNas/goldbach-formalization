import ImbalancedChen.Part3Gamma0NormalizedCompactSeed
import ImbalancedChen.Part3ActualModularSmoothCuspCutoff

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

True C-infinity regularity of the actual compact normalized Poincare seed.
The compact real bump's actual effective-group trace is locally a finite
sum by proper-action compact hits; the actual Mobius chart is smooth.
Thus the real denominator is smooth without a trace-regularity premise.

At points in tsupport(F), positivity of the trace licenses smooth division.
Outside tsupport(F), F vanishes on a neighborhood, so the normalized seed
is identically zero there EVEN WHEN its denominator vanishes. The final
caller produces trace positivity from a true orbit cover of tsupport(F),
not merely support(F). No finite-tensor-span or operator-domain membership
is asserted or assumed.
-/

namespace ImbalancedChen.Part3.Gamma0NormalizedSeedSmoothness20261025a

noncomputable section
open Set Filter Topology
open scoped UpperHalfPlane
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactGreenProductL120261025a
open Gamma0NormalizedCompactSeed20261025a
open MaassWeakOperatorCore20261024zz
open ActualGamma0MaassDescent20261025a ActualModularSmoothCuspCutoff20261025a

/-- A compact REAL seed has an actual neighborhood-finite effective
trace; the complex compact-hit supplier is used through an exact cast. -/
theorem bumpTrace_locally_eq_finsetSum (N : ℕ) (b : UpperHalfPlane → ℝ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hbK : Function.support b ⊆ K)
    (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (effectiveGamma0 N), ∀ w ∈ U,
      bumpTrace N b w = ∑ q ∈ S, b (effectiveMatrixAction N q w) := by
  have hcast : Function.support (fun w => (b w : ℂ)) ⊆ K := by
    intro w hw
    apply hbK
    intro hz
    exact hw (by simp [hz])
  obtain ⟨U, hU, S, hS⟩ := compact_seed_locally_finite N (fun w => (b w : ℂ)) hK hcast z
  refine ⟨U, hU, S, ?_⟩
  intro w hw
  apply tsum_eq_sum
  intro q hq
  exact Complex.ofReal_eq_zero.mp (hS w hw q hq)

/-- Composition of the actual positive chart with an actual effective
matrix is exactly the native Mobius chart, to every order. -/
theorem effective_chartLift_mobius (N : ℕ) (q : effectiveGamma0 N)
    {p : ℝ × ℝ} (hp : 0 < p.2) :
    chartLift (mobiusChart (effectiveRepresentative N q : SL(2, ℤ)) p) =
      effectiveMatrixAction N q (chartLift p) := by
  change chartLift (mobiusChart (effectiveRepresentative N q : SL(2, ℤ)) p) =
    (effectiveRepresentative N q : SL(2, ℤ)) • chartLift p
  rw [mobiusChart_eq_actual _ hp, chartLift_pair]

/-- Genuine real trace regularity from the compact bump's own chart
smoothness and the derived finite formula; no hTraceSmooth premise. -/
theorem bumpTrace_chart_cinfty (N : ℕ) (b : UpperHalfPlane → ℝ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hbK : Function.support b ⊆ K)
    (hb : ContDiffOn ℝ ∞ (fun p => b (chartLift p)) positiveChart) :
    ContDiffOn ℝ ∞ (fun p => bumpTrace N b (chartLift p)) positiveChart := by
  intro p hp
  obtain ⟨U, hU, S, hS⟩ := bumpTrace_locally_eq_finsetSum N b hK hbK (chartLift p)
  have heq : (fun r => bumpTrace N b (chartLift r)) =ᶠ[𝓝 p]
      (fun r => ∑ q ∈ S,
        b (chartLift (mobiusChart (effectiveRepresentative N q : SL(2, ℤ)) r))) := by
    filter_upwards [(chartLift_continuousAt_positive hp).eventually hU,
      positiveChart_isOpen.mem_nhds hp] with r hr hrpos
    rw [hS (chartLift r) hr]
    apply Finset.sum_congr rfl
    intro q _
    rw [effective_chartLift_mobius N q hrpos]
  have hsum : ContDiffAt ℝ ∞ (fun r => ∑ q ∈ S,
      b (chartLift (mobiusChart (effectiveRepresentative N q : SL(2, ℤ)) r))) p := by
    apply ContDiffAt.sum
    intro q _
    let g : SL(2, ℤ) := effectiveRepresentative N q
    have him : 0 < (mobiusChart g p).2 := by
      rw [mobiusChart_eq_actual g hp]
      exact (g • chartLift p).im_pos
    have hbAt : ContDiffAt ℝ ∞ (fun r => b (chartLift r)) (mobiusChart g p) :=
      (hb _ him).contDiffAt (positiveChart_isOpen.mem_nhds him)
    exact hbAt.comp p (mobiusChart_cinftyAt g hp)
  exact (hsum.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Actual local gluing across zero denominators. Positivity is needed
on the CLOSED support of F; its open complement gives a zero germ. -/
theorem normalizedSeed_chart_cinfty_of_trace_positive
    (N : ℕ) (b : UpperHalfPlane → ℝ) (F : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hbK : Function.support b ⊆ K)
    (hb : ContDiffOn ℝ ∞ (fun p => b (chartLift p)) positiveChart)
    (hF : ContDiffOn ℝ ∞ (fun p => F (chartLift p)) positiveChart)
    (hpos : ∀ z ∈ tsupport F, 0 < bumpTrace N b z) :
    ContDiffOn ℝ ∞ (fun p => normalizedSeed N b F (chartLift p)) positiveChart := by
  have htrace := bumpTrace_chart_cinfty N b hK hbK hb
  intro p hp
  by_cases hz : chartLift p ∈ tsupport F
  · have hbAt : ContDiffAt ℝ ∞ (fun r => (b (chartLift r) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((hb p hp).contDiffAt (positiveChart_isOpen.mem_nhds hp))
    have hFAt : ContDiffAt ℝ ∞ (fun r => F (chartLift r)) p :=
      (hF p hp).contDiffAt (positiveChart_isOpen.mem_nhds hp)
    have hdAt : ContDiffAt ℝ ∞ (fun r => (bumpTrace N b (chartLift r) : ℂ)) p :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp p
        ((htrace p hp).contDiffAt (positiveChart_isOpen.mem_nhds hp))
    have hd : (bumpTrace N b (chartLift p) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (hpos _ hz))
    exact ((hbAt.mul hFAt).div hdAt hd).contDiffWithinAt
  · have hopen : (tsupport F)ᶜ ∈ 𝓝 (chartLift p) :=
      isClosed_tsupport.isOpen_compl.mem_nhds hz
    have heq : (fun r => normalizedSeed N b F (chartLift r)) =ᶠ[𝓝 p]
        (fun _ => (0 : ℂ)) := by
      filter_upwards [(chartLift_continuousAt_positive hp).eventually hopen] with r hr
      have hzero : F (chartLift r) = 0 := image_eq_zero_of_notMem_tsupport hr
      simp only [normalizedSeed, hzero, mul_zero, zero_div]
    have hc : ContDiffAt ℝ ∞ (fun _ : ℝ × ℝ => (0 : ℂ)) p := contDiffAt_const
    exact (hc.congr_of_eventuallyEq heq).contDiffWithinAt

/-- End-to-end smooth normalization from a TRUE orbit cover of tsupport.
The trace positivity is now produced, not supplied as a nonzero divisor.
Neither smoothness of the normalized seed nor core membership is input. -/
theorem normalizedSeed_chart_cinfty_of_orbit_cover
    (N : ℕ) (b : UpperHalfPlane → ℝ) (F : UpperHalfPlane → ℂ)
    {K C : Set UpperHalfPlane} (hK : IsCompact K)
    (hbK : Function.support b ⊆ K) (hbnonneg : ∀ z, 0 ≤ b z)
    (hbC : ∀ z ∈ C, 0 < b z)
    (hb : ContDiffOn ℝ ∞ (fun p => b (chartLift p)) positiveChart)
    (hF : ContDiffOn ℝ ∞ (fun p => F (chartLift p)) positiveChart)
    (hcover : ∀ z ∈ tsupport F,
      ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ C) :
    ContDiffOn ℝ ∞ (fun p => normalizedSeed N b F (chartLift p)) positiveChart := by
  apply normalizedSeed_chart_cinfty_of_trace_positive N b F hK hbK hb hF
  intro z hz
  exact bumpTrace_pos_of_orbit_meets N b hK hbK hbnonneg hbC z (hcover z hz)

/-- The same TRUE construction supplies the exact C2 regularity needed
by finite-jet approximation, with compact support supplied independently
by the existing exact normalized-seed module. -/
theorem normalizedSeed_compact_C2_of_orbit_cover
    (N : ℕ) (b : UpperHalfPlane → ℝ) (F : UpperHalfPlane → ℂ)
    {K C : Set UpperHalfPlane} (hK : IsCompact K)
    (hbK : Function.support b ⊆ K) (hbnonneg : ∀ z, 0 ≤ b z)
    (hbC : ∀ z ∈ C, 0 < b z)
    (hb : ContDiffOn ℝ ∞ (fun p => b (chartLift p)) positiveChart)
    (hF : ContDiffOn ℝ ∞ (fun p => F (chartLift p)) positiveChart)
    (hcover : ∀ z ∈ tsupport F,
      ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ C) :
    HasCompactSupport (normalizedSeed N b F) ∧
      ContDiffOn ℝ 2 (fun p => normalizedSeed N b F (chartLift p)) positiveChart := by
  exact ⟨normalizedSeed_hasCompactSupport N b F hK hbK,
    (normalizedSeed_chart_cinfty_of_orbit_cover N b F hK hbK hbnonneg hbC hb hF hcover).of_le
      (by simp)⟩

/-- The SAME smoothness statement for the existing native zero extension
used by the actual upperMaass and finite-jet APIs. Only positive chart
points are in the conclusion, so no boundary smoothness is asserted. -/
theorem normalizedSeed_extendUpper_cinfty_of_orbit_cover
    (N : ℕ) (b : UpperHalfPlane → ℝ) (F : UpperHalfPlane → ℂ)
    {K C : Set UpperHalfPlane} (hK : IsCompact K)
    (hbK : Function.support b ⊆ K) (hbnonneg : ∀ z, 0 ≤ b z)
    (hbC : ∀ z ∈ C, 0 < b z)
    (hb : ContDiffOn ℝ ∞ (fun p => b (chartLift p)) positiveChart)
    (hF : ContDiffOn ℝ ∞ (fun p => F (chartLift p)) positiveChart)
    (hcover : ∀ z ∈ tsupport F,
      ∃ q : effectiveGamma0 N, effectiveMatrixAction N q z ∈ C) :
    ContDiffOn ℝ ∞ (extendUpper (normalizedSeed N b F)) positiveChart := by
  have hs := normalizedSeed_chart_cinfty_of_orbit_cover N b F hK hbK hbnonneg hbC hb hF hcover
  apply hs.congr
  intro p hp
  exact (extendUpper_chartLift (normalizedSeed N b F) p hp).symm

end
end ImbalancedChen.Part3.Gamma0NormalizedSeedSmoothness20261025a
