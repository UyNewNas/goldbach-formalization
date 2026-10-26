import ImbalancedChen.Part3ActualTensorPoincareMaassJoin
import ImbalancedChen.Part3ActualGamma0MaassDescent
import ImbalancedChen.Part3Gamma0CompactGreenProductL1

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

The actual Maass operator commutes with periodization of ANY compact C2
seed, using the native positive chart. Compact support of the output is
derived from a zero germ, never from vanishing at an isolated point. A
single genuine compact-hit neighborhood makes both series finite. The
only geometric differentiation supplier is the existing actual Mobius
second-chain theorem. No operator-domain or finite-tensor membership is
claimed.
-/

namespace ImbalancedChen.Part3.ActualCompactSeedMaassJoin20261025a

noncomputable section
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane BigOperators
open Gamma0EffectiveActionKernel20261024z Gamma0EffectiveFiniteUnfolding20261025a
open Gamma0CompactTensorPoincareLocalFinite20261025a
open Gamma0CompactTensorPoincareC2Core20261025a
open Gamma0CompactSeedQuotientL2Budget20261025a
open Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0QuotientCellPushforward20261025a Gamma0CarrierAESection20261025a
open Gamma0QuotientConullTransport20261025a
open Gamma0CompactGreenProductL120261025a
open ActualGamma0MaassDescent20261025a ActualPoincareMaassLocalFinite20261025a
open ActualMobiusMaassEquivariance20261025a MaassWeakOperatorCore20261024zz

private theorem chart_open : IsOpen positiveChart :=
  isOpen_lt continuous_const continuous_snd

private theorem chartLift_continuous_positive {p : ℝ × ℝ} (hp : 0 < p.2) :
    ContinuousAt chartLift p := by
  apply (UpperHalfPlane.contMDiffAt_ofComplex (n := 2) hp).continuousAt.comp
  have heq : complexOfPair =
      (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    funext q
    ext <;> simp [complexOfPair]
  rw [heq]
  fun_prop

theorem native_C2_continuous (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) : Continuous f := by
  have hc := hf.continuousOn.comp_continuous
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
    (fun z => z.im_pos)
  simpa only [extendUpper_pair] using hc

theorem native_C2_upperMaass_continuous (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) :
    Continuous (upperMaass f) := by
  exact (chartMaass_continuousOn (extendUpper f) hf).comp_continuous
    (UpperHalfPlane.continuous_re.prodMk UpperHalfPlane.continuous_im)
    (fun z => z.im_pos)

/-- Locality of the TOTAL derivative suffices for support locality; no
regularity at a boundary point of the support is silently assumed. -/
theorem upperMaass_support_subset_closed (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsClosed K) (hs : Function.support f ⊆ K) :
    Function.support (upperMaass f) ⊆ K := by
  intro z hz
  by_contra hzK
  have hU : Kᶜ ∈ 𝓝 z := hK.isOpen_compl.mem_nhds hzK
  have hpre : ∀ᶠ p in 𝓝 (z.re, z.im), chartLift p ∈ Kᶜ :=
    (chartLift_continuous_positive z.im_pos).eventually
      (by simpa only [chartLift_pair] using hU)
  have heq : extendUpper f =ᶠ[𝓝 (z.re, z.im)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hpre, chart_open.mem_nhds z.im_pos] with p hp hpPos
    rw [extendUpper_chartLift f p hpPos]
    by_contra hnonzero
    exact hp (hs hnonzero)
  apply hz
  change chartMaass (extendUpper f) (z.re, z.im) = 0
  rw [chartMaass_eq_of_eventuallyEq heq]
  simp [chartMaass]

/-- One true compact transporter set controls input AND output locally. -/
theorem compactSeed_common_local_support (N : ℕ) (f : UpperHalfPlane → ℂ)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (z : UpperHalfPlane) :
    ∃ U ∈ 𝓝 z, ∃ S : Finset (effectiveGamma0 N), ∀ w ∈ U, ∀ q ∉ S,
      f (effectiveMatrixAction N q w) = 0 ∧
        upperMaass f (effectiveMatrixAction N q w) = 0 := by
  obtain ⟨U, hUc, hUn⟩ := exists_compact_mem_nhds z
  have hfinite := finite_effective_compact_hits N hUc hK
  refine ⟨U, hUn, hfinite.toFinset, ?_⟩
  intro w hw q hq
  have hzero (a : UpperHalfPlane → ℂ) (ha : Function.support a ⊆ K) :
      a (effectiveMatrixAction N q w) = 0 := by
    by_contra hn
    apply hq
    exact hfinite.mem_toFinset.mpr
      ⟨effectiveMatrixAction N q w, ⟨w, hw, rfl⟩, ha hn⟩
  exact ⟨hzero f hs, hzero _ (upperMaass_support_subset_closed f hK.isClosed hs)⟩

def translatedSeedChart (N : ℕ) (f : UpperHalfPlane → ℂ)
    (q : effectiveGamma0 N) (p : ℝ × ℝ) : ℂ :=
  extendUpper f (mobiusChart (effectiveRepresentative N q : SL(2, ℤ)) p)

theorem translatedSeedChart_eq_actual (N : ℕ) (f : UpperHalfPlane → ℂ)
    (q : effectiveGamma0 N) {p : ℝ × ℝ} (hp : 0 < p.2) :
    translatedSeedChart N f q p = f (effectiveMatrixAction N q (chartLift p)) :=
  extendUpper_mobiusChart f (effectiveRepresentative N q : SL(2, ℤ)) p hp

theorem translatedSeedChart_C2 (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) (q : effectiveGamma0 N) :
    ContDiffOn ℝ 2 (translatedSeedChart N f q) positiveChart := by
  intro p hp
  let g : SL(2, ℤ) := effectiveRepresentative N q
  have hgp : 0 < (mobiusChart g p).2 := by
    rw [mobiusChart_eq_actual g hp]
    exact (g • chartLift p).im_pos
  exact (((hf _ hgp).contDiffAt (chart_open.mem_nhds hgp)).comp p
    (mobiusChart_contDiffAt g hp)).contDiffWithinAt

theorem translatedSeedChart_maass (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart) (q : effectiveGamma0 N)
    (p : ℝ × ℝ) (hp : 0 < p.2) :
    chartMaass (translatedSeedChart N f q) p =
      upperMaass f (effectiveMatrixAction N q (chartLift p)) := by
  let g : SL(2, ℤ) := effectiveRepresentative N q
  have hgp : 0 < (mobiusChart g p).2 := by
    rw [mobiusChart_eq_actual g hp]
    exact (g • chartLift p).im_pos
  change chartMaass (fun r => extendUpper f (mobiusChart g r)) p = _
  rw [chartMaass_comp_mobiusChart g (extendUpper f) p hp
    ((hf _ hgp).contDiffAt (chart_open.mem_nhds hgp)), mobiusChart_eq_actual g hp]
  rfl

/-- The full generic compact-C2 commutation identity for the existing
upperMaass, not a postulated graph intertwining map. -/
theorem upperMaass_compactSeedTrace (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    upperMaass (complexSeedTrace N f) = complexSeedTrace N (upperMaass f) := by
  funext z
  let p : ℝ × ℝ := (z.re, z.im)
  have hp : 0 < p.2 := z.im_pos
  obtain ⟨U, hU, S, hS⟩ := compactSeed_common_local_support N f hK hs z
  have hpre : ∀ᶠ r in 𝓝 p, chartLift r ∈ U :=
    (chartLift_continuous_positive hp).eventually
      (by simpa only [p, chartLift_pair] using hU)
  have heq : extendUpper (complexSeedTrace N f) =ᶠ[𝓝 p]
      (fun r => ∑ q ∈ S, translatedSeedChart N f q r) := by
    filter_upwards [hpre, chart_open.mem_nhds hp] with r hr hrpos
    rw [extendUpper_chartLift _ r hrpos]
    change (∑' q : effectiveGamma0 N, f (effectiveMatrixAction N q (chartLift r))) = _
    rw [tsum_eq_sum (fun q hq => (hS (chartLift r) hr q hq).1)]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedSeedChart_eq_actual N f q hrpos).symm
  change chartMaass (extendUpper (complexSeedTrace N f)) p = _
  calc
    _ = chartMaass (fun r => ∑ q ∈ S, translatedSeedChart N f q r) p :=
      chartMaass_eq_of_eventuallyEq heq
    _ = ∑ q ∈ S, chartMaass (translatedSeedChart N f q) p :=
      chartMaass_finsetSum S (translatedSeedChart N f)
        (fun q _ => translatedSeedChart_C2 N f hf q) hp
    _ = ∑ q ∈ S, upperMaass f (effectiveMatrixAction N q z) := by
      apply Finset.sum_congr rfl
      intro q _
      simpa only [p, chartLift_pair] using translatedSeedChart_maass N f hf q p hp
    _ = complexSeedTrace N (upperMaass f) z :=
      (tsum_eq_sum (fun q hq => (hS z (mem_of_mem_nhds hU) q hq).2)).symm

theorem compactSeedTrace_chart_C2 (N : ℕ) (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    ContDiffOn ℝ 2 (extendUpper (complexSeedTrace N f)) positiveChart := by
  intro p hp
  obtain ⟨U, hU, S, hS⟩ := compact_seed_locally_finite N f hK hs (chartLift p)
  have heq : extendUpper (complexSeedTrace N f) =ᶠ[𝓝 p]
      (fun r => ∑ q ∈ S, translatedSeedChart N f q r) := by
    filter_upwards [(chartLift_continuous_positive hp).eventually hU,
      chart_open.mem_nhds hp] with r hr hrpos
    rw [extendUpper_chartLift _ r hrpos]
    change (∑' q : effectiveGamma0 N, f (effectiveMatrixAction N q (chartLift r))) = _
    rw [tsum_eq_sum (fun q hq => hS (chartLift r) hr q hq)]
    apply Finset.sum_congr rfl
    intro q _
    exact (translatedSeedChart_eq_actual N f q hrpos).symm
  have hsum : ContDiffAt ℝ 2 (fun r => ∑ q ∈ S, translatedSeedChart N f q r) p := by
    apply ContDiffAt.sum
    intro q _
    exact ((translatedSeedChart_C2 N f hf q) p hp).contDiffAt (chart_open.mem_nhds hp)
  exact (hsum.congr_of_eventuallyEq heq).contDiffWithinAt

theorem compactSeed_graph_memLp (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K) :
    MemLp (complexPoincare N f) 2 (carrierPushforward N) ∧
      MemLp (complexPoincare N (upperMaass f)) 2 (carrierPushforward N) :=
  ⟨compactPoincare_memLp_two N f (native_C2_continuous f hf) hK hs,
    compactPoincare_memLp_two N (upperMaass f) (native_C2_upperMaass_continuous f hf)
      hK (upperMaass_support_subset_closed f hK.isClosed hs)⟩

theorem compactSeed_graph_projection (N : ℕ) [NeZero N] (f : UpperHalfPlane → ℂ)
    (hf : ContDiffOn ℝ 2 (extendUpper f) positiveChart)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hs : Function.support f ⊆ K)
    (z : reducedCarrier N) :
    complexPoincare N (upperMaass f) (reducedProjection N z) =
      upperMaass (complexSeedTrace N f) z := by
  rw [complexPoincare_projection, upperMaass_compactSeedTrace N f hf hK hs]

end
end ImbalancedChen.Part3.ActualCompactSeedMaassJoin20261025a
