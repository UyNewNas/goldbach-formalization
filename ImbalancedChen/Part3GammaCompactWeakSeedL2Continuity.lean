import ImbalancedChen.Part3GammaCompactWeakSeedPoincareL2
import ImbalancedChen.Part3GammaCompactSeedL2Transport

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Exact compact weak-seed subtraction and strong actual quotient L2
continuity. The SAME support container controls every sequence member
and its limit; the compact-overlap coefficient is independent of n.
-/

namespace ImbalancedChen.Part3.GammaCompactWeakSeedL2Continuity20261026b
noncomputable section
open Set Function Filter MeasureTheory
open scoped UpperHalfPlane Topology
open Gamma0QuotientCellPushforward20261025a Gamma0ComplexL1PoincareUnfolding20261025a
open Gamma0CompactGlobalOverlap20261025a GammaCompactSeedL2Transport20261026a
open Gamma0ActualSmoothQuotientCore20261025a GammaCompactWeakSeedPoincareL220261026b

theorem weakSeedL2_sub (N : ℕ) [NeZero N]
    (a b : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K)
    (has : Function.support a ⊆ K) (hbs : Function.support b ⊆ K) :
    weakSeedL2 N (a-b) (ha.sub hb) K hK (sub_support_subset has hbs) =
      weakSeedL2 N a ha K hK has - weakSeedL2 N b hb K hK hbs := by
  apply Lp.ext
  filter_upwards [weakSeedL2_ae N (a-b) (ha.sub hb) K hK (sub_support_subset has hbs),
    weakSeedL2_ae N a ha K hK has, weakSeedL2_ae N b hb K hK hbs,
    compactQuotient_sub_ae N a b hK has hbs,
    Lp.coeFn_sub (weakSeedL2 N a ha K hK has) (weakSeedL2 N b hb K hK hbs)]
    with q hsub hfa hfb htrace hlp
  simp only [Pi.sub_apply] at htrace
  rw [hsub, hlp, hfa, hfb]
  exact htrace

theorem weakSeedL2_difference_norm_sq_le (N : ℕ) [NeZero N]
    (a b : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume) (hb : MemLp b 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K)
    (has : Function.support a ⊆ K) (hbs : Function.support b ⊆ K) :
    ‖weakSeedL2 N a ha K hK has - weakSeedL2 N b hb K hK hbs‖^2 ≤
      (compactOverlapBound N K : ℝ) * ‖ha.toLp a - hb.toLp b‖^2 := by
  rw [← weakSeedL2_sub N a b ha hb K hK has hbs, ← MemLp.toLp_sub ha hb]
  exact weakSeedL2_norm_sq_le N (a-b) (ha.sub hb) K hK (sub_support_subset has hbs)

/-- True strong continuity on compactly supported seed L2 families. -/
theorem weakSeedL2_tendsto (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : MemLp a 2 volume)
    (aSeq : ℕ → UpperHalfPlane → ℂ) (hSeq : ∀ n, MemLp (aSeq n) 2 volume)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (has : Function.support a ⊆ K)
    (hSeqs : ∀ n, Function.support (aSeq n) ⊆ K)
    (hlim : Tendsto (fun n => (hSeq n).toLp (aSeq n)) atTop (𝓝 (ha.toLp a))) :
    Tendsto (fun n => weakSeedL2 N (aSeq n) (hSeq n) K hK (hSeqs n)) atTop
      (𝓝 (weakSeedL2 N a ha K hK has)) := by
  have hseed : Tendsto (fun n => (hSeq n).toLp (aSeq n) - ha.toLp a) atTop (𝓝 0) := by
    simpa only [sub_self] using hlim.sub tendsto_const_nhds
  have hbound (n : ℕ) := weakSeedL2_difference_norm_sq_le N (aSeq n) a (hSeq n) ha
    K hK (hSeqs n) has
  have hsquare : Tendsto (fun n =>
      ‖weakSeedL2 N (aSeq n) (hSeq n) K hK (hSeqs n) - weakSeedL2 N a ha K hK has‖^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hbound
    simpa using tendsto_const_nhds.mul (hseed.norm.pow 2)
  have hnorm := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsquare
  have hdiff : Tendsto (fun n =>
      weakSeedL2 N (aSeq n) (hSeq n) K hK (hSeqs n) - weakSeedL2 N a ha K hK has)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hnorm
  simpa only [sub_add_cancel, zero_add] using hdiff.add tendsto_const_nhds

/-- Agreement with the old continuous-seed construction is proved from
their actual common quotient representatives. -/
theorem weakSeedL2_eq_seedL2 (N : ℕ) [NeZero N]
    (a : UpperHalfPlane → ℂ) (ha : Continuous a)
    (K : Set UpperHalfPlane) (hK : IsCompact K) (hs : Function.support a ⊆ K) :
    weakSeedL2 N a (ha.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact hK hs)) K hK hs =
      seedL2 N a ha K hK hs := by
  apply Lp.ext
  exact (weakSeedL2_ae N a _ K hK hs).trans (seedL2_ae N a ha K hK hs).symm

end
end ImbalancedChen.Part3.GammaCompactWeakSeedL2Continuity20261026b
