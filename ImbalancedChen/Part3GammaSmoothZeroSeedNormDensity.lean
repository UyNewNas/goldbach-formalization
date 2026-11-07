import ImbalancedChen.Part3GammaZeroSeedCompactLiftContinuity
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Pinned support-preserving smooth approximation is applied to each
original continuous compact height profile. All approximants retain the
original positive compact height support and one actual compact H carrier.
The proved actual compact-overlap estimate transfers uniform profile
approximation to strong convergence of the ORIGINAL quotient zeroSeedL2
vectors. The closed span of smooth zero seeds equals that of all original
HeightSeed vectors. Density is proved, not stored in an input field.
-/
namespace ImbalancedChen.Part3.GammaSmoothZeroSeedNormDensity20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualConstantMode20261025a
open ActualInfinityCuspAnnihilator20261026b
open SmoothZeroHeightSeedProfiles20261026b
open GammaZeroSeedCompactLiftContinuity20261026b GammaCompactSeedL2Transport20261026a

/-- Reuse the pinned genuine support-preserving smooth approximation;
no new profile density assumption or enlarged support is introduced. -/
theorem exists_smoothHeightSeed_uniform_approx (s : HeightSeed) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : SmoothHeightSeed, Function.support t.toFun ⊆ Function.support s.toFun ∧
      ∀ y : ℝ, ‖s.toFun y - t.toFun y‖ ≤ ε := by
  obtain ⟨g, hgs, hge, hsupport⟩ := s.continuous.exists_contDiff_approx ⊤
    (ε := fun _ => ε) continuous_const (fun _ => hε)
  have hts : tsupport g ⊆ tsupport s.toFun := closure_mono hsupport
  let t : SmoothHeightSeed :=
    { toFun := g
      continuous := hgs.continuous
      compact := s.compact.mono hsupport
      positive := hts.trans s.positive
      cinfty := hgs }
  refine ⟨t, hsupport, ?_⟩
  intro y
  simpa only [dist_eq_norm, norm_sub_rev] using (hge y).le

/-- One sequence retains the original compact height support; its true
zero-seed quotient vectors converge in the actual physical L2 norm. -/
theorem exists_smooth_zeroSeedL2_sequence (N : ℕ) [NeZero N] (s : HeightSeed) :
    ∃ t : ℕ → SmoothHeightSeed,
      (∀ n, Function.support (t n).toFun ⊆ Function.support s.toFun) ∧
      Tendsto (fun n => zeroSeedL2 N (t n).toHeightSeed) atTop (𝓝 (zeroSeedL2 N s)) := by
  classical
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  choose t hsupport herror using fun n => exists_smoothHeightSeed_uniform_approx s (hδ n)
  refine ⟨t, hsupport, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  let C := transportConstant N (heightProfileCompactCarrier s)
  have hbound : ∀ n, ‖zeroSeedL2 N (t n).toHeightSeed - zeroSeedL2 N s‖ ≤ C * δ n := by
    intro n
    rw [norm_sub_rev]
    exact zeroSeedL2_uniform_difference_bound N s (t n).toHeightSeed
      (closure_mono (hsupport n)) (hδ n).le (herror n)
  apply squeeze_zero (fun n => norm_nonneg _) hbound
  simpa only [mul_zero] using (tendsto_const_nhds.mul
    (show Tendsto δ atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat))

def smoothZeroSeedClosedSpan (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (Submodule.span ℂ (Set.range (fun s : SmoothHeightSeed => zeroSeedL2 N s.toHeightSeed))).topologicalClosure

def continuousZeroSeedClosedSpan (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (Submodule.span ℂ (Set.range (zeroSeedL2 N))).topologicalClosure

theorem zeroSeedL2_mem_smoothZeroSeedClosedSpan (N : ℕ) [NeZero N] (s : HeightSeed) :
    zeroSeedL2 N s ∈ smoothZeroSeedClosedSpan N := by
  obtain ⟨t, _hsupport, hlim⟩ := exists_smooth_zeroSeedL2_sequence N s
  apply (Submodule.span ℂ
    (Set.range (fun s : SmoothHeightSeed => zeroSeedL2 N s.toHeightSeed))).isClosed_topologicalClosure.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    (Submodule.span ℂ _).le_topologicalClosure (Submodule.subset_span ⟨t n, rfl⟩)

/-- Equality of genuine physical closed spans, derived from the actual
norm convergence rather than a spectral/completeness hypothesis. -/
theorem smoothZeroSeedClosedSpan_eq_continuousZeroSeedClosedSpan (N : ℕ) [NeZero N] :
    smoothZeroSeedClosedSpan N = continuousZeroSeedClosedSpan N := by
  apply le_antisymm
  · apply (Submodule.span ℂ
      (Set.range (fun s : SmoothHeightSeed => zeroSeedL2 N s.toHeightSeed))).topologicalClosure_minimal
      _ (Submodule.isClosed_topologicalClosure _)
    apply Submodule.span_le.mpr
    rintro v ⟨s, rfl⟩
    exact (Submodule.span ℂ _).le_topologicalClosure (Submodule.subset_span ⟨s.toHeightSeed, rfl⟩)
  · apply (Submodule.span ℂ (Set.range (zeroSeedL2 N))).topologicalClosure_minimal
      _ (Submodule.isClosed_topologicalClosure _)
    apply Submodule.span_le.mpr
    rintro v ⟨s, rfl⟩
    exact zeroSeedL2_mem_smoothZeroSeedClosedSpan N s

end
end ImbalancedChen.Part3.GammaSmoothZeroSeedNormDensity20261026b
