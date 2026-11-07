import ImbalancedChen.Part3GammaSmoothZeroSeedNormDensity

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Smooth compact positive-height zero-seed tests characterize the ORIGINAL
full infinity-cusp annihilator, because their actual quotient L2 vectors
approximate every original continuous HeightSeed vector in norm. The
actual native Friedrichs output of any true-domain annihilator vector
therefore lies in that same ORIGINAL full infinity-cusp subspace.

The proof uses the actual zero-seed native graph, the original physical
test characterization and genuine norm density. It does not assert
resolvent reduction, dense restricted domain, self-adjoint restriction,
all-cusp membership, compact resolvent, or cusp/Eisenstein completeness.
-/
namespace ImbalancedChen.Part3.GammaInfinityCuspNativeOutputInvariance20261026b

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Gamma0ActualConstantMode20261025a
open Gamma0ActualFriedrichsOperator20261025a
open ActualInfinityCuspAnnihilator20261026b
open SmoothZeroHeightSeedProfiles20261026b
open GammaSmoothZeroSeedNativeGraph20261026b
open GammaSmoothZeroSeedNormDensity20261026b

/-- Actual strong quotient-norm density upgrades smooth physical test
annihilation to every original continuous compact HeightSeed test. -/
theorem infinityCusp_mem_iff_smooth_zeroSeed_tests (N : ℕ) [NeZero N] (u : QuotientL2 N) :
    u ∈ infinityCuspSubspace N ↔
      ∀ s : SmoothHeightSeed, inner ℂ (zeroSeedL2 N s.toHeightSeed) u = 0 := by
  constructor
  · intro hu s
    exact (mem_infinityCuspSubspace_iff N u).mp hu s.toHeightSeed
  · intro hsmooth
    apply (mem_infinityCuspSubspace_iff N u).mpr
    intro s
    obtain ⟨t, _hsupport, hlim⟩ := exists_smooth_zeroSeedL2_sequence N s
    have hi : Tendsto (fun n => inner ℂ (zeroSeedL2 N (t n).toHeightSeed) u)
        atTop (𝓝 (inner ℂ (zeroSeedL2 N s) u)) :=
      hlim.inner (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))
    have hzero : Tendsto (fun n => inner ℂ (zeroSeedL2 N (t n).toHeightSeed) u)
        atTop (𝓝 (0 : ℂ)) := by
      have heq : (fun n => inner ℂ (zeroSeedL2 N (t n).toHeightSeed) u) =
          (fun _ : ℕ => (0 : ℂ)) := funext (fun n => hsmooth (t n))
      rw [heq]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hi hzero

/-- Native output invariance of the ACTUAL full infinity-cusp annihilator.
Operator-domain membership is the original native one, not a surrogate. -/
theorem actual_friedrichs_infinityCusp_output_mem (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain)
    (hu : (u : QuotientL2 N) ∈ infinityCuspSubspace N) :
    actualGammaFriedrichs N u ∈ infinityCuspSubspace N := by
  apply (infinityCusp_mem_iff_smooth_zeroSeed_tests N (actualGammaFriedrichs N u)).mpr
  intro s
  exact native_cusp_output_annihilates_smooth_zeroSeeds N u hu s

/-- Exact actual graph version: input in the full physical infinity-cusp
annihilator forces its actual native output to satisfy every original test. -/
theorem actual_native_graph_infinityCusp_output_mem (N : ℕ) [NeZero N]
    {u v : QuotientL2 N} (huv : (u, v) ∈ (actualGammaFriedrichs N).graph)
    (hu : u ∈ infinityCuspSubspace N) : v ∈ infinityCuspSubspace N := by
  obtain ⟨w, hw, hout⟩ := LinearPMap.mem_graph_iff.mp huv
  rw [← hout]
  exact actual_friedrichs_infinityCusp_output_mem N w (by simpa only [hw] using hu)

/-- The all-original-test conclusion, stated directly for applications
which need the actual incomplete Eisenstein pairing rather than membership. -/
theorem actual_native_cusp_output_all_height_tests_zero (N : ℕ) [NeZero N]
    (u : (actualGammaFriedrichs N).domain)
    (hu : (u : QuotientL2 N) ∈ infinityCuspSubspace N) (s : HeightSeed) :
    inner ℂ (zeroSeedL2 N s) (actualGammaFriedrichs N u) = 0 :=
  (mem_infinityCuspSubspace_iff N (actualGammaFriedrichs N u)).mp
    (actual_friedrichs_infinityCusp_output_mem N u hu) s

end
end ImbalancedChen.Part3.GammaInfinityCuspNativeOutputInvariance20261026b
