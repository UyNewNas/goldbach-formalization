import ImbalancedChen.Part3ActualKCandidateEnergyExhaustion
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
SOURCEONLY / UNCOMPILED / CODE_ONLY, 2026-10-24.

The explicit measure in `Part3KLDensityMeasure` has finite mass on compact
sets.  Consequently the usual compactly supported smooth functions form an
L² core, both for the whole real candidate parameter and for its positive
restriction.  The final theorem applies this core to the actual K-test
transform only under the separate uniform finite-energy hypothesis from
`Part3ActualKCandidateEnergyExhaustion`.

No Plancherel identity, spectral-measure identification, or uniform-energy
bound is asserted here.  A smooth function on the real line used against the
positive restriction need not vanish near zero; its restriction is smooth on
the open positive axis but need not have support compact in that axis.
-/

namespace ImbalancedChen.Part3.KLCandidateSmoothCore20261024zz
noncomputable section

open Set MeasureTheory
open P3KLDensityMeasureSourceOnly
open ActualKCandidateEnergyExhaustion20261024z
open P3ActualLiteralPacketIntegralSourceOnly
open P3NativePeriod64SamplingSourceOnly (D4)

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The only measure input needed by Mathlib's smooth-core theorem. -/
local instance candidateMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts candidateMeasure := by
  refine ⟨?_⟩
  intro K hK
  exact candidateMeasure_compact_lt_top hK

def positiveCandidateMeasure : Measure ℝ :=
  candidateMeasure.restrict (Ioi (0 : ℝ))

local instance positiveCandidateMeasure_finiteOnCompacts :
    IsFiniteMeasureOnCompacts positiveCandidateMeasure := by
  dsimp [positiveCandidateMeasure]
  infer_instance

/-- Smooth compactly supported functions are dense in L² for the explicit
whole-line candidate measure.  This is an actual L² closure statement. -/
theorem candidate_smooth_core_dense :
    Dense {F : Lp ℂ (2 : ℝ≥0∞) candidateMeasure |
      ∃ g : ℝ → ℂ,
        ↑↑F =ᵐ[candidateMeasure] g ∧
        HasCompactSupport g ∧ ContDiff ℝ ⊤ g} := by
  exact Lp.dense_hasCompactSupport_contDiff
    (μ := candidateMeasure) (p := (2 : ℝ≥0∞)) (by norm_num)

/-- The same L² closure statement for the candidate measure restricted to
strictly positive real parameters. -/
theorem positive_candidate_smooth_core_dense :
    Dense {F : Lp ℂ (2 : ℝ≥0∞) positiveCandidateMeasure |
      ∃ g : ℝ → ℂ,
        ↑↑F =ᵐ[positiveCandidateMeasure] g ∧
        HasCompactSupport g ∧ ContDiff ℝ ⊤ g} := by
  exact Lp.dense_hasCompactSupport_contDiff
    (μ := positiveCandidateMeasure) (p := (2 : ℝ≥0∞)) (by norm_num)

/-- Strong L² approximation in representatives, with a concrete error bound. -/
theorem positive_candidate_smooth_approx {f : ℝ → ℂ}
    (hf : MemLp f 2 positiveCandidateMeasure) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ ⊤ g ∧
      eLpNorm (f - g) 2 positiveCandidateMeasure ≤ ENNReal.ofReal ε := by
  exact hf.exist_eLpNorm_sub_le (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hε

/-- Conditional strong smooth-core approximation of the actual K transform.
The uniform finite bound is an explicit premise, not a result of this file. -/
theorem actualK_candidate_smooth_approx {ι : Type*}
    (P : PacketData ι) (k : D4 → ℤ) {C : ℝ≥0∞}
    (hC : C < ∞)
    (hbound : ∀ N : ℕ, truncatedCandidateEnergy P k N ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ ⊤ g ∧
      eLpNorm (kTestTransform P k - g) 2 candidateMeasure ≤
        ENNReal.ofReal ε := by
  have hf : MemLp (kTestTransform P k) 2 candidateMeasure :=
    actualK_memLp_two_of_uniform_bound P k hC hbound
  exact hf.exist_eLpNorm_sub_le (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hε

end
end ImbalancedChen.Part3.KLCandidateSmoothCore20261024zz
