import ImbalancedChen.Part3Gamma0ActualSigmaHeatResolvent
import ImbalancedChen.Part3GammaZeroAtomConstantClosure

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The physical mean-zero subspace of the actual Gamma0 quotient is invariant
under its actual heat and positive shifted Friedrichs resolvents. Constant
preservation is deduced from the proved native constant graph and the
actual Sigma multiplier action. No mean-preservation premise, spectral gap,
whole-plane Hardy estimate, or automorphic spectral classification is used.
-/
namespace ImbalancedChen.Part3.GammaHeatMeanInvariant20261026b

noncomputable section
open Set MeasureTheory
open Gamma0ActualSmoothQuotientCore20261025a
open Gamma0QuotientCellPushforward20261025a
open Gamma0ActualConstantMode20261025a
open Gamma0ActualFriedrichsOperator20261025a
open Gamma0ActualShiftedFriedrichsResolvent20261025a
open Gamma0ActualHeatGenerator20261025a
open Gamma0ActualSigmaPlancherel20261025a
open Gamma0ActualSigmaHeatResolvent20261025a
open GammaConstantFormClosure20261026a
open GammaConstantRankOneProjection20261026a
open GammaZeroAtomConstantClosure20261026a

/-- The actual unnormalized physical mean is a continuous functional. -/
def actualMeanZero (N : ℕ) [NeZero N] : Submodule ℂ (QuotientL2 N) :=
  (innerSL ℂ (constantL2 N)).ker

theorem mem_actualMeanZero_iff (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    f ∈ actualMeanZero N ↔ ∫ q, f q ∂carrierPushforward N = 0 := by
  change inner ℂ (constantL2 N) f = 0 ↔ _
  rw [constantL2_inner]

theorem actualMeanZero_isClosed (N : ℕ) [NeZero N] :
    IsClosed (actualMeanZero N : Set (QuotientL2 N)) :=
  (innerSL ℂ (constantL2 N)).isClosed_ker

/-- The native zero graph forces the true heat multiplier to be one
on every nonzero spectral coordinate of the physical constant. -/
theorem actualGammaHeat_constant (N : ℕ) [NeZero N] {t : ℝ} (ht : 0 ≤ t) :
    actualGammaHeat N t (constantL2 N) = constantL2 N := by
  apply (actualSigmaPlancherel N).injective
  apply Lp.ext
  have hg := (actualGammaFriedrichs_sigma_graph_iff_lambda N (constantL2 N) 0).mp
    (constantL2_mem_friedrichsGraph_zero N)
  rw [map_zero] at hg
  filter_upwards [actualGammaHeat_sigma_action_ae N ht (constantL2 N), hg,
    Lp.coeFn_zero ℂ 2 (actualSigmaMeasure N)] with s hs hgraph hzero
  rw [hs]
  change (Real.exp (-t * actualSigmaLambda N s) : ℂ) *
    actualSigmaPlancherel N (constantL2 N) s = _
  change (0 : ActualSigmaL2 N) s =
    (actualSigmaLambda N s : ℂ) * actualSigmaPlancherel N (constantL2 N) s at hgraph
  rw [hzero] at hgraph
  by_cases hl : actualSigmaLambda N s = 0
  · simp only [hl, mul_zero, neg_zero, Real.exp_zero, Complex.ofReal_one, one_mul]
  · have hlC : (actualSigmaLambda N s : ℂ) ≠ 0 := by exact_mod_cast hl
    have hf : actualSigmaPlancherel N (constantL2 N) s = 0 :=
      (mul_eq_zero.mp hgraph.symm).resolve_left hlC
    simp only [hf, mul_zero]

/-- Preservation of the literal carrierPushforward integral. -/
theorem actualGammaHeat_preserves_mean (N : ℕ) [NeZero N] {t : ℝ}
    (ht : 0 ≤ t) (f : QuotientL2 N) :
    (∫ q, actualGammaHeat N t f q ∂carrierPushforward N) =
      ∫ q, f q ∂carrierPushforward N := by
  rw [← constantL2_inner, ← constantL2_inner,
    ← (actualGammaHeat_selfAdjoint N t).isSymmetric,
    actualGammaHeat_constant N ht]

theorem actualGammaHeat_meanZero_invariant (N : ℕ) [NeZero N] {t : ℝ}
    (ht : 0 ≤ t) {f : QuotientL2 N} (hf : f ∈ actualMeanZero N) :
    actualGammaHeat N t f ∈ actualMeanZero N := by
  rw [mem_actualMeanZero_iff] at hf ⊢
  rw [actualGammaHeat_preserves_mean N ht f, hf]

/-- The native shifted inverse acts on the genuine constant by 1/a. -/
theorem actualGammaShiftedResolvent_constant (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0 < a) :
    actualGammaShiftedResolvent N a (constantL2 N) =
      ((a⁻¹ : ℝ) : ℂ) • constantL2 N := by
  have h := actualGammaShiftedResolvent_on_domain N ha (constantDomainPoint N)
  rw [actualGammaFriedrichs_constant, add_zero] at h
  change actualGammaShiftedResolvent N a ((a : ℂ) • constantL2 N) = constantL2 N at h
  rw [map_smul] at h
  have hinv : ((a⁻¹ : ℝ) : ℂ) * (a : ℂ) = 1 := by
    exact_mod_cast inv_mul_cancel₀ ha.ne'
  calc
    _ = ((a⁻¹ : ℝ) : ℂ) • ((a : ℂ) •
        actualGammaShiftedResolvent N a (constantL2 N)) := by
      rw [smul_smul, hinv, one_smul]
    _ = _ := by rw [h]

theorem actualGammaShiftedResolvent_mean (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0 < a) (f : QuotientL2 N) :
    (∫ q, actualGammaShiftedResolvent N a f q ∂carrierPushforward N) =
      ((a⁻¹ : ℝ) : ℂ) * (∫ q, f q ∂carrierPushforward N) := by
  rw [← constantL2_inner, ← constantL2_inner,
    ← (actualGammaShiftedResolvent_selfAdjoint N a).isSymmetric,
    actualGammaShiftedResolvent_constant N ha, inner_smul_left]
  simp

theorem actualGammaShiftedResolvent_meanZero_invariant (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0 < a) {f : QuotientL2 N} (hf : f ∈ actualMeanZero N) :
    actualGammaShiftedResolvent N a f ∈ actualMeanZero N := by
  rw [mem_actualMeanZero_iff] at hf ⊢
  rw [actualGammaShiftedResolvent_mean N ha f, hf, mul_zero]

/-- Orthogonal centering uses the actual constant projection. -/
def actualCenteredVector (N : ℕ) [NeZero N] (f : QuotientL2 N) : QuotientL2 N :=
  f - constantRankOne N f

theorem actualCenteredVector_mem_meanZero (N : ℕ) [NeZero N] (f : QuotientL2 N) :
    actualCenteredVector N f ∈ actualMeanZero N := by
  change inner ℂ (constantL2 N) (f - constantRankOne N f) = 0
  rw [inner_sub_right, constantRankOne_apply_mean, inner_smul_right,
    constantL2_inner, constantL2_inner_self]
  have hv : (actualVolume N : ℂ) ≠ 0 := by exact_mod_cast (actualVolume_pos N).ne'
  field_simp

theorem actualGammaHeat_constantProjection (N : ℕ) [NeZero N] {t : ℝ}
    (ht : 0 ≤ t) (f : QuotientL2 N) :
    actualGammaHeat N t (constantRankOne N f) = constantRankOne N f := by
  rw [constantRankOne_apply_mean, map_smul, actualGammaHeat_constant N ht]

theorem constantProjection_actualGammaHeat (N : ℕ) [NeZero N] {t : ℝ}
    (ht : 0 ≤ t) (f : QuotientL2 N) :
    constantRankOne N (actualGammaHeat N t f) = constantRankOne N f := by
  rw [constantRankOne_apply_mean, constantRankOne_apply_mean,
    actualGammaHeat_preserves_mean N ht f]

theorem actualGammaHeat_centered (N : ℕ) [NeZero N] {t : ℝ}
    (ht : 0 ≤ t) (f : QuotientL2 N) :
    actualGammaHeat N t (actualCenteredVector N f) =
      actualGammaHeat N t f - constantRankOne N f := by
  rw [actualCenteredVector, map_sub, actualGammaHeat_constantProjection N ht f]

theorem actualCenteredVector_heat (N : ℕ) [NeZero N] {t : ℝ}
    (ht : 0 ≤ t) (f : QuotientL2 N) :
    actualCenteredVector N (actualGammaHeat N t f) =
      actualGammaHeat N t (actualCenteredVector N f) := by
  rw [actualGammaHeat_centered N ht f, actualCenteredVector,
    constantProjection_actualGammaHeat N ht f]

theorem actualGammaShiftedResolvent_centered (N : ℕ) [NeZero N]
    {a : ℝ} (ha : 0 < a) (f : QuotientL2 N) :
    actualGammaShiftedResolvent N a (actualCenteredVector N f) =
      actualCenteredVector N (actualGammaShiftedResolvent N a f) := by
  simp only [actualCenteredVector, map_sub]
  rw [constantRankOne_apply_mean, constantRankOne_apply_mean,
    actualGammaShiftedResolvent_mean N ha f, map_smul,
    actualGammaShiftedResolvent_constant N ha, smul_smul]
  apply congrArg (fun z : ℂ => actualGammaShiftedResolvent N a f - z • constantL2 N)
  ring

end
end ImbalancedChen.Part3.GammaHeatMeanInvariant20261026b
