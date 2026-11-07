import ImbalancedChen.Part3ActualTensorFormCoreExhaustion
import ImbalancedChen.Part3ActualNestedTensorRitzGradientLimits
import ImbalancedChen.Part3ActualCompletedEnergyResolvent
import ImbalancedChen.Part3ActualCompletedTensorEnergyGreen

/-!
The concrete actual first-gradient form-core exhaustion converges in the
actual completed energy space to the constructed Riesz weak solution.
The proof uses the actual simultaneous core approximation theorem, never
H-only density as a substitute for form-core density. It identifies all
three Ritz limits and gives the exact energy-norm error formula.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualExhaustionRitzResolventLimit20261025a

noncomputable section

open Set Filter Topology
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.ActualTensorGradientLinearMaps20261025a
open ImbalancedChen.Part3.ActualFiniteTensorWeakResolvent20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzL2Limit20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzGradientLimits20261025a
open ImbalancedChen.Part3.ActualTensorFormCoreExhaustionSourceOnly
open ImbalancedChen.Part3.ActualCompletedTensorEnergyForm20261025a
open ImbalancedChen.Part3.ActualCompletedTensorEnergyGreen20261025a
open ImbalancedChen.Part3.ActualCompletedEnergyResolvent20261025a

theorem exhaustion_nested (k : ℕ) :
    actualFiniteTensorSpan (exhaustionSize k) (exhaustionTensors k) ≤
      actualFiniteTensorSpan (exhaustionSize (k + 1)) (exhaustionTensors (k + 1)) :=
  trialSpace_le_succ k

def trialFormSet (n : ℕ) : Set completedEnergy :=
  {w | ∃ v : actualTensorDomain, (v : HyperbolicL2) ∈ trialSpace n ∧ w = coreEmbedding v}

private theorem coreEmbedding_norm_sub_le (v u : actualTensorDomain) :
    ‖coreEmbedding v - coreEmbedding u‖ ≤
      ‖(v : HyperbolicL2) - (u : HyperbolicL2)‖ +
        ‖actualGradient false v - actualGradient false u‖ +
        ‖actualGradient true v - actualGradient true u‖ := by
  have hn := coreEmbedding_norm_sq_eq_energy (v - u)
  rw [map_sub] at hn
  have he := shiftedEnergy_eq_gradient_norms (v - u)
  rw [map_sub, map_sub] at he
  change shiftedEnergy (v - u) =
    ‖(v : HyperbolicL2) - (u : HyperbolicL2)‖ ^ 2 +
      ‖actualGradient false v - actualGradient false u‖ ^ 2 +
      ‖actualGradient true v - actualGradient true u‖ ^ 2 at he
  have ha := norm_nonneg ((v : HyperbolicL2) - (u : HyperbolicL2))
  have hb := norm_nonneg (actualGradient false v - actualGradient false u)
  have hc := norm_nonneg (actualGradient true v - actualGradient true u)
  have hd := norm_nonneg (coreEmbedding v - coreEmbedding u)
  nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]

/-- This is density in the actual completed form norm, proved from the
true three-component form-core exhaustion and the actual core closure. -/
theorem trialFormUnion_dense : Dense (⋃ n : ℕ, trialFormSet n) := by
  have hcore : range coreEmbedding ⊆ closure (⋃ n : ℕ, trialFormSet n) := by
    rintro _ ⟨u, rfl⟩
    apply Metric.mem_closure_iff.2
    intro epsilon hepsilon
    obtain ⟨n, v, hv, hH, hx, hy⟩ := exists_trialSpace_form_approx u
      (show 0 < epsilon / 3 by positivity)
    refine ⟨coreEmbedding v, mem_iUnion.2 ⟨n, v, hv, rfl⟩, ?_⟩
    have hb := coreEmbedding_norm_sub_le v u
    have hd : ‖coreEmbedding v - coreEmbedding u‖ < epsilon := by linarith
    simpa only [dist_eq_norm, norm_sub_rev] using hd
  have hclosure := closure_minimal hcore isClosed_closure
  intro u
  exact hclosure (coreEmbedding_denseRange u)

def exhaustionEnergyRitz (f : HyperbolicL2) (n : ℕ) : completedEnergy :=
  coreEmbedding (ritzVector (exhaustionSize n) (exhaustionTensors n) f)

theorem exhaustionEnergyRitz_norm_sq (f : HyperbolicL2) (n : ℕ) :
    ‖exhaustionEnergyRitz f n‖ ^ 2 =
      ritzEnergySequence exhaustionSize exhaustionTensors f n :=
  coreEmbedding_norm_sq_eq_energy _

theorem exhaustionEnergyRitz_norm_sub_sq (f : HyperbolicL2) (i j : ℕ) :
    ‖exhaustionEnergyRitz f j - exhaustionEnergyRitz f i‖ ^ 2 =
      |ritzEnergySequence exhaustionSize exhaustionTensors f j -
        ritzEnergySequence exhaustionSize exhaustionTensors f i| := by
  change ‖coreEmbedding (ritzVector (exhaustionSize j) (exhaustionTensors j) f) -
    coreEmbedding (ritzVector (exhaustionSize i) (exhaustionTensors i) f)‖ ^ 2 = _
  rw [← map_sub, coreEmbedding_norm_sq_eq_energy]
  exact ritz_shiftedEnergy_error_eq_abs_increment exhaustionSize exhaustionTensors exhaustion_nested f i j

theorem cauchySeq_exhaustionEnergyRitz (f : HyperbolicL2) :
    CauchySeq (exhaustionEnergyRitz f) := by
  have henergy := (tendsto_ritzEnergySequence exhaustionSize exhaustionTensors exhaustion_nested f).cauchySeq
  apply Metric.cauchySeq_iff'.2
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 henergy (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  refine ⟨N, ?_⟩
  intro k hk
  have hn := exhaustionEnergyRitz_norm_sub_sq f N k
  have he : |ritzEnergySequence exhaustionSize exhaustionTensors f k -
      ritzEnergySequence exhaustionSize exhaustionTensors f N| < epsilon ^ 2 := by
    simpa only [Real.dist_eq] using hN k hk
  have hs : ‖exhaustionEnergyRitz f k - exhaustionEnergyRitz f N‖ < epsilon := by
    nlinarith [norm_nonneg (exhaustionEnergyRitz f k - exhaustionEnergyRitz f N)]
  simpa only [dist_eq_norm] using hs

/-- The actual finite weak equation for a literal test in the current
trial space, translated by the true complex core Green identity. -/
theorem exhaustionEnergyRitz_trial_weak (f : HyperbolicL2) (n : ℕ)
    (v : actualTensorDomain) (hv : (v : HyperbolicL2) ∈ trialSpace n) :
    inner ℂ (coreEmbedding v) (exhaustionEnergyRitz f n) = inner ℂ (v : HyperbolicL2) f := by
  rw [exhaustionEnergyRitz, coreEmbedding_inner_eq_shiftedMaass]
  change inner ℂ (v : HyperbolicL2)
    ((ritzSolution (exhaustionSize n) (exhaustionTensors n) f : HyperbolicL2) +
      actualFiniteTensorLaplacian (exhaustionSize n) (exhaustionTensors n)
        (ritzSolution (exhaustionSize n) (exhaustionTensors n) f)) = _
  exact ritzSolution_weak (exhaustionSize n) (exhaustionTensors n) f ⟨(v : HyperbolicL2), hv⟩

/-- The concrete form-dense exhaustion converges to the genuine actual
Riesz solution. No convergence or density premise is supplied. -/
theorem tendsto_exhaustionEnergyRitz (f : HyperbolicL2) :
    Tendsto (exhaustionEnergyRitz f) atTop (𝓝 (energyRieszSolution f)) := by
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete (cauchySeq_exhaustionEnergyRitz f)
  have heq : u = energyRieszSolution f := by
    apply trialFormUnion_dense.eq_of_inner_right ℂ
    intro w hw
    obtain ⟨n, v, hv, rfl⟩ := mem_iUnion.1 hw
    have hleft : Tendsto (fun k => inner ℂ (coreEmbedding v) (exhaustionEnergyRitz f k))
        atTop (𝓝 (inner ℂ (coreEmbedding v) u)) := tendsto_const_nhds.inner hu
    have hconst : Tendsto (fun k => inner ℂ (coreEmbedding v) (exhaustionEnergyRitz f k))
        atTop (𝓝 (inner ℂ (v : HyperbolicL2) f)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with k hk
      exact (exhaustionEnergyRitz_trial_weak f k v (trialSpace_monotone hk hv)).symm
    exact (tendsto_nhds_unique hleft hconst).trans (energyRieszSolution_coreWeak f v).symm
  simpa only [heq] using hu

/-- Exact completed-energy error, retaining the actual finite trial
energy rather than an assumed error budget. -/
theorem exhaustionEnergyRitz_error_exact (f : HyperbolicL2) (n : ℕ) :
    ‖energyRieszSolution f - exhaustionEnergyRitz f n‖ ^ 2 =
      ‖energyRieszSolution f‖ ^ 2 -
        ritzEnergySequence exhaustionSize exhaustionTensors f n := by
  let v := ritzVector (exhaustionSize n) (exhaustionTensors n) f
  have hv : (v : HyperbolicL2) ∈ trialSpace n :=
    (ritzSolution (exhaustionSize n) (exhaustionTensors n) f).property
  have hR := energyRieszSolution_coreWeak f v
  have hF := exhaustionEnergyRitz_trial_weak f n v hv
  change inner ℂ (exhaustionEnergyRitz f n) (energyRieszSolution f) = _ at hR
  change inner ℂ (exhaustionEnergyRitz f n) (exhaustionEnergyRitz f n) = _ at hF
  have hc := congrArg Complex.re (hR.trans hF.symm)
  have hs := inner_re_symm (𝕜 := ℂ) (energyRieszSolution f) (exhaustionEnergyRitz f n)
  have hself : (inner ℂ (exhaustionEnergyRitz f n) (exhaustionEnergyRitz f n)).re =
      ‖exhaustionEnergyRitz f n‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow, Complex.ofReal_re]
  have hn := norm_sub_sq (𝕜 := ℂ) (energyRieszSolution f) (exhaustionEnergyRitz f n)
  have hE := exhaustionEnergyRitz_norm_sq f n
  linarith only [hc, hs, hself, hn, hE]

theorem tendsto_exhaustionEnergyRitz_error_zero (f : HyperbolicL2) :
    Tendsto (fun n => ‖energyRieszSolution f - exhaustionEnergyRitz f n‖ ^ 2) atTop (𝓝 0) := by
  have h : Tendsto (fun n => ‖energyRieszSolution f - exhaustionEnergyRitz f n‖ ^ 2)
      atTop (𝓝 (‖energyRieszSolution f - energyRieszSolution f‖ ^ 2)) :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => energyRieszSolution f)
      atTop (𝓝 (energyRieszSolution f))).sub (tendsto_exhaustionEnergyRitz f)).norm.pow 2
  simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h

/-- The scalar energy supremum of this actual form-core exhaustion is
the energy of the genuine Riesz weak solution. -/
theorem exhaustionEnergySup_eq_Riesz_norm_sq (f : HyperbolicL2) :
    ritzEnergySup exhaustionSize exhaustionTensors f = ‖energyRieszSolution f‖ ^ 2 := by
  have hleft := tendsto_ritzEnergySequence exhaustionSize exhaustionTensors exhaustion_nested f
  have hright := (tendsto_exhaustionEnergyRitz f).norm.pow 2
  have heq : (fun n => ‖exhaustionEnergyRitz f n‖ ^ 2) =
      ritzEnergySequence exhaustionSize exhaustionTensors f :=
    funext (exhaustionEnergyRitz_norm_sq f)
  rw [heq] at hright
  exact tendsto_nhds_unique hleft hright

/-- All three concrete Ritz limits are the three coordinates of the
actual completed-energy Riesz solution. The physical limit is exactly R f. -/
theorem exhaustion_ritz_limits_identified (f : HyperbolicL2) :
    Tendsto (ritzL2Sequence exhaustionSize exhaustionTensors f) atTop (𝓝 (actualWeakResolvent f)) ∧
      Tendsto (ritzGradientSequence false exhaustionSize exhaustionTensors f) atTop
        (𝓝 (completedGradient false (energyRieszSolution f))) ∧
      Tendsto (ritzGradientSequence true exhaustionSize exhaustionTensors f) atTop
        (𝓝 (completedGradient true (energyRieszSolution f))) := by
  have h := tendsto_exhaustionEnergyRitz f
  refine ⟨?_, ?_, ?_⟩
  · exact (physicalProjection.continuous.tendsto (energyRieszSolution f)).comp h
  · exact ((completedGradient false).continuous.tendsto (energyRieszSolution f)).comp h
  · exact ((completedGradient true).continuous.tendsto (energyRieszSolution f)).comp h

end

end ImbalancedChen.Part3.ActualExhaustionRitzResolventLimit20261025a
