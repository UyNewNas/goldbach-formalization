import ImbalancedChen.Part3ActualTensorGradientLinearMaps
import ImbalancedChen.Part3ActualNestedTensorRitzL2Limit

/-!
The actual nested finite Ritz sequence is Cauchy simultaneously in canonical
hyperbolic L2 and in both actual planar gradient L2 spaces. Completeness
gives a triple limit, and the full squared triple error equals the actual
energy tail. No completed-domain gradient map or density claim is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualNestedTensorRitzGradientLimits20261025a

noncomputable section

open Filter Topology
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.MaassFiniteCoreL2LinearOperator20261025a
open ImbalancedChen.Part3.MaassFirstGradientWeakLimit20261025a
open ImbalancedChen.Part3.MaassGradientUpperSupportClosure20261025a
open ImbalancedChen.Part3.ActualFiniteTensorWeakResolvent20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzL2Limit20261025a
open ImbalancedChen.Part3.ActualTensorGradientLinearMaps20261025a

theorem actualGradient_norm_sq_le_energy (vertical : Bool) (u : actualTensorDomain) :
    ‖actualGradient vertical u‖ ^ 2 ≤ shiftedEnergy u := by
  have he := shiftedEnergy_eq_gradient_norms u
  cases vertical <;>
    nlinarith [sq_nonneg ‖(u : HyperbolicL2)‖,
      sq_nonneg ‖actualGradient false u‖, sq_nonneg ‖actualGradient true u‖]

def ritzGradientSequence (vertical : Bool) (r : ℕ → ℕ)
    (T : (k : ℕ) → Fin (r k) → CompactTensor) (f : HyperbolicL2) (k : ℕ) : PlaneL2 :=
  actualGradient vertical (ritzVector (r k) (T k) f)

theorem ritzGradientSequence_norm_le (vertical : Bool) (r : ℕ → ℕ)
    (T : (k : ℕ) → Fin (r k) → CompactTensor) (f : HyperbolicL2) (k : ℕ) :
    ‖ritzGradientSequence vertical r T f k‖ ≤ ‖f‖ := by
  have he := (actualGradient_norm_sq_le_energy vertical (ritzVector (r k) (T k) f)).trans
    (shiftedEnergy_ritz_le_forcing (r k) (T k) f)
  change ‖ritzGradientSequence vertical r T f k‖ ^ 2 ≤ ‖f‖ ^ 2 at he
  nlinarith [norm_nonneg (ritzGradientSequence vertical r T f k), norm_nonneg f]

theorem ritzGradientSequence_norm_sub_sq_le (vertical : Bool)
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2)
    (i j : ℕ) :
    ‖ritzGradientSequence vertical r T f j - ritzGradientSequence vertical r T f i‖ ^ 2 ≤
      |ritzEnergySequence r T f j - ritzEnergySequence r T f i| := by
  change ‖actualGradient vertical (ritzVector (r j) (T j) f) -
      actualGradient vertical (ritzVector (r i) (T i) f)‖ ^ 2 ≤ _
  rw [← map_sub, ← ritz_shiftedEnergy_error_eq_abs_increment r T hnext f i j]
  exact actualGradient_norm_sq_le_energy vertical _

/-- Each actual planar gradient sequence is Cauchy, derived from the
same scalar energy convergence as the actual input sequence. -/
theorem cauchySeq_ritzGradientSequence (vertical : Bool)
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    CauchySeq (ritzGradientSequence vertical r T f) := by
  have henergy := (tendsto_ritzEnergySequence r T hnext f).cauchySeq
  apply Metric.cauchySeq_iff'.2
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 henergy (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  refine ⟨N, ?_⟩
  intro k hk
  have hb := ritzGradientSequence_norm_sub_sq_le vertical r T hnext f N k
  have he : |ritzEnergySequence r T f k - ritzEnergySequence r T f N| < epsilon ^ 2 := by
    simpa only [Real.dist_eq] using hN k hk
  have hn : ‖ritzGradientSequence vertical r T f k -
      ritzGradientSequence vertical r T f N‖ < epsilon := by
    nlinarith [norm_nonneg (ritzGradientSequence vertical r T f k -
      ritzGradientSequence vertical r T f N)]
  simpa only [dist_eq_norm] using hn

theorem exists_ritzGradient_limit (vertical : Bool)
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    ∃ G : PlaneL2, Tendsto (ritzGradientSequence vertical r T f) atTop (𝓝 G) ∧
      ‖G‖ ≤ ‖f‖ ∧ G ∈ upperSupportedSubmodule := by
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_ritzGradientSequence vertical r T hnext f)
  refine ⟨G, hG, ?_, ?_⟩
  · exact le_of_tendsto' hG.norm (ritzGradientSequence_norm_le vertical r T f)
  · exact isClosed_upperSupportedSubmodule.mem_of_tendsto hG
      (Eventually.of_forall fun k => actualGradient_upperSupported vertical (ritzVector (r k) (T k) f))

/-- Before passing to any limit, the full input-plus-gradient error is
exactly the true finite energy increment on each ordered pair. -/
theorem ritz_triple_error_eq_energy_increment
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2)
    {i j : ℕ} (hij : i ≤ j) :
    ‖ritzL2Sequence r T f j - ritzL2Sequence r T f i‖ ^ 2 +
        ‖ritzGradientSequence false r T f j - ritzGradientSequence false r T f i‖ ^ 2 +
        ‖ritzGradientSequence true r T f j - ritzGradientSequence true r T f i‖ ^ 2 =
      ritzEnergySequence r T f j - ritzEnergySequence r T f i := by
  have he := shiftedEnergy_eq_gradient_norms
    (ritzVector (r j) (T j) f - ritzVector (r i) (T i) f)
  rw [map_sub, map_sub] at he
  change shiftedEnergy (ritzVector (r j) (T j) f - ritzVector (r i) (T i) f) =
    ‖ritzL2Sequence r T f j - ritzL2Sequence r T f i‖ ^ 2 +
      ‖ritzGradientSequence false r T f j - ritzGradientSequence false r T f i‖ ^ 2 +
      ‖ritzGradientSequence true r T f j - ritzGradientSequence true r T f i‖ ^ 2 at he
  have hp := nested_ritz_pythagoras (T i) (T j)
    (actualFiniteTensorSpan_sequence_mono r T hnext hij) f
  change ritzEnergySequence r T f j = ritzEnergySequence r T f i +
    shiftedEnergy (ritzVector (r j) (T j) f - ritzVector (r i) (T i) f) at hp
  linarith only [he, hp]

/-- Simultaneous actual input and gradient limits, with an exact energy
tail identity. This supplies a concrete form-completion triple without
claiming that its input limit belongs to the original finite core domain. -/
theorem exists_ritz_input_gradient_limits
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    ∃ (u : HyperbolicL2) (Gx Gy : PlaneL2),
      Tendsto (ritzL2Sequence r T f) atTop (𝓝 u) ∧
      Tendsto (ritzGradientSequence false r T f) atTop (𝓝 Gx) ∧
      Tendsto (ritzGradientSequence true r T f) atTop (𝓝 Gy) ∧
      ‖u‖ ≤ ‖f‖ ∧ ‖Gx‖ ≤ ‖f‖ ∧ ‖Gy‖ ≤ ‖f‖ ∧
      Gx ∈ upperSupportedSubmodule ∧ Gy ∈ upperSupportedSubmodule ∧
      ∀ k, ‖u - ritzL2Sequence r T f k‖ ^ 2 +
          ‖Gx - ritzGradientSequence false r T f k‖ ^ 2 +
          ‖Gy - ritzGradientSequence true r T f k‖ ^ 2 =
        ritzEnergySup r T f - ritzEnergySequence r T f k := by
  obtain ⟨u, hu, _⟩ := existsUnique_ritzL2_limit r T hnext f
  obtain ⟨Gx, hx, hnx, hsx⟩ := exists_ritzGradient_limit false r T hnext f
  obtain ⟨Gy, hy, hny, hsy⟩ := exists_ritzGradient_limit true r T hnext f
  refine ⟨u, Gx, Gy, hu.1, hx, hy, hu.2.1, hnx, hny, hsx, hsy, ?_⟩
  intro k
  have hl0 : Tendsto (fun j => ‖ritzL2Sequence r T f j - ritzL2Sequence r T f k‖ ^ 2)
      atTop (𝓝 (‖u - ritzL2Sequence r T f k‖ ^ 2)) :=
    (hu.1.sub tendsto_const_nhds).norm.pow 2
  have hlx : Tendsto (fun j => ‖ritzGradientSequence false r T f j -
      ritzGradientSequence false r T f k‖ ^ 2)
      atTop (𝓝 (‖Gx - ritzGradientSequence false r T f k‖ ^ 2)) :=
    (hx.sub tendsto_const_nhds).norm.pow 2
  have hly : Tendsto (fun j => ‖ritzGradientSequence true r T f j -
      ritzGradientSequence true r T f k‖ ^ 2)
      atTop (𝓝 (‖Gy - ritzGradientSequence true r T f k‖ ^ 2)) :=
    (hy.sub tendsto_const_nhds).norm.pow 2
  have hsum := (hl0.add hlx).add hly
  have hr := (tendsto_ritzEnergySequence r T hnext f).sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ritzEnergySequence r T f k)
      atTop (𝓝 (ritzEnergySequence r T f k)))
  have heq : (fun j => ‖ritzL2Sequence r T f j - ritzL2Sequence r T f k‖ ^ 2 +
      ‖ritzGradientSequence false r T f j - ritzGradientSequence false r T f k‖ ^ 2 +
      ‖ritzGradientSequence true r T f j - ritzGradientSequence true r T f k‖ ^ 2) =ᶠ[atTop]
      (fun j => ritzEnergySequence r T f j - ritzEnergySequence r T f k) := by
    filter_upwards [eventually_ge_atTop k] with j hj
    exact ritz_triple_error_eq_energy_increment r T hnext f hj
  exact tendsto_nhds_unique hsum (hr.congr' heq.symm)

end

end ImbalancedChen.Part3.ActualNestedTensorRitzGradientLimits20261025a
