import ImbalancedChen.Part3ActualNestedTensorRitzEnergy
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.MonotoneConvergence

/-!
Actual hyperbolic L2 convergence of nested finite tensor Ritz solutions.

The actual weak resolver supplies every trial vector. Its shifted energies
are monotone and bounded by the ambient forcing norm squared. The proved
energy increment controls each physical L2 difference, hence gives Cauchy
and a unique L2 limit with a quantitative energy-tail error estimate.
No convergence, dense exhaustion or infinite-dimensional weak resolvent
is assumed. No limit of actual Laplacians or plane gradients is asserted.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen.Part3.ActualNestedTensorRitzL2Limit20261025a

noncomputable section

open Filter Topology
open ImbalancedChen.Part3.MaassWeakOperatorCore20261024zz
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualFiniteTensorWeakResolvent20261025a
open ImbalancedChen.Part3.ActualNestedTensorRitzEnergy20261025a

/-- Varying finite families, viewed in the actual canonical L2 space. -/
def ritzL2Sequence (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (f : HyperbolicL2) (k : ℕ) : HyperbolicL2 :=
  ritzVector (r k) (T k) f

def ritzEnergySequence (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (f : HyperbolicL2) (k : ℕ) : ℝ :=
  shiftedEnergy (ritzVector (r k) (T k) f)

def ritzEnergySup (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (f : HyperbolicL2) : ℝ := ⨆ k, ritzEnergySequence r T f k

/-- Adjacent inclusion gives all ordered inclusions of the actual spans. -/
theorem actualFiniteTensorSpan_sequence_mono
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) :
    Monotone (fun k => actualFiniteTensorSpan (r k) (T k)) :=
  monotone_nat_of_le_succ hnext

theorem ritzEnergySequence_mono
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    Monotone (ritzEnergySequence r T f) := by
  intro i j hij
  exact nested_ritz_energy_mono (T i) (T j)
    (actualFiniteTensorSpan_sequence_mono r T hnext hij) f

theorem ritzEnergySequence_bddAbove
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor) (f : HyperbolicL2) :
    BddAbove (Set.range (ritzEnergySequence r T f)) := by
  refine ⟨‖f‖ ^ 2, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact shiftedEnergy_ritz_le_forcing (r k) (T k) f

theorem ritzEnergySup_bounds
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor) (f : HyperbolicL2) :
    0 ≤ ritzEnergySup r T f ∧ ritzEnergySup r T f ≤ ‖f‖ ^ 2 := by
  constructor
  · exact (shiftedEnergy_nonneg (ritzVector (r 0) (T 0) f)).trans
      (le_ciSup (ritzEnergySequence_bddAbove r T f) 0)
  · exact ciSup_le fun k => shiftedEnergy_ritz_le_forcing (r k) (T k) f

/-- Energy convergence is proved by actual monotonicity and the uniform
forcing bound; its limit is the real supremum of these trial energies. -/
theorem tendsto_ritzEnergySequence
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    Tendsto (ritzEnergySequence r T f) atTop (𝓝 (ritzEnergySup r T f)) :=
  tendsto_atTop_ciSup (ritzEnergySequence_mono r T hnext f)
    (ritzEnergySequence_bddAbove r T f)

/-- Every actual ordered pair has its squared L2 distance paid by the
same signed energy increment, with no independently supplied error bound. -/
theorem ritzL2Sequence_norm_sub_sq_le
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2)
    {i j : ℕ} (hij : i ≤ j) :
    ‖ritzL2Sequence r T f j - ritzL2Sequence r T f i‖ ^ 2 ≤
      ritzEnergySequence r T f j - ritzEnergySequence r T f i :=
  nested_ritz_L2_error_le_energy_increment (T i) (T j)
    (actualFiniteTensorSpan_sequence_mono r T hnext hij) f

/-- The actual shifted form error equals the absolute scalar energy
increment for either ordering of the two finite trials. -/
theorem ritz_shiftedEnergy_error_eq_abs_increment
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2)
    (i j : ℕ) :
    shiftedEnergy (ritzVector (r j) (T j) f - ritzVector (r i) (T i) f) =
      |ritzEnergySequence r T f j - ritzEnergySequence r T f i| := by
  rcases le_total i j with hij | hji
  · have hp := nested_ritz_pythagoras (T i) (T j)
      (actualFiniteTensorSpan_sequence_mono r T hnext hij) f
    have hm := ritzEnergySequence_mono r T hnext f hij
    rw [abs_of_nonneg (sub_nonneg.mpr hm)]
    change shiftedEnergy (ritzVector (r j) (T j) f - ritzVector (r i) (T i) f) =
      shiftedEnergy (ritzVector (r j) (T j) f) - shiftedEnergy (ritzVector (r i) (T i) f)
    linarith only [hp]
  · have hp := nested_ritz_pythagoras (T j) (T i)
      (actualFiniteTensorSpan_sequence_mono r T hnext hji) f
    have hm := ritzEnergySequence_mono r T hnext f hji
    have hs : shiftedEnergy (ritzVector (r j) (T j) f - ritzVector (r i) (T i) f) =
        shiftedEnergy (ritzVector (r i) (T i) f - ritzVector (r j) (T j) f) := by
      rw [shiftedEnergy_sub, shiftedEnergy_sub,
        shiftedDirichlet_symm (ritzVector (r j) (T j) f) (ritzVector (r i) (T i) f)]
      ring
    rw [hs, abs_of_nonpos (sub_nonpos.mpr hm)]
    change shiftedEnergy (ritzVector (r i) (T i) f - ritzVector (r j) (T j) f) =
      -(shiftedEnergy (ritzVector (r j) (T j) f) - shiftedEnergy (ritzVector (r i) (T i) f))
    linarith only [hp]

/-- The actual shifted Dirichlet form differences are Cauchy as well.
This is stated on actual finite vectors without inventing a completed
gradient domain or asserting a representation of the L2 limit. -/
theorem ritz_shiftedEnergy_cauchy
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    ∀ epsilon > 0, ∃ N, ∀ i ≥ N, ∀ j ≥ N,
      shiftedEnergy (ritzVector (r i) (T i) f - ritzVector (r j) (T j) f) < epsilon := by
  intro epsilon hepsilon
  have henergy := (tendsto_ritzEnergySequence r T hnext f).cauchySeq
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 henergy epsilon hepsilon
  refine ⟨N, ?_⟩
  intro i hi j hj
  rw [ritz_shiftedEnergy_error_eq_abs_increment r T hnext f j i]
  simpa only [Real.dist_eq] using hN i hi j hj

/-- Energy Cauchy and actual coercive increments force the physical
canonical L2 sequence to be Cauchy. This does not assume convergence. -/
theorem cauchySeq_ritzL2Sequence
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    CauchySeq (ritzL2Sequence r T f) := by
  have henergy := (tendsto_ritzEnergySequence r T hnext f).cauchySeq
  apply Metric.cauchySeq_iff'.2
  intro epsilon hepsilon
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 henergy (epsilon ^ 2) (sq_pos_of_pos hepsilon)
  refine ⟨N, ?_⟩
  intro k hk
  have hinc := ritzL2Sequence_norm_sub_sq_le r T hnext f hk
  have hnear : |ritzEnergySequence r T f k - ritzEnergySequence r T f N| < epsilon ^ 2 := by
    simpa only [Real.dist_eq] using hN k hk
  have hsmall : ritzEnergySequence r T f k - ritzEnergySequence r T f N < epsilon ^ 2 :=
    (le_abs_self _).trans_lt hnear
  have hn : ‖ritzL2Sequence r T f k - ritzL2Sequence r T f N‖ < epsilon := by
    nlinarith [norm_nonneg (ritzL2Sequence r T f k - ritzL2Sequence r T f N)]
  simpa only [dist_eq_norm] using hn

/-- The actual L2 limit has the same forcing norm bound, and each
finite trial has a quantified squared error controlled by its energy tail.
Uniqueness follows in canonical L2 without a dense-union assumption. -/
theorem existsUnique_ritzL2_limit
    (r : ℕ → ℕ) (T : (k : ℕ) → Fin (r k) → CompactTensor)
    (hnext : ∀ k, actualFiniteTensorSpan (r k) (T k) ≤
      actualFiniteTensorSpan (r (k + 1)) (T (k + 1))) (f : HyperbolicL2) :
    ∃! u : HyperbolicL2,
      Tendsto (ritzL2Sequence r T f) atTop (𝓝 u) ∧ ‖u‖ ≤ ‖f‖ ∧
        ∀ k, ‖u - ritzL2Sequence r T f k‖ ^ 2 ≤
          ritzEnergySup r T f - ritzEnergySequence r T f k := by
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete (cauchySeq_ritzL2Sequence r T hnext f)
  have hnorm : ‖u‖ ≤ ‖f‖ :=
    le_of_tendsto' hu.norm (fun k => ritzSolution_norm_le (r k) (T k) f)
  have herr (k : ℕ) : ‖u - ritzL2Sequence r T f k‖ ^ 2 ≤
      ritzEnergySup r T f - ritzEnergySequence r T f k := by
    have hleft : Tendsto (fun j => ‖ritzL2Sequence r T f j - ritzL2Sequence r T f k‖ ^ 2)
        atTop (𝓝 (‖u - ritzL2Sequence r T f k‖ ^ 2)) :=
      (hu.sub tendsto_const_nhds).norm.pow 2
    have hright : Tendsto (fun j => ritzEnergySequence r T f j - ritzEnergySequence r T f k)
        atTop (𝓝 (ritzEnergySup r T f - ritzEnergySequence r T f k)) :=
      (tendsto_ritzEnergySequence r T hnext f).sub tendsto_const_nhds
    apply le_of_tendsto_of_tendsto hleft hright
    filter_upwards [eventually_ge_atTop k] with j hj
    exact ritzL2Sequence_norm_sub_sq_le r T hnext f hj
  refine ⟨u, ⟨hu, hnorm, herr⟩, ?_⟩
  intro v hv
  exact tendsto_nhds_unique hv.1 hu

end

end ImbalancedChen.Part3.ActualNestedTensorRitzL2Limit20261025a
