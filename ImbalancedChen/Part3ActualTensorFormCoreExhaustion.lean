import ImbalancedChen.Part3CanonicalMaassTensorDensity
import ImbalancedChen.Part3ActualTensorGradientLinearMaps
import ImbalancedChen.Part3ActualFiniteTensorWeakResolvent
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
CODE_ONLY / SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.
A genuine countable nested finite-tensor exhaustion of the actual first-
gradient graph core. Countable points are chosen in the actual graph subtype
of H x (PlaneL2 x PlaneL2), not merely in H. Their actual finite tensor
presentations are accumulated by appendTensors. Thus every actual core test
can be approximated simultaneously in H and both true gradient norms.
-/

noncomputable section

namespace ImbalancedChen.Part3.ActualTensorFormCoreExhaustionSourceOnly

open MeasureTheory Set TopologicalSpace
open MaassWeakOperatorCore20261024zz MaassFiniteCoreL2Graph20261025a
open MaassFiniteCoreL2LinearOperator20261025a MaassFirstGradientWeakLimit20261025a
open ActualTensorGradientLinearMaps20261025a CanonicalMaassTensorDensity20261025a
open ActualFiniteTensorWeakResolvent20261025a

local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

/-- Native product topology is the actual topology of simultaneous L2 and
first-gradient convergence. -/
abbrev GradientTriple := HyperbolicL2 × (PlaneL2 × PlaneL2)

def coreGraphMap (u : actualTensorDomain) : GradientTriple :=
  ((u : HyperbolicL2), (actualGradient false u, actualGradient true u))

def coreGradientGraph : Set GradientTriple := Set.range coreGraphMap

instance : Nonempty coreGradientGraph :=
  ⟨⟨coreGraphMap 0, ⟨0, rfl⟩⟩⟩

/-- This is native Lp second countability from the actual countably
 generated Borel spaces and s-finite canonical/planar measures. -/
theorem gradientTriple_secondCountable : SecondCountableTopology GradientTriple := by
  infer_instance

/-- Dense sequence in the actual graph subtype, with its inherited product
metric. No graph-density or exhaustion supplier is assumed. -/
def graphSequence : ℕ → coreGradientGraph := denseSeq coreGradientGraph

def coreSequence (n : ℕ) : actualTensorDomain :=
  Classical.choose (graphSequence n).property

theorem coreSequence_graph (n : ℕ) :
    coreGraphMap (coreSequence n) = (graphSequence n : GradientTriple) :=
  Classical.choose_spec (graphSequence n).property

/-- Simultaneous approximation of an actual core vector and its two actual
first derivatives follows from density in the graph subtype. -/
theorem exists_coreSequence_form_near (u : actualTensorDomain) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ‖(coreSequence n : HyperbolicL2) - (u : HyperbolicL2)‖ < ε ∧
      ‖actualGradient false (coreSequence n) - actualGradient false u‖ < ε ∧
      ‖actualGradient true (coreSequence n) - actualGradient true u‖ < ε := by
  obtain ⟨n, hn⟩ := (denseRange_denseSeq coreGradientGraph).exists_dist_lt
    (⟨coreGraphMap u, ⟨u, rfl⟩⟩ : coreGradientGraph) hε
  change dist (coreGraphMap u) (graphSequence n : GradientTriple) < ε at hn
  rw [← coreSequence_graph n] at hn
  have hh : dist (u : HyperbolicL2) (coreSequence n : HyperbolicL2) < ε ∧
      dist (actualGradient false u) (actualGradient false (coreSequence n)) < ε ∧
      dist (actualGradient true u) (actualGradient true (coreSequence n)) < ε := by
    simpa only [coreGraphMap, Prod.dist_eq, max_lt_iff] using hn
  refine ⟨n, ?_, ?_, ?_⟩
  · simpa only [dist_eq_norm, norm_sub_rev] using hh.1
  · simpa only [dist_eq_norm, norm_sub_rev] using hh.2.1
  · simpa only [dist_eq_norm, norm_sub_rev] using hh.2.2

private theorem coreSequence_has_representation (n : ℕ) :
    ∃ k : ℕ, ∃ T : Fin k → CompactTensor,
      (coreSequence n : HyperbolicL2) = finiteCoreL2 Finset.univ T := by
  rcases (coreSequence n).property with ⟨g, k, T, hf, hg⟩
  exact ⟨k, T, hf⟩

def blockSize (n : ℕ) : ℕ := Classical.choose (coreSequence_has_representation n)

def blockTensors (n : ℕ) : Fin (blockSize n) → CompactTensor :=
  Classical.choose (Classical.choose_spec (coreSequence_has_representation n))

theorem coreSequence_representation (n : ℕ) :
    (coreSequence n : HyperbolicL2) = finiteCoreL2 Finset.univ (blockTensors n) :=
  Classical.choose_spec (Classical.choose_spec (coreSequence_has_representation n))

/-- Literal cumulative append of the chosen actual finite tensor families. -/
def cumulativeFamily : ℕ → Σ k : ℕ, Fin k → CompactTensor
  | 0 => ⟨0, Fin.elim0⟩
  | n + 1 => ⟨(cumulativeFamily n).1 + blockSize n,
      appendTensors (cumulativeFamily n).2 (blockTensors n)⟩

def exhaustionSize (n : ℕ) : ℕ := (cumulativeFamily n).1

def exhaustionTensors (n : ℕ) : Fin (exhaustionSize n) → CompactTensor :=
  (cumulativeFamily n).2

/-- These are exactly the existing actual finite tensor trial spans. -/
def trialSpace (n : ℕ) : Submodule ℂ HyperbolicL2 :=
  actualFiniteTensorSpan (exhaustionSize n) (exhaustionTensors n)

instance trialSpace_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (trialSpace n) :=
  actualFiniteTensorSpan_finiteDimensional _ _

theorem trialSpace_le_domain (n : ℕ) : trialSpace n ≤ actualTensorDomain :=
  actualFiniteTensorSpan_le_domain _ _

private theorem finiteCoreL2_singleton_congr {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) (i : Fin n) (j : Fin m)
    (h : T i = U j) : finiteCoreL2 {i} T = finiteCoreL2 {j} U := by
  classical
  unfold finiteCoreL2
  apply MemLp.toLp_congr
  exact Filter.Eventually.of_forall fun z => by simp [finiteCoreFunction, h]

private theorem actualSpan_append_left {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    actualFiniteTensorSpan n T ≤ actualFiniteTensorSpan (n + m) (appendTensors T U) := by
  apply Submodule.span_le.2
  rintro v ⟨i, rfl⟩
  have he := finiteCoreL2_singleton_congr T (appendTensors T U) i (Fin.castAdd m i)
    (by simp [appendTensors])
  rw [he]
  exact Submodule.subset_span (Set.mem_range_self (Fin.castAdd m i))

private theorem actualSpan_append_right {n m : ℕ}
    (T : Fin n → CompactTensor) (U : Fin m → CompactTensor) :
    actualFiniteTensorSpan m U ≤ actualFiniteTensorSpan (n + m) (appendTensors T U) := by
  apply Submodule.span_le.2
  rintro v ⟨j, rfl⟩
  have he := finiteCoreL2_singleton_congr U (appendTensors T U) j (Fin.natAdd n j)
    (by simp [appendTensors])
  rw [he]
  exact Submodule.subset_span (Set.mem_range_self (Fin.natAdd n j))

private theorem finiteCoreL2_sum_singletons {n : ℕ} (T : Fin n → CompactTensor) :
    finiteCoreL2 Finset.univ T = ∑ i : Fin n, finiteCoreL2 {i} T := by
  classical
  apply Lp.ext
  have hall : ∀ᵐ z ∂(volume : Measure UpperHalfPlane), ∀ i : Fin n,
      finiteCoreL2 {i} T z = finiteCoreFunction {i} T z :=
    ae_all_iff.2 (fun i => (finiteCoreFunction_memLp {i} T).coeFn_toLp)
  filter_upwards [(finiteCoreFunction_memLp Finset.univ T).coeFn_toLp,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin n => finiteCoreL2 {i} T), hall]
    with z hz hsum hallz
  rw [hz, hsum]
  simp only [finiteCoreFunction]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hallz i]
  simp only [finiteCoreFunction, Finset.sum_singleton]

private theorem finiteCoreL2_mem_actualSpan {n : ℕ} (T : Fin n → CompactTensor) :
    finiteCoreL2 Finset.univ T ∈ actualFiniteTensorSpan n T := by
  classical
  rw [finiteCoreL2_sum_singletons]
  exact Submodule.sum_mem _ (fun i _ => Submodule.subset_span (Set.mem_range_self i))

theorem trialSpace_le_succ (n : ℕ) : trialSpace n ≤ trialSpace (n + 1) :=
  actualSpan_append_left (exhaustionTensors n) (blockTensors n)

theorem trialSpace_monotone : Monotone trialSpace :=
  monotone_nat_of_le_succ trialSpace_le_succ

theorem coreSequence_mem_trialSpace (n : ℕ) :
    (coreSequence n : HyperbolicL2) ∈ trialSpace (n + 1) := by
  rw [coreSequence_representation]
  exact actualSpan_append_right (exhaustionTensors n) (blockTensors n)
    (finiteCoreL2_mem_actualSpan (blockTensors n))

/-- Concrete native first-gradient form-core approximation by one of the
nested actual finite tensor trial spaces. -/
theorem exists_trialSpace_form_approx (u : actualTensorDomain) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ v : actualTensorDomain, (v : HyperbolicL2) ∈ trialSpace n ∧
      ‖(v : HyperbolicL2) - (u : HyperbolicL2)‖ < ε ∧
      ‖actualGradient false v - actualGradient false u‖ < ε ∧
      ‖actualGradient true v - actualGradient true u‖ < ε := by
  obtain ⟨n, hH, hx, hy⟩ := exists_coreSequence_form_near u hε
  exact ⟨n + 1, coreSequence n, coreSequence_mem_trialSpace n, hH, hx, hy⟩

/-- Ambient H-density is a consequence of the stronger graph-core
approximation and the already proved actual canonical domain density. -/
theorem exists_trialSpace_H_approx (f : HyperbolicL2) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, ∃ v : HyperbolicL2, v ∈ trialSpace n ∧ ‖v - f‖ < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨u, hu, hfu⟩ := actualTensorDomain_dense.exists_dist_lt f hhalf
  obtain ⟨n, v, hv, hH, hx, hy⟩ :=
    exists_trialSpace_form_approx (⟨u, hu⟩ : actualTensorDomain) hhalf
  refine ⟨n, (v : HyperbolicL2), hv, ?_⟩
  have huf : ‖u - f‖ < ε / 2 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hfu
  calc
    ‖(v : HyperbolicL2) - f‖ ≤ ‖(v : HyperbolicL2) - u‖ + ‖u - f‖ := norm_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hH huf
    _ = ε := by ring

theorem trialSpace_union_dense : Dense (⋃ n : ℕ, (trialSpace n : Set HyperbolicL2)) := by
  intro f
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨n, v, hv, hnear⟩ := exists_trialSpace_H_approx f hε
  refine ⟨v, Set.mem_iUnion.2 ⟨n, hv⟩, ?_⟩
  simpa only [dist_eq_norm, norm_sub_rev] using hnear

/-- The actual triples arising from one finite trial space. -/
def trialGraph (n : ℕ) : Set GradientTriple :=
  {p | ∃ v : actualTensorDomain, (v : HyperbolicL2) ∈ trialSpace n ∧ p = coreGraphMap v}

theorem coreGraph_subset_closure_trialGraphUnion :
    coreGradientGraph ⊆ closure (⋃ n : ℕ, trialGraph n) := by
  rintro p ⟨u, rfl⟩
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨n, v, hv, hH, hx, hy⟩ := exists_trialSpace_form_approx u hε
  refine ⟨coreGraphMap v, Set.mem_iUnion.2 ⟨n, ⟨v, hv, rfl⟩⟩, ?_⟩
  have hh : dist (u : HyperbolicL2) (v : HyperbolicL2) < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hH
  have hxx : dist (actualGradient false u) (actualGradient false v) < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hx
  have hyy : dist (actualGradient true u) (actualGradient true v) < ε := by
    simpa only [dist_eq_norm, norm_sub_rev] using hy
  simpa only [coreGraphMap, Prod.dist_eq, max_lt_iff] using And.intro hh (And.intro hxx hyy)

/-- Genuine energy-graph core exhaustion, in the native product topology. -/
theorem closure_trialGraphUnion_eq_coreGraphClosure :
    closure (⋃ n : ℕ, trialGraph n) = closure coreGradientGraph := by
  apply le_antisymm
  · apply closure_mono
    rintro p hp
    rcases Set.mem_iUnion.1 hp with ⟨n, v, hv, rfl⟩
    exact ⟨v, rfl⟩
  · exact closure_minimal coreGraph_subset_closure_trialGraphUnion isClosed_closure

end ImbalancedChen.Part3.ActualTensorFormCoreExhaustionSourceOnly
