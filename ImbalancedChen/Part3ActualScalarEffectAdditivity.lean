import ImbalancedChen.Part3ActualScalarPositiveOperator
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Lattice.Nat

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Finite additivity, monotonicity and strong countable additivity for the actual
positive effects. The tail bound is obtained from actual mixed-coefficient
Cauchy--Schwarz and scalar mass domination, without idempotence. The native
finite-measure tail theorem then supplies strong convergence for disjoint
measurable sequences. This is the positive-operator-valued-measure layer;
projection-valued multiplication and idempotence remain separate obligations.
-/

namespace ImbalancedChen.Part3.ActualScalarEffectAdditivity20261025a

noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
open ImbalancedChen.Part3.MaassFiniteCoreL2Graph20261025a
open ImbalancedChen.Part3.ActualResolventScalarMeasure20261025a
open ImbalancedChen.Part3.ActualScalarMeasureQuadratic20261025a
open ImbalancedChen.Part3.ActualScalarPositiveOperator20261025a

theorem operator_eq_of_diagonal (S T : HyperbolicL2 →L[ℂ] HyperbolicL2)
    (h : ∀ f, inner ℂ (S f) f = inner ℂ (T f) f) : S = T := by
  have hl := (ext_inner_map S.toLinearMap T.toLinearMap).mp h
  ext f
  exact congrArg (fun A : HyperbolicL2 →ₗ[ℂ] HyperbolicL2 => A f) hl

theorem spectralEffect_empty : spectralEffect (∅ : Set ResolventSpectrum) = 0 := by
  apply operator_eq_of_diagonal
  intro f
  simp only [spectralEffect_diagonal, spectralQuadratic, measureReal_empty,
    Complex.ofReal_zero, ContinuousLinearMap.zero_apply, inner_zero_left]

theorem spectralEffect_univ : spectralEffect (Set.univ : Set ResolventSpectrum) = 1 := by
  apply operator_eq_of_diagonal
  intro f
  rw [spectralEffect_diagonal, spectralQuadratic_univ]
  change ((‖f‖ ^ 2 : ℝ) : ℂ) = inner ℂ f f
  rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]

theorem spectralEffect_union {B C : Set ResolventSpectrum}
    (hd : Disjoint B C) (hC : MeasurableSet C) :
    spectralEffect (B ∪ C) = spectralEffect B + spectralEffect C := by
  apply operator_eq_of_diagonal
  intro f
  rw [ContinuousLinearMap.add_apply, inner_add_left,
    spectralEffect_diagonal, spectralEffect_diagonal, spectralEffect_diagonal]
  change (((scalarMeasure f).real (B ∪ C) : ℝ) : ℂ) =
    ((scalarMeasure f).real B : ℂ) + ((scalarMeasure f).real C : ℂ)
  rw [measureReal_union hd hC, Complex.ofReal_add]

theorem spectralEffect_mono {B C : Set ResolventSpectrum} (hBC : B ⊆ C) :
    spectralEffect B ≤ spectralEffect C := by
  apply (ContinuousLinearMap.le_def _ _).mpr
  refine ⟨(spectralEffect_symmetric C).sub (spectralEffect_symmetric B), ?_⟩
  intro f
  change 0 ≤ (inner ℂ ((spectralEffect C - spectralEffect B) f) f).re
  rw [ContinuousLinearMap.sub_apply, inner_sub_left, Complex.sub_re,
    spectralEffect_diagonal, spectralEffect_diagonal, Complex.ofReal_re, Complex.ofReal_re]
  exact sub_nonneg.mpr (spectralQuadratic_mono hBC f)

theorem spectralEffect_le_one (B : Set ResolventSpectrum) : spectralEffect B ≤ 1 := by
  rw [← spectralEffect_univ]
  exact spectralEffect_mono (Set.subset_univ B)

/-- The key tail estimate is valid for positive effects; it does not use
E_B squared equals E_B, or any projection identity. -/
theorem spectralEffect_norm_sq_le_mass (B : Set ResolventSpectrum) (f : HyperbolicL2) :
    ‖spectralEffect B f‖ ^ 2 ≤ spectralQuadratic B f := by
  have hc : cross B f (spectralEffect B f) = ((‖spectralEffect B f‖ ^ 2 : ℝ) : ℂ) := by
    rw [← spectralEffect_inner, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  have hn : ‖cross B f (spectralEffect B f)‖ = ‖spectralEffect B f‖ ^ 2 := by
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := cross_norm_sq_le B f (spectralEffect B f)
  rw [hn] at h
  have hp := mul_le_mul_of_nonneg_left
    (spectralQuadratic_le_norm_sq B (spectralEffect B f)) (spectralQuadratic_nonneg B f)
  by_cases hz : ‖spectralEffect B f‖ ^ 2 = 0
  · rw [hz]
    exact spectralQuadratic_nonneg B f
  · have hpos : 0 < ‖spectralEffect B f‖ ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_right hpos).mp
    nlinarith only [h, hp]

theorem spectralEffect_norm_le_sqrt_mass (B : Set ResolventSpectrum) (f : HyperbolicL2) :
    ‖spectralEffect B f‖ ≤ Real.sqrt (spectralQuadratic B f) :=
  Real.le_sqrt_of_sq_le (spectralEffect_norm_sq_le_mass B f)

def prefixSet (S : ℕ → Set ResolventSpectrum) (n : ℕ) : Set ResolventSpectrum :=
  ⋃ i < n, S i

def tailSet (S : ℕ → Set ResolventSpectrum) (n : ℕ) : Set ResolventSpectrum :=
  ⋃ i ≥ n, S i

theorem prefixSet_succ (S : ℕ → Set ResolventSpectrum) (n : ℕ) :
    prefixSet S (n + 1) = prefixSet S n ∪ S n := Set.biUnion_lt_succ S n

theorem prefixSet_measurable (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) : MeasurableSet (prefixSet S n) :=
  MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hS i))

theorem tailSet_measurable (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i)) (n : ℕ) : MeasurableSet (tailSet S n) :=
  MeasurableSet.iUnion (fun i => MeasurableSet.iUnion (fun _ => hS i))

theorem prefixSet_disjoint_next (S : ℕ → Set ResolventSpectrum)
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    Disjoint (prefixSet S n) (S n) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [prefixSet, mem_iUnion, exists_prop] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact Set.disjoint_left.mp (hd (by omega : i ≠ n)) hxi hy

theorem prefixSet_disjoint_tail (S : ℕ → Set ResolventSpectrum)
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    Disjoint (prefixSet S n) (tailSet S n) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  simp only [prefixSet, mem_iUnion, exists_prop] at hx
  simp only [tailSet, mem_iUnion, exists_prop] at hy
  obtain ⟨i, hi, hxi⟩ := hx
  obtain ⟨j, hj, hxj⟩ := hy
  exact Set.disjoint_left.mp (hd (by omega : i ≠ j)) hxi hxj

theorem prefixSet_union_tail (S : ℕ → Set ResolventSpectrum) (n : ℕ) :
    prefixSet S n ∪ tailSet S n = ⋃ i, S i := by
  ext x
  simp only [prefixSet, tailSet, mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (⟨i, _, hi⟩ | ⟨i, _, hi⟩) <;> exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    by_cases hin : i < n
    · exact Or.inl ⟨i, hin, hi⟩
    · exact Or.inr ⟨i, by omega, hi⟩

theorem spectralEffect_prefix (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (n : ℕ) :
    spectralEffect (prefixSet S n) = ∑ i ∈ Finset.range n, spectralEffect (S i) := by
  induction n with
  | zero => simp [prefixSet, spectralEffect_empty]
  | succ n ih =>
    rw [prefixSet_succ, spectralEffect_union (prefixSet_disjoint_next S hd n) (hS n),
      ih, Finset.sum_range_succ]

theorem tendsto_tail_mass (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (f : HyperbolicL2) :
    Tendsto (fun n => spectralQuadratic (tailSet S n) f) atTop (𝓝 0) := by
  have h := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (μ := scalarMeasure f) (fun i => (hS i).nullMeasurableSet) hd
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa only [spectralQuadratic, Measure.real, tailSet, Function.comp_apply,
    ENNReal.toReal_zero] using ht

/-- The actual tail effect tends strongly to zero. -/
theorem tendsto_tail_effect (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (f : HyperbolicL2) :
    Tendsto (fun n => spectralEffect (tailSet S n) f) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => spectralEffect_norm_le_sqrt_mass (tailSet S n) f)
  have h := (Real.continuous_sqrt.tendsto 0).comp (tendsto_tail_mass S hS hd f)
  simpa only [Real.sqrt_zero] using h

/-- Strong convergence of the disjoint finite union effects to the full
union effect, with no projection-valued premise. -/
theorem tendsto_prefix_effect (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (f : HyperbolicL2) :
    Tendsto (fun n => spectralEffect (prefixSet S n) f) atTop
      (𝓝 (spectralEffect (⋃ i, S i) f)) := by
  have heq (n : ℕ) : spectralEffect (prefixSet S n) f =
      spectralEffect (⋃ i, S i) f - spectralEffect (tailSet S n) f := by
    have h := spectralEffect_union (prefixSet_disjoint_tail S hd n)
      (tailSet_measurable S hS n)
    rw [prefixSet_union_tail] at h
    have hf := congrArg (fun A : HyperbolicL2 →L[ℂ] HyperbolicL2 => A f) h
    simp only [ContinuousLinearMap.add_apply] at hf
    exact (eq_sub_iff_add_eq).mpr hf.symm
  have hfun : (fun n => spectralEffect (prefixSet S n) f) =
      (fun n => spectralEffect (⋃ i, S i) f - spectralEffect (tailSet S n) f) := funext heq
  rw [hfun]
  simpa only [sub_zero] using
    (tendsto_const_nhds.sub (tendsto_tail_effect S hS hd f))

/-- Countable additivity in the strong operator sense, stated at every
actual vector and with the literal finite operator sum. -/
theorem tendsto_sum_effects (S : ℕ → Set ResolventSpectrum)
    (hS : ∀ i, MeasurableSet (S i))
    (hd : Pairwise fun i j => Disjoint (S i) (S j)) (f : HyperbolicL2) :
    Tendsto (fun n => (∑ i ∈ Finset.range n, spectralEffect (S i)) f) atTop
      (𝓝 (spectralEffect (⋃ i, S i) f)) := by
  simpa only [spectralEffect_prefix S hS hd] using tendsto_prefix_effect S hS hd f

end
end ImbalancedChen.Part3.ActualScalarEffectAdditivity20261025a
