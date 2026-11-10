import ImbalancedChen.P2Winner9ActualEightSimplexMoment
import ImbalancedChen.P2Winner9MixedDegreeOnePolynomialMoment
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

This is the first actual-measure part of the k=1 mixed identity (M).
It converts the genuine canonical Δ8 monomial law into nine-barycentric
Dirichlet moments, without assuming M or any final moment formula.
The signed fourth-degree expansion and equality to the Phase14 integer
mixedNumerator remain explicit open steps, recorded in the registry.
Both manuscript-specific imports are held uncompiled source.
-/

namespace ImbalancedChen.P2Winner9BarycentricMixedDegreeOne

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9SimplexCoordinateSlice
open ImbalancedChen.P2Winner9ActualEightSimplexMoment
open ImbalancedChen.P2Winner9NestedEightSimplexMoment
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly

def barycentric (i : Fin 9) (x : Fin 8 → ℝ) : ℝ :=
  Fin.cases (1 - ∑ j : Fin 8, x j) (fun j => x j) i

def affine (v : Fin 9 → ℝ) (x : Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 9, v i * barycentric i x

theorem barycentric_continuous (i : Fin 9) : Continuous (barycentric i) := by
  fin_cases i <;> simp [barycentric] <;> fun_prop

theorem affine_continuous (v : Fin 9 → ℝ) : Continuous (affine v) := by
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul (barycentric_continuous i)

def barycentricMoment (e : Fin 9 → Nat) : ℝ :=
  ∫ x in standardSimplex 8 (1 : ℝ),
    ∏ i : Fin 9, (barycentric i x)^(e i)

/-- The actual nine-barycentric Dirichlet monomial integral, using the
PhaseB genuine set-integral theorem. There is no moment-law premise. -/
theorem barycentricMoment_eq (e : Fin 9 → Nat) :
    barycentricMoment e =
      (((e 0).factorial *
          factorialProduct (List.ofFn (fun i : Fin 8 => e i.succ)) : Nat) : ℝ) /
        (((e 0) + (List.ofFn (fun i : Fin 8 => e i.succ)).sum + 8).factorial : ℝ) := by
  have hfun (x : Fin 8 → ℝ) :
      (∏ i : Fin 9, (barycentric i x)^(e i)) =
        (1 - ∑ i : Fin 8, x i)^(e 0) *
          (∏ i : Fin 8, (x i)^(e i.succ)) := by
    simp [Fin.prod_univ_succ, barycentric]
  have h : barycentricMoment e =
      ImbalancedChen.P2Winner9NestedEightSimplexMoment.actualMoment
        (e 0) (fun i : Fin 8 => e i.succ) 1 := by
    unfold barycentricMoment
    rw [standardSimplex_eight]
    apply setIntegral_congr_fun
      (isClosed_standardSimplex (1 : ℝ)).measurableSet
    intro x _
    exact hfun x
  rw [h, actual_eight_factorial (e 0)
    (fun i : Fin 8 => e i.succ) (by norm_num)]
  simp

def unitExponent (i : Fin 9) (r : Fin 9) : Nat :=
  if r = i then 1 else 0

private theorem prod_unit (i : Fin 9) (x : Fin 8 → ℝ) :
    (∏ r : Fin 9, (barycentric r x)^(unitExponent i r)) =
      barycentric i x := by
  classical
  calc
    _ = ∏ r : Fin 9, if r = i then barycentric r x else 1 := by
      apply Finset.prod_congr rfl
      intro r _
      by_cases h : r = i <;> simp [unitExponent, h]
    _ = _ := by simp

theorem barycentric_first (i : Fin 9) :
    (∫ x in standardSimplex 8 (1 : ℝ), barycentric i x) =
      barycentricMoment (unitExponent i) := by
  unfold barycentricMoment
  apply setIntegral_congr_fun
    (isClosed_standardSimplex (1 : ℝ)).measurableSet
  intro x _
  exact (prod_unit i x).symm

theorem barycentric_first_value (i : Fin 9) :
    (∫ x in standardSimplex 8 (1 : ℝ), barycentric i x) =
      1 / (9.factorial : ℝ) := by
  rw [barycentric_first, barycentricMoment_eq]
  fin_cases i <;>
    norm_num [unitExponent, factorialProduct, List.ofFn]

def fourExponent (i k j l : Fin 9) (r : Fin 9) : Nat :=
  unitExponent i r + unitExponent k r +
    unitExponent j r + unitExponent l r

/-- The signed fourth-degree integrand is literally a barycentric
monomial. Its integral is evaluable by `barycentricMoment_eq`. -/
theorem barycentric_four (i k j l : Fin 9) :
    (∫ x in standardSimplex 8 (1 : ℝ),
      barycentric i x * barycentric k x *
        barycentric j x * barycentric l x) =
      barycentricMoment (fourExponent i k j l) := by
  unfold barycentricMoment
  apply setIntegral_congr_fun
    (isClosed_standardSimplex (1 : ℝ)).measurableSet
  intro x _
  simp only [fourExponent, pow_add, Finset.prod_mul_distrib,
    prod_unit]

def gapVertices (d : SimplexData) : Fin 9 → ℝ :=
  fun i => d.gaps i

def yVertices (d : SimplexData) : Fin 9 → ℝ :=
  fun i => (d.y i : ℝ) / d.U

def bVertices (d : SimplexData) (j : Fin 10) : Fin 9 → ℝ :=
  fun i => (d.deviations j i : ℝ) / d.L

def actualGapMass (d : SimplexData) : ℝ :=
  ∫ x in standardSimplex 8 (1 : ℝ), affine (gapVertices d) x

def actualMixedNumerator (d : SimplexData) (j : Fin 10) : ℝ :=
  ∫ x in standardSimplex 8 (1 : ℝ),
    affine (gapVertices d) x * affine (yVertices d) x *
      (affine (bVertices d j) x)^2

def actualMixedExpectation (d : SimplexData) (j : Fin 10) : ℝ :=
  actualMixedNumerator d j / actualGapMass d

/-- The actual gap measure is the claimed Dirichlet-mixture normalizer.
This uses nine genuine first barycentric set integrals. -/
theorem actualGapMass_eq (d : SimplexData) :
    actualGapMass d = (gapTotal d.gaps : ℝ) / (9.factorial : ℝ) := by
  have hi (i : Fin 9) : IntegrableOn
      (fun x : Fin 8 → ℝ => gapVertices d i * barycentric i x)
      (standardSimplex 8 (1 : ℝ)) := by
    exact (continuous_const.mul (barycentric_continuous i)).continuousOn.integrableOn_compact
      (isCompact_standardSimplex (by norm_num))
  unfold actualGapMass affine
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const_mul, barycentric_first_value]
  rw [← Finset.sum_mul]
  simp [gapVertices, gapTotal, Nat.cast_sum, div_eq_mul_inv]

theorem actualGapMass_pos (d : SimplexData) : 0 < actualGapMass d := by
  rw [actualGapMass_eq]
  have hG : (0 : ℝ) < (gapTotal d.gaps : ℝ) := by exact_mod_cast d.gapsPos
  positivity

/-- The pointwise fourfold expansion preserves the signed deviations.
It is the exact polynomial being integrated for the k=1 moment. -/
theorem mixed_integrand_expand (d : SimplexData) (j : Fin 10)
    (x : Fin 8 → ℝ) :
    affine (gapVertices d) x * affine (yVertices d) x *
        (affine (bVertices d j) x)^2 =
      ∑ i : Fin 9, ∑ k : Fin 9, ∑ r : Fin 9, ∑ t : Fin 9,
        (gapVertices d i * yVertices d k *
          bVertices d j r * bVertices d j t) *
          (barycentric i x * barycentric k x *
            barycentric r x * barycentric t x) := by
  simp only [affine, pow_two, Finset.sum_mul, Finset.mul_sum]
  ring

private def term (d : SimplexData) (j : Fin 10)
    (i k r t : Fin 9) (x : Fin 8 → ℝ) : ℝ :=
  (gapVertices d i * yVertices d k *
      bVertices d j r * bVertices d j t) *
    (barycentric i x * barycentric k x *
      barycentric r x * barycentric t x)

private theorem term_integrable (d : SimplexData) (j : Fin 10)
    (i k r t : Fin 9) :
    IntegrableOn (term d j i k r t) (standardSimplex 8 (1 : ℝ)) := by
  apply ContinuousOn.integrableOn_compact _
    (isCompact_standardSimplex (by norm_num))
  unfold term
  exact (continuous_const.mul ((((barycentric_continuous i).mul
    (barycentric_continuous k)).mul (barycentric_continuous r)).mul
      (barycentric_continuous t))).continuousOn

/-- The actual numerator is an exact finite sum of measured fourth
moments. Each summand is an actual integral, and `barycentricMoment_eq`
evaluates every term by factorials. -/
theorem actualMixedNumerator_eq_moment_sum
    (d : SimplexData) (j : Fin 10) :
    actualMixedNumerator d j =
      ∑ i : Fin 9, ∑ k : Fin 9, ∑ r : Fin 9, ∑ t : Fin 9,
        (gapVertices d i * yVertices d k *
          bVertices d j r * bVertices d j t) *
          barycentricMoment (fourExponent i k r t) := by
  have h₁ (i k r : Fin 9) : IntegrableOn
      (fun x : Fin 8 → ℝ => ∑ t : Fin 9, term d j i k r t x)
      (standardSimplex 8 (1 : ℝ)) :=
    integrable_finsetSum Finset.univ (fun t _ => term_integrable d j i k r t)
  have h₂ (i k : Fin 9) : IntegrableOn
      (fun x : Fin 8 → ℝ => ∑ r : Fin 9, ∑ t : Fin 9, term d j i k r t x)
      (standardSimplex 8 (1 : ℝ)) :=
    integrable_finsetSum Finset.univ (fun r _ => h₁ i k r)
  have h₃ (i : Fin 9) : IntegrableOn
      (fun x : Fin 8 → ℝ => ∑ k : Fin 9, ∑ r : Fin 9,
        ∑ t : Fin 9, term d j i k r t x)
      (standardSimplex 8 (1 : ℝ)) :=
    integrable_finsetSum Finset.univ (fun k _ => h₂ i k)
  have he : (fun x : Fin 8 → ℝ =>
      affine (gapVertices d) x * affine (yVertices d) x *
        (affine (bVertices d j) x)^2) =
      (fun x => ∑ i : Fin 9, ∑ k : Fin 9,
        ∑ r : Fin 9, ∑ t : Fin 9, term d j i k r t x) := by
    funext x
    exact mixed_integrand_expand d j x
  unfold actualMixedNumerator
  rw [he, integral_finsetSum Finset.univ (fun i _ => h₃ i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum Finset.univ (fun k _ => h₂ i k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum Finset.univ (fun r _ => h₁ i k r)]
  apply Finset.sum_congr rfl
  intro r _
  rw [integral_finsetSum Finset.univ
    (fun t _ => term_integrable d j i k r t)]
  apply Finset.sum_congr rfl
  intro t _
  unfold term
  rw [integral_const_mul, barycentric_four]

theorem actualMixedExpectation_eq_moment_sum
    (d : SimplexData) (j : Fin 10) :
    actualMixedExpectation d j =
      ((9.factorial : ℝ) / (gapTotal d.gaps : ℝ)) *
        (∑ i : Fin 9, ∑ k : Fin 9, ∑ r : Fin 9, ∑ t : Fin 9,
          (gapVertices d i * yVertices d k *
            bVertices d j r * bVertices d j t) *
            barycentricMoment (fourExponent i k r t)) := by
  rw [actualMixedExpectation, actualMixedNumerator_eq_moment_sum,
    actualGapMass_eq]
  have hG : (gapTotal d.gaps : ℝ) ≠ 0 := by
    exact ne_of_gt (by exact_mod_cast d.gapsPos)
  have hf : (9.factorial : ℝ) ≠ 0 := by norm_num
  field_simp [hG, hf]

/-- An explicit finite Dirichlet factorial expression for the actual
signed k=1 expectation. The remaining equality to Phase14's particular
integer convolution is finite algebra, not a measure-theory premise. -/
theorem actualMixedExpectation_eq_factorial_sum
    (d : SimplexData) (j : Fin 10) :
    actualMixedExpectation d j =
      ((9.factorial : ℝ) / (gapTotal d.gaps : ℝ)) *
        (∑ i : Fin 9, ∑ k : Fin 9, ∑ r : Fin 9, ∑ t : Fin 9,
          (gapVertices d i * yVertices d k *
            bVertices d j r * bVertices d j t) *
            (((fourExponent i k r t 0).factorial *
              factorialProduct (List.ofFn
                (fun q : Fin 8 => fourExponent i k r t q.succ)) : Nat) : ℝ) /
              (((fourExponent i k r t 0) +
                (List.ofFn (fun q : Fin 8 => fourExponent i k r t q.succ)).sum + 8).factorial : ℝ))) := by
  rw [actualMixedExpectation_eq_moment_sum]
  simp_rw [barycentricMoment_eq]

end

end ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
