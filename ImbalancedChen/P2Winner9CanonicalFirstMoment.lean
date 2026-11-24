import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne

/-! The exact first affine moment against the canonical gap weight. -/
namespace ImbalancedChen.P2Winner9CanonicalFirstMoment

noncomputable section

open MeasureTheory
open P2Winner9BarycentricMixedDegreeOne
open P2Winner9CurvatureExactMomentFloor (gapTotal)
open P2Winner9CurvatureFullExactAssembly (SimplexData)
open P2Winner9NestedEightSimplexMoment (factorialProduct)
open P2Winner9SimplexCoordinateSlice
open scoped BigOperators

private theorem prod_unit (i : Fin 9) (x : Fin 8 → ℝ) :
    (∏ r : Fin 9, barycentric r x ^ unitExponent i r) = barycentric i x := by
  calc
    _ = ∏ r : Fin 9, if r = i then barycentric r x else 1 := by
      apply Finset.prod_congr rfl
      intro r _
      by_cases h : r = i <;> simp [unitExponent, h]
    _ = _ := by simp

private theorem pairFactorial : ∀ i j : Fin 9,
    let e := fun r => unitExponent i r + unitExponent j r
    e 0 + (List.ofFn (fun r : Fin 8 => e r.succ)).sum + 8 = 10 ∧
      (e 0).factorial * factorialProduct (List.ofFn (fun r : Fin 8 => e r.succ)) =
        1 + if j = i then 1 else 0 := by
  decide +kernel

/-- The unweighted second barycentric moment, including the repeated index. -/
theorem barycentric_pair_value (i j : Fin 9) :
    (∫ x in standardSimplex 8 (1 : ℝ), barycentric i x * barycentric j x) =
      (1 + if j = i then 1 else 0) / ((10 : ℕ).factorial : ℝ) := by
  let e := fun r => unitExponent i r + unitExponent j r
  have he : (∫ x in standardSimplex 8 (1 : ℝ), barycentric i x * barycentric j x) =
      barycentricMoment e := by
    unfold barycentricMoment
    apply setIntegral_congr_fun (isClosed_standardSimplex (1 : ℝ)).measurableSet
    intro x _
    simp only [e, pow_add, Finset.prod_mul_distrib, prod_unit]
  rw [he, barycentricMoment_eq]
  obtain ⟨hdegree, hfactor⟩ := pairFactorial i j
  change e 0 + (List.ofFn (fun r : Fin 8 => e r.succ)).sum + 8 = 10 at hdegree
  change (e 0).factorial * factorialProduct (List.ofFn (fun r : Fin 8 => e r.succ)) = _ at hfactor
  rw [hdegree, hfactor]
  by_cases h : j = i <;> norm_num [h]

private def term (d : SimplexData) (v : Fin 9 → ℝ) (i j : Fin 9) (x : Fin 8 → ℝ) : ℝ :=
  (gapVertices d i * v j) * (barycentric i x * barycentric j x)

/-- The first affine moment under the normalized Lebesgue gap weight. -/
theorem actualGapWeightedAffine_eq (d : SimplexData) (v : Fin 9 → ℝ) :
    (∫ x in standardSimplex 8 (1 : ℝ), affine (gapVertices d) x * affine v x) /
        actualGapMass d =
      ((gapTotal d.gaps : ℝ) * (∑ i, v i) + ∑ i, gapVertices d i * v i) /
        (10 * (gapTotal d.gaps : ℝ)) := by
  have hi (i j : Fin 9) : IntegrableOn (term d v i j) (standardSimplex 8 (1 : ℝ)) := by
    exact (continuous_const.mul
      ((barycentric_continuous i).mul (barycentric_continuous j))).continuousOn.integrableOn_compact
        (isCompact_standardSimplex (by norm_num))
  have hsum (i : Fin 9) : IntegrableOn (fun x => ∑ j, term d v i j x)
      (standardSimplex 8 (1 : ℝ)) :=
    integrable_finsetSum Finset.univ (fun j _ => hi i j)
  have hexpand : (fun x => affine (gapVertices d) x * affine v x) =
      fun x => ∑ i, ∑ j, term d v i j x := by
    funext x
    unfold affine
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    unfold term
    ring
  rw [hexpand, integral_finsetSum Finset.univ (fun i _ => hsum i)]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hi _ j), term, integral_const_mul,
    barycentric_pair_value]
  have hrow (i : Fin 9) :
      (∑ j : Fin 9, gapVertices d i * v j * ((1 + if j = i then 1 else 0) /
        ((10 : ℕ).factorial : ℝ))) =
        (gapVertices d i * (∑ j, v j) + gapVertices d i * v i) /
          ((10 : ℕ).factorial : ℝ) := by
    calc
      _ = ∑ j : Fin 9, (gapVertices d i * v j +
          if j = i then gapVertices d i * v i else 0) / ((10 : ℕ).factorial : ℝ) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = i
        · subst j
          simp
          ring
        · simp only [if_neg h]
          ring
      _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq']
        simp
  simp_rw [hrow]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, actualGapMass_eq]
  have hg : (∑ i : Fin 9, gapVertices d i) = (gapTotal d.gaps : ℝ) := by
    simp only [gapVertices, gapTotal, Nat.cast_sum]
  rw [hg]
  have hG : (gapTotal d.gaps : ℝ) ≠ 0 := by exact_mod_cast d.gapsPos.ne'
  norm_num
  field_simp [hG]
  ring

end

end ImbalancedChen.P2Winner9CanonicalFirstMoment
