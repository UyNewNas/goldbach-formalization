import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
import Mathlib.Data.Nat.Choose.Multinomial

/-! Actual affine powers with additional barycentric monomial factors. -/

namespace ImbalancedChen.P2Winner9MixedPowerMoment

noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor (gapTotal)
open ImbalancedChen.P2Winner9SimplexCoordinateSlice
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9NestedEightSimplexMoment (factorialProduct)

private theorem barycentricMoment_eq_product (e : Fin 9 → ℕ) :
    barycentricMoment e =
      ((∏ i, (e i).factorial : ℕ) : ℝ) / (((∑ i, e i) + 8).factorial : ℝ) := by
  rw [barycentricMoment_eq, factorialProduct, List.map_ofFn, List.prod_ofFn,
    List.sum_ofFn, Fin.prod_univ_succ (fun i : Fin 9 => (e i).factorial),
    Fin.sum_univ_succ (fun i : Fin 9 => e i)]
  rfl

private theorem multinomial_shift {k : ℕ} {e : Fin 9 → ℕ}
    (he : e ∈ Finset.piAntidiag Finset.univ k) (m : Fin 9 → ℕ) :
    Nat.multinomial Finset.univ e * (∏ i, (e i + m i).factorial) =
      k.factorial * ((∏ i, (m i).factorial) * ∏ i, (e i + m i).choose (m i)) := by
  have h i : (e i + m i).factorial =
      (e i).factorial * ((m i).factorial * (e i + m i).choose (m i)) := by
    rw [← Nat.add_choose_mul_factorial_mul_factorial (e i) (m i)]
    ac_rfl
  simp only [h, Finset.prod_mul_distrib]
  rw [← mul_assoc, mul_comm (Nat.multinomial _ _), Nat.multinomial_spec,
    (Finset.mem_piAntidiag.mp he).1]

private theorem integral_affine_pow_barycentric_expansion (v : Fin 9 → ℝ)
    (k : ℕ) (m : Fin 9 → ℕ) :
    (∫ x in standardSimplex 8 (1 : ℝ),
      (affine v x)^k * ∏ i, (barycentric i x)^(m i)) =
      ∑ e ∈ Finset.piAntidiag Finset.univ k,
        ((Nat.multinomial Finset.univ e : ℝ) * ∏ i, (v i)^(e i)) *
          barycentricMoment (e + m) := by
  let coeff (e : Fin 9 → ℕ) := (Nat.multinomial Finset.univ e : ℝ) * ∏ i, (v i)^(e i)
  let term (e : Fin 9 → ℕ) (x : Fin 8 → ℝ) :=
    coeff e * ∏ i, (barycentric i x)^((e + m) i)
  have hfun : (fun x => (affine v x)^k * ∏ i, (barycentric i x)^(m i)) =
      (fun x => ∑ e ∈ Finset.piAntidiag Finset.univ k, term e x) := by
    funext x
    unfold affine
    rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp only [term, coeff, mul_pow, Finset.prod_mul_distrib, Pi.add_apply, pow_add]
    ring
  have hi (e : Fin 9 → ℕ) : IntegrableOn (term e) (standardSimplex 8 (1 : ℝ)) := by
    refine (Continuous.mul continuous_const ?_).continuousOn.integrableOn_compact
      (isCompact_standardSimplex (by norm_num))
    exact continuous_finsetProd Finset.univ (fun i _ => (barycentric_continuous i).pow _)
  rw [hfun, integral_finsetSum _ (fun e _ => hi e)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  unfold term coeff barycentricMoment
  rw [integral_const_mul]

/-- The general measured affine-power coefficient with fixed barycentric insertions.
The multinomial and Dirichlet factorials combine into binomial coefficients. -/
theorem integral_affine_pow_barycentric (v : Fin 9 → ℝ) (k : ℕ) (m : Fin 9 → ℕ) :
    (∫ x in standardSimplex 8 (1 : ℝ),
      (affine v x)^k * ∏ i, (barycentric i x)^(m i)) =
      ((k.factorial : ℝ) * ((∏ i, (m i).factorial : ℕ) : ℝ) /
        ((k + (∑ i, m i) + 8).factorial : ℝ)) *
      (∑ e ∈ Finset.piAntidiag Finset.univ k,
        ∏ i, ((e i + m i).choose (m i) : ℝ) * (v i)^(e i)) := by
  rw [integral_affine_pow_barycentric_expansion, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have sume := (Finset.mem_piAntidiag.mp he).1
  have hsum : (∑ i, (e + m) i) + 8 = k + (∑ i, m i) + 8 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sume]
  have hprod : (Nat.multinomial Finset.univ e : ℝ) *
      ((∏ i, (e i + m i).factorial : ℕ) : ℝ) =
      (k.factorial : ℝ) * (((∏ i, (m i).factorial : ℕ) : ℝ) *
        ((∏ i, (e i + m i).choose (m i) : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) (multinomial_shift he m)
  rw [barycentricMoment_eq_product, hsum, Finset.prod_mul_distrib, ← Nat.cast_prod]
  change (Nat.multinomial Finset.univ e : ℝ) * (∏ i, (v i)^(e i)) *
      (((∏ i, (e i + m i).factorial : ℕ) : ℝ) / _) = _
  calc
    _ = ((Nat.multinomial Finset.univ e : ℝ) * ((∏ i, (e i + m i).factorial : ℕ) : ℝ)) *
        ((∏ i, (v i)^(e i)) / ((k + (∑ i, m i) + 8).factorial : ℝ)) := by ring
    _ = _ := by rw [hprod]; ring

/-- One gap factor and two deviation factors, with repeats counted. -/
def tripleExponent (a c r : Fin 9) (i : Fin 9) : ℕ :=
  unitExponent a i + unitExponent c i + unitExponent r i

theorem tripleExponent_degree (a c r : Fin 9) :
    (∑ i, tripleExponent a c r i) = 3 := by
  have hu (a : Fin 9) : (∑ i, unitExponent a i) = 1 := by
    simp [unitExponent, Finset.sum_ite_eq']
  simp only [tripleExponent, Finset.sum_add_distrib, hu]

private theorem prod_unitExponent (a : Fin 9) (x : Fin 8 → ℝ) :
    (∏ i, (barycentric i x)^(unitExponent a i)) = barycentric a x := by
  rw [Fintype.prod_eq_single a (fun i hi => by simp [unitExponent, hi])]
  simp [unitExponent]

/-- The actual mixed power integral on the canonical simplex with gap density. -/
def actualMixedPowerNumerator (d : SimplexData) (j : Fin 10) (k : ℕ) : ℝ :=
  ∫ x in standardSimplex 8 (1 : ℝ),
    affine (gapVertices d) x * (affine (yVertices d) x)^k * (affine (bVertices d j) x)^2

/-- The probability-normalized mixed power under the canonical gap density. -/
def actualMixedPowerExpectation (d : SimplexData) (j : Fin 10) (k : ℕ) : ℝ :=
  actualMixedPowerNumerator d j k / actualGapMass d

/-- The division-free signed sum obtained by expanding the measured mixed power. -/
def mixedCompositionNumerator (d : SimplexData) (j : Fin 10) (k : ℕ) : ℤ :=
  ∑ a : Fin 9, ∑ c : Fin 9, ∑ r : Fin 9,
    (d.gaps a : ℤ) * d.deviations j c * d.deviations j r *
      ((∏ i, (tripleExponent a c r i).factorial : ℕ) : ℤ) *
      (∑ e ∈ Finset.piAntidiag Finset.univ k,
        ∏ i, ((e i + tripleExponent a c r i).choose (tripleExponent a c r i) : ℤ) *
          (d.y i : ℤ)^(e i))

private theorem actualMixedPowerNumerator_expansion (d : SimplexData) (j : Fin 10) (k : ℕ) :
    actualMixedPowerNumerator d j k =
      ∑ a : Fin 9, ∑ c : Fin 9, ∑ r : Fin 9,
        (gapVertices d a * bVertices d j c * bVertices d j r) *
          (∫ x in standardSimplex 8 (1 : ℝ),
            (affine (yVertices d) x)^k * ∏ i, (barycentric i x)^(tripleExponent a c r i)) := by
  let term (a c r : Fin 9) (x : Fin 8 → ℝ) :=
    (gapVertices d a * bVertices d j c * bVertices d j r) *
      ((affine (yVertices d) x)^k * ∏ i, (barycentric i x)^(tripleExponent a c r i))
  have he : (fun x => affine (gapVertices d) x * (affine (yVertices d) x)^k *
      (affine (bVertices d j) x)^2) = fun x => ∑ a, ∑ c, ∑ r, term a c r x := by
    funext x
    change (∑ a, gapVertices d a * barycentric a x) * (affine (yVertices d) x)^k *
      (∑ c, bVertices d j c * barycentric c x)^2 = _
    rw [pow_two, ← mul_assoc]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun c _ => ?_))
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [term, tripleExponent, pow_add, Finset.prod_mul_distrib, prod_unitExponent]
    ring
  have hi (a c r : Fin 9) : IntegrableOn (term a c r) (standardSimplex 8 (1 : ℝ)) := by
    have hp : Continuous (fun x => ∏ i, (barycentric i x)^(tripleExponent a c r i)) :=
      continuous_finsetProd Finset.univ (fun i _ => (barycentric_continuous i).pow _)
    have hc : Continuous (term a c r) :=
      continuous_const.mul (((affine_continuous (yVertices d)).pow k).mul hp)
    exact hc.continuousOn.integrableOn_compact (isCompact_standardSimplex (by norm_num))
  unfold actualMixedPowerNumerator
  rw [he, integral_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun c _ => integrable_finsetSum Finset.univ (fun r _ => hi a c r)))]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [integral_finsetSum Finset.univ (fun c _ => integrable_finsetSum Finset.univ (fun r _ => hi a c r))]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [integral_finsetSum Finset.univ (fun r _ => hi a c r)]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold term
  rw [integral_const_mul]

private theorem composition_sum_vertex_scale (d : SimplexData) (k : ℕ) (m : Fin 9 → ℕ) :
    (∑ e ∈ Finset.piAntidiag Finset.univ k,
      ∏ i, ((e i + m i).choose (m i) : ℝ) * (yVertices d i)^(e i)) =
    ((∑ e ∈ Finset.piAntidiag Finset.univ k,
      ∏ i, ((e i + m i).choose (m i) : ℤ) * (d.y i : ℤ)^(e i)) : ℝ) / (d.U : ℝ)^k := by
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun e he => ?_)
  have hsum : (∑ i, e i) = k := (Finset.mem_piAntidiag.mp he).1
  simp only [yVertices, div_pow, ← mul_div_assoc _ _ _, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, hsum]

/-- Exact signed integer expression for each unnormalized measured mixed power. -/
theorem actualMixedPowerNumerator_eq_compositions (d : SimplexData) (j : Fin 10) (k : ℕ) :
    actualMixedPowerNumerator d j k =
      ((k.factorial : ℝ) / ((k + 11).factorial : ℝ) / (d.U : ℝ)^k / (d.L : ℝ)^2) *
        (mixedCompositionNumerator d j k : ℝ) := by
  rw [actualMixedPowerNumerator_expansion]
  simp_rw [integral_affine_pow_barycentric, tripleExponent_degree, composition_sum_vertex_scale]
  unfold mixedCompositionNumerator
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  simp only [gapVertices, bVertices, div_eq_mul_inv]
  ring

/-- Exact signed integer expression for each probability-normalized mixed power. -/
theorem actualMixedPowerExpectation_eq_compositions (d : SimplexData) (j : Fin 10) (k : ℕ) :
    actualMixedPowerExpectation d j k =
      (((9 : ℕ).factorial : ℝ) * (k.factorial : ℝ) / ((k + 11).factorial : ℝ)) *
        ((mixedCompositionNumerator d j k : ℝ) /
          ((gapTotal d.gaps : ℝ) * (d.U : ℝ)^k * (d.L : ℝ)^2)) := by
  rw [actualMixedPowerExpectation, actualMixedPowerNumerator_eq_compositions, actualGapMass_eq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end

end ImbalancedChen.P2Winner9MixedPowerMoment
