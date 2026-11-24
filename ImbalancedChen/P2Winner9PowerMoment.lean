import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
import Mathlib.Data.Nat.Choose.Multinomial

namespace ImbalancedChen.P2Winner9PowerMoment

open Finset
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly

private abbrev compositions (k : ℕ) : Finset (Fin 9 → ℕ) :=
  Finset.piAntidiag Finset.univ k

private theorem mem_compositions {k : ℕ} {e : Fin 9 → ℕ} :
    e ∈ compositions k ↔ (∑ r, e r) = k := by
  simp [compositions]

private theorem exponent_le {k : ℕ} {e : Fin 9 → ℕ} (he : e ∈ compositions k)
    (i : Fin 9) : e i ≤ k := by
  rw [← mem_compositions.mp he]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

private def spike (i : Fin 9) (j : ℕ) (r : Fin 9) : ℕ :=
  if r = i then j else 0

private theorem sum_spike (i : Fin 9) (j : ℕ) : (∑ r, spike i j r) = j := by
  simp [spike, Finset.sum_ite_eq']

private theorem prod_pow_spike {R : Type*} [CommMonoid R] (y : Fin 9 → R)
    (i : Fin 9) (j : ℕ) : (∏ r, y r ^ (spike i j r)) = y i ^ j := by
  refine Fintype.prod_eq_single i (fun r h => ?_) |>.trans ?_
  · simp [spike, h]
  · simp [spike]

private theorem homogeneous_eq_compositions (y : Fin 9 → ℕ) (k : ℕ) :
    homogeneous y k = ∑ e ∈ compositions k, ∏ r, y r ^ e r := by
  unfold homogeneous
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun e _ r => (e r).val)
    (fun e he r => ⟨e r, Nat.lt_succ_of_le (exponent_le he r)⟩) ?_ ?_ ?_ ?_ ?_
  · intro e he
    exact mem_compositions.mpr (Finset.mem_filter.mp he).2
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_compositions.mp he⟩
  · intro e he
    rfl
  · intro e he
    rfl
  · intro e he
    rfl

private theorem sum_shifted (y : Fin 9 → ℕ) (i : Fin 9) {k j : ℕ} (hj : j ≤ k) :
    (∑ e ∈ compositions k, if j ≤ e i then ∏ r, y r ^ e r else 0) =
      (∑ e ∈ compositions (k - j), ∏ r, y r ^ e r) * y i ^ j := by
  classical
  rw [← Finset.sum_filter, Finset.sum_mul]
  symm
  refine Finset.sum_nbij (fun e => e + spike i j) ?_ ?_ ?_ ?_
  · intro e he
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_compositions.mpr
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_spike, mem_compositions.mp he,
        Nat.sub_add_cancel hj]
    · simp [Pi.add_apply, spike]
  · intro a ha b hb hab
    funext r
    exact Nat.add_right_cancel (congrFun hab r)
  · intro b hb
    have hb' := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
    let a : Fin 9 → ℕ := fun r => b r - spike i j r
    have hab : a + spike i j = b := by
      funext r
      change b r - spike i j r + spike i j r = b r
      by_cases hr : r = i
      · subst r
        simpa [spike] using Nat.sub_add_cancel hb'.2
      · simp [spike, hr]
    have ha : a ∈ compositions (k - j) := by
      have hsum := congrArg (fun e : Fin 9 → ℕ => ∑ r, e r) hab
      simp only [Pi.add_apply, Finset.sum_add_distrib, sum_spike, mem_compositions.mp hb'.1] at hsum
      exact mem_compositions.mpr (by omega)
    exact ⟨a, Finset.mem_coe.mpr ha, hab⟩
  · intro e he
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib, prod_pow_spike]

private theorem mul_succ_as_sum {k n : ℕ} (h : n ≤ k) (a : ℕ) :
    (n + 1) * a = ∑ j ∈ Finset.range (k + 1), if j ≤ n then a else 0 := by
  have hf : (Finset.range (k + 1)).filter (fun j => j ≤ n) = Finset.range (n + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf, Finset.sum_const_nat (fun _ _ => rfl), Finset.card_range]

/-- The convolution in the original exact assembly counts each monomial once
for each choice of how many copies of its distinguished gap coordinate to remove. -/
theorem weightedMoment_eq_compositions (d : SimplexData) (k : ℕ) :
    weightedMoment d k =
      ∑ i : Fin 9, d.gaps i * (∑ e ∈ compositions k, (e i + 1) * ∏ r, d.y r ^ e r) := by
  classical
  unfold weightedMoment powerMoment
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  calc
    _ = ∑ j ∈ Finset.range (k + 1), d.gaps i *
        (∑ e ∈ compositions k, if j ≤ e i then ∏ r, d.y r ^ e r else 0) := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [sum_shifted d.y i (Nat.le_of_lt_succ (Finset.mem_range.mp hj)),
        ← homogeneous_eq_compositions]
      ac_rfl
    _ = ∑ e ∈ compositions k, d.gaps i *
        (∑ j ∈ Finset.range (k + 1), if j ≤ e i then ∏ r, d.y r ^ e r else 0) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by
      refine Finset.sum_congr rfl (fun e he => ?_)
      rw [← mul_succ_as_sum (exponent_le he i)]


noncomputable section

open Set MeasureTheory
open ImbalancedChen.P2Winner9SimplexCoordinateSlice
open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9NestedEightSimplexMoment (factorialProduct)
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor (gapTotal)

private theorem barycentricMoment_eq_prod (e : Fin 9 → ℕ) :
    barycentricMoment e =
      ((∏ r, (e r).factorial : ℕ) : ℝ) / (((∑ r, e r) + 8).factorial : ℝ) := by
  rw [barycentricMoment_eq, factorialProduct, List.map_ofFn, List.prod_ofFn,
    List.sum_ofFn, Fin.prod_univ_succ (fun r : Fin 9 => (e r).factorial),
    Fin.sum_univ_succ (fun r : Fin 9 => e r)]
  rfl

private theorem multinomial_shifted_factorial {k : ℕ} {e : Fin 9 → ℕ}
    (he : e ∈ compositions k) (i : Fin 9) :
    Nat.multinomial Finset.univ e * (∏ r, (e r + spike i 1 r).factorial) =
      k.factorial * (e i + 1) := by
  have hprod : (∏ r, (e r + spike i 1 r).factorial) =
      (∏ r, (e r).factorial) * (e i + 1) := by
    calc
      _ = ∏ r, ((e r).factorial * if r = i then e i + 1 else 1) := by
        refine Finset.prod_congr rfl (fun r _ => ?_)
        by_cases h : r = i
        · subst r
          simp [spike, Nat.factorial_succ, mul_comm]
        · simp [spike, h]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  rw [hprod, ← mul_assoc, mul_comm (Nat.multinomial _ _), Nat.multinomial_spec,
    mem_compositions.mp he]

/-- The canonical simplex integral with gap density and the kth power of y. -/
def actualPowerNumerator (d : SimplexData) (k : ℕ) : ℝ :=
  ∫ x in standardSimplex 8 (1 : ℝ), affine (gapVertices d) x * (affine (yVertices d) x)^k

/-- The kth power moment under the probability measure with gap density. -/
def actualPowerExpectation (d : SimplexData) (k : ℕ) : ℝ :=
  actualPowerNumerator d k / actualGapMass d

private def powerCoefficient (d : SimplexData) (i : Fin 9) (e : Fin 9 → ℕ) : ℝ :=
  gapVertices d i * (Nat.multinomial Finset.univ e : ℝ) * (∏ r, (yVertices d r)^e r)

private def powerTerm (d : SimplexData) (i : Fin 9) (e : Fin 9 → ℕ) (x : Fin 8 → ℝ) : ℝ :=
  powerCoefficient d i e * (∏ r, (barycentric r x)^((e + spike i 1) r))

private theorem power_integrand_expand (d : SimplexData) (k : ℕ) (x : Fin 8 → ℝ) :
    affine (gapVertices d) x * (affine (yVertices d) x)^k =
      ∑ i, ∑ e ∈ compositions k, powerTerm d i e x := by
  unfold affine
  rw [Finset.sum_pow_eq_sum_piAntidiag, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e _ => ?_
  simp only [powerTerm, powerCoefficient, mul_pow, Finset.prod_mul_distrib, Pi.add_apply, pow_add,
    prod_pow_spike, pow_one]
  ring

private theorem powerTerm_integrable (d : SimplexData) (i : Fin 9) (e : Fin 9 → ℕ) :
    IntegrableOn (powerTerm d i e) (standardSimplex 8 (1 : ℝ)) := by
  refine (Continuous.mul continuous_const ?_).continuousOn.integrableOn_compact
    (isCompact_standardSimplex (by norm_num))
  exact continuous_finsetProd Finset.univ (fun r _ => (barycentric_continuous r).pow _)

private theorem actualPowerNumerator_eq_sum (d : SimplexData) (k : ℕ) :
    actualPowerNumerator d k =
      ∑ i, ∑ e ∈ compositions k, powerCoefficient d i e * barycentricMoment (e + spike i 1) := by
  have hfun : (fun x => affine (gapVertices d) x * (affine (yVertices d) x)^k) =
      (fun x => ∑ i, ∑ e ∈ compositions k, powerTerm d i e x) :=
    funext (power_integrand_expand d k)
  unfold actualPowerNumerator
  rw [hfun, integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum (compositions k) (fun e _ => powerTerm_integrable d i e))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_finsetSum (compositions k) (fun e _ => powerTerm_integrable d i e)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  unfold powerTerm barycentricMoment
  rw [integral_const_mul]

private theorem vertex_power_product (d : SimplexData) {k : ℕ} {e : Fin 9 → ℕ}
    (he : e ∈ compositions k) :
    (∏ r, (yVertices d r)^e r) =
      ((∏ r, (d.y r)^e r : ℕ) : ℝ) / (d.U : ℝ)^k := by
  simp only [yVertices, div_pow, Finset.prod_div_distrib, Nat.cast_prod, Nat.cast_pow,
    Finset.prod_pow_eq_pow_sum, mem_compositions.mp he]

private theorem powerCoefficient_mul_moment (d : SimplexData) {k : ℕ} {e : Fin 9 → ℕ}
    (he : e ∈ compositions k) (i : Fin 9) :
    powerCoefficient d i e * barycentricMoment (e + spike i 1) =
      ((k.factorial : ℝ) / ((k + 9).factorial : ℝ) / (d.U : ℝ)^k) *
        ((d.gaps i * ((e i + 1) * ∏ r, d.y r ^ e r) : ℕ) : ℝ) := by
  have hsum : (∑ r, (e + spike i 1) r) + 8 = k + 9 := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, sum_spike, mem_compositions.mp he]
  have hprod :
      (Nat.multinomial Finset.univ e : ℝ) * ((∏ r, (e r + spike i 1 r).factorial : ℕ) : ℝ) =
        (k.factorial : ℝ) * (↑(e i + 1) : ℝ) := by
    exact_mod_cast multinomial_shifted_factorial he i
  rw [barycentricMoment_eq_prod, hsum, powerCoefficient, vertex_power_product d he]
  rw [show (∏ r, ((e + spike i 1) r).factorial) =
      ∏ r, (e r + spike i 1 r).factorial by rfl]
  calc
    _ = ((Nat.multinomial Finset.univ e : ℝ) *
          ((∏ r, (e r + spike i 1 r).factorial : ℕ) : ℝ)) *
        (gapVertices d i * ((∏ r, d.y r ^ e r : ℕ) : ℝ) /
          ((d.U : ℝ)^k * ((k + 9).factorial : ℝ))) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
    _ = _ := by
      rw [hprod]
      simp only [gapVertices, Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring

/-- Every canonical gap-weighted power integral equals the original exact
weighted moment times its factorial and vertex-scale factors. -/
theorem actualPowerNumerator_eq_weightedMoment (d : SimplexData) (k : ℕ) :
    actualPowerNumerator d k =
      ((k.factorial : ℝ) / ((k + 9).factorial : ℝ)) *
        (weightedMoment d k : ℝ) / (d.U : ℝ)^k := by
  rw [actualPowerNumerator_eq_sum, weightedMoment_eq_compositions]
  simp only [Nat.cast_sum, Nat.cast_mul]
  calc
    _ = ∑ i, ∑ e ∈ compositions k,
        ((k.factorial : ℝ) / ((k + 9).factorial : ℝ) / (d.U : ℝ)^k) *
          ((d.gaps i : ℝ) * ((e i + 1) * ((∏ r, d.y r ^ e r : ℕ) : ℝ))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun e he => ?_
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using
        powerCoefficient_mul_moment d he i
    _ = _ := by
      simp_rw [← Finset.mul_sum, Nat.cast_add, Nat.cast_one]
      ring

/-- Dividing by the genuine gap mass gives the probability-normalized
power moment used by the exact Winner9 assembly. -/
theorem actualPowerExpectation_eq_weightedMoment (d : SimplexData) (k : ℕ) :
    actualPowerExpectation d k =
      (((9 : ℕ).factorial : ℝ) / (gapTotal d.gaps : ℝ)) *
        ((k.factorial : ℝ) / ((k + 9).factorial : ℝ)) *
        (weightedMoment d k : ℝ) / (d.U : ℝ)^k := by
  rw [actualPowerExpectation, actualPowerNumerator_eq_weightedMoment, actualGapMass_eq]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

end

end ImbalancedChen.P2Winner9PowerMoment
