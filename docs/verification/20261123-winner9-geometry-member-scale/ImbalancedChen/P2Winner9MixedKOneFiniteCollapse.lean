import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Bounded finite-algebra continuation of the actual Δ8 measured k=1
mixed expectation. No analytic moment identity (M) is an assumption.
The fourth Dirichlet moment is reduced to its equality-partition kernel,
and the weighted kernel is expanded to the Phase14 signed coefficient.
This source has not been compiled or checked; all imports are held.
-/

namespace ImbalancedChen.P2Winner9MixedKOneFiniteCollapse

noncomputable section

open ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
open ImbalancedChen.P2Winner9ActualEightSimplexMoment
open ImbalancedChen.P2Winner9NestedEightSimplexMoment
open ImbalancedChen.P2Winner9CurvatureExactMomentFloor
open ImbalancedChen.P2Winner9CurvatureFullExactAssembly
open ImbalancedChen.P2Winner9MixedDegreeSixExactAssembly
open ImbalancedChen.P2Winner9MixedZeroCoefficientCurvatureLink
open ImbalancedChen.P2Winner9MixedDegreeOnePolynomialMoment

def delta (i j : Fin 9) : ℤ := if i = j then 1 else 0

/-- Fifteen equality partitions of four labelled factors. -/
def kernel (a b c d : Fin 9) : ℤ :=
  1 + delta a b + delta a c + delta a d +
    delta b c + delta b d + delta c d +
    delta a b * delta c d +
    delta a c * delta b d +
    delta a d * delta b c +
    2 * (delta a b * delta a c + delta a b * delta a d +
      delta a c * delta a d + delta b c * delta b d) +
    6 * delta a b * delta a c * delta a d

/-- The degree is exactly four for every four labelled vertices, even
when indices repeat. This finite proof uses no certificate data. -/
theorem fourExponent_degree (a b c d : Fin 9) :
    fourExponent a b c d 0 +
      (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)).sum + 8 = 12 := by
  rw [List.sum_ofFn, ← Fin.sum_univ_succ]
  simp [fourExponent, Finset.sum_add_distrib, unitExponent]

/-- Inserting each successive label adds one choice for every earlier
occurrence of the same label. -/
private theorem kernel_factors (a b c e : Fin 9) :
    kernel a b c e = (1 + delta a b) * (1 + delta a c + delta b c) *
      (1 + delta a e + delta b e + delta c e) := by
  unfold kernel delta
  split_ifs <;> norm_num <;> grind

private theorem factorial_insert (n : Fin 9 → ℕ) (i : Fin 9) :
    (∏ r : Fin 9, (n r + unitExponent i r).factorial) =
      (∏ r : Fin 9, (n r).factorial) * (n i + 1) := by
  have hp (r : Fin 9) : (n r + unitExponent i r).factorial =
      (n r).factorial * (if r = i then n r + 1 else 1) := by
    by_cases h : r = i <;> simp [unitExponent, h, Nat.factorial_succ, mul_comm]
  simp_rw [hp]
  rw [Finset.prod_mul_distrib]
  simp

private theorem factorial_unit (i : Fin 9) :
    (∏ r : Fin 9, (unitExponent i r).factorial) = 1 := by
  apply Finset.prod_eq_one
  intro r _
  by_cases h : r = i <;> simp [unitExponent, h]

/-- The factorial multiplicity is 1,2,4,6 or 24 according to the
equality partition. The 15-term kernel encodes all five cases. -/
theorem fourFactorial_kernel (a b c d : Fin 9) :
    (((fourExponent a b c d 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c d q.succ)) : Nat) : ℤ) =
      kernel a b c d := by
  have hlist (f : Fin 9 → ℕ) :
      (f 0).factorial * factorialProduct (List.ofFn (fun r : Fin 8 => f r.succ)) =
        ∏ r : Fin 9, (f r).factorial := by
    rw [Fin.prod_univ_succ, factorialProduct, List.map_ofFn, List.prod_ofFn] <;> rfl
  have hu (i r : Fin 9) : (unitExponent i r : ℤ) = delta i r := by
    by_cases h : r = i
    · subst r
      simp [unitExponent, delta]
    · simp [unitExponent, delta, h, Ne.symm h]
  rw [hlist, kernel_factors]
  unfold fourExponent
  rw [factorial_insert (fun r => unitExponent a r + unitExponent b r + unitExponent c r) d,
    factorial_insert (fun r => unitExponent a r + unitExponent b r) c,
    factorial_insert (unitExponent a) b, factorial_unit]
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, hu, one_mul]
  ring

private def oneAt (i r : Fin 9) : Fin 2 := if r = i then 1 else 0

private theorem degree_oneAt (i : Fin 9) : (∑ r : Fin 9, (oneAt i r).val) = 1 := by
  have h (r : Fin 9) : (oneAt i r).val = if r = i then 1 else 0 := by
    by_cases hr : r = i <;> simp [oneAt, hr]
  simp [h]

private theorem eq_oneAt_of_degree_one (v : Fin 9 → Fin 2)
    (h : (∑ r : Fin 9, (v r).val) = 1) : ∃ i, v = oneAt i := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 9, (v i).val ≠ 0 := by
    by_contra! hz
    simp [hz] at h
  have hs := Finset.add_sum_erase Finset.univ (fun r => (v r).val) (Finset.mem_univ i)
  have ho : (v i).val = 1 := by omega
  have hzero : (∑ r ∈ Finset.univ.erase i, (v r).val) = 0 := by omega
  refine ⟨i, ?_⟩
  funext r
  apply Fin.ext
  by_cases hr : r = i
  · subst r
    simpa [oneAt] using ho
  · have hle := Finset.single_le_sum (f := fun r => (v r).val)
      (fun r _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩)
    simp [oneAt, hr] <;> omega

private theorem oneAt_injective : Function.Injective oneAt := by
  intro i j he
  by_contra hij
  have h := congrFun he i
  simp [oneAt, hij] at h

private theorem monomial_oneAt (y : Fin 9 → ℕ) (i : Fin 9) :
    (∏ r : Fin 9, y r ^ (oneAt i r).val) = y i := by
  calc
    _ = ∏ r : Fin 9, if r = i then y r else 1 := by
      apply Finset.prod_congr rfl
      intro r _
      by_cases h : r = i <;> simp [oneAt, h]
    _ = _ := by simp

/-- A bounded n=1 complete-homogeneous coefficient, independent of
moment calculus. -/
theorem homogeneous_one (y : Fin 9 → Nat) :
    (homogeneous y 1 : ℤ) = ∑ i : Fin 9, (y i : ℤ) := by
  classical
  have ht (v : Fin 9 → Fin 2) :
      (if (∑ r : Fin 9, (v r).val) = 1 then ∏ r : Fin 9, y r ^ (v r).val else 0) =
        ∑ i : Fin 9, if v = oneAt i then y i else 0 := by
    by_cases h : (∑ r : Fin 9, (v r).val) = 1
    · obtain ⟨i, rfl⟩ := eq_oneAt_of_degree_one v h
      simp [degree_oneAt, monomial_oneAt, oneAt_injective.eq_iff]
    · have hne (i : Fin 9) : v ≠ oneAt i := by
        rintro rfl
        exact h (degree_oneAt i)
      simp [h, hne]
  have hn : homogeneous y 1 = ∑ i : Fin 9, y i := by
    unfold homogeneous
    calc
      _ = ∑ v : Fin 9 → Fin 2, ∑ i : Fin 9, if v = oneAt i then y i else 0 :=
        Finset.sum_congr rfl (fun v _ => ht v)
      _ = _ := by rw [Finset.sum_comm]; simp
  exact_mod_cast hn

private theorem contract_one (v : Fin 9 → ℤ) (a : Fin 9) :
    (∑ i : Fin 9, v i * (1 + delta a i)) = (∑ i : Fin 9, v i) + v a := by
  simp [mul_add, Finset.sum_add_distrib, delta, mul_ite]

private theorem contract_two (v : Fin 9 → ℤ) (a b : Fin 9) :
    (∑ i : Fin 9, v i * (1 + delta a i + delta b i)) =
      (∑ i : Fin 9, v i) + v a + v b := by
  simp [mul_add, Finset.sum_add_distrib, delta, mul_ite]

private theorem contract_three (v : Fin 9 → ℤ) (a b c : Fin 9) :
    (∑ i : Fin 9, v i * (1 + delta a i + delta b i + delta c i)) =
      (∑ i : Fin 9, v i) + v a + v b + v c := by
  simp [mul_add, Finset.sum_add_distrib, delta, mul_ite]

private theorem sum_deviation_pair (v : Fin 9 → ℤ) (a b : Fin 9) :
    (∑ c : Fin 9, v c * (1 + delta a c + delta b c) *
      ((∑ i : Fin 9, v i) + v a + v b + v c)) =
      ((∑ i : Fin 9, v i) + v a + v b)^2 + (∑ i : Fin 9, (v i)^2) +
        (v a)^2 + (v b)^2 := by
  calc
    _ = ((∑ i : Fin 9, v i) + v a + v b) *
        (∑ c : Fin 9, v c * (1 + delta a c + delta b c)) +
          ∑ c : Fin 9, (v c)^2 * (1 + delta a c + delta b c) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = _ := by
      rw [contract_two v a b, contract_two (fun i => (v i)^2) a b]
      ring

private theorem sum_vertex_polynomial (y v : Fin 9 → ℤ) (s q x : ℤ) :
    (∑ i : Fin 9, y i * ((s + x + v i)^2 + q + x^2 + (v i)^2)) =
      (s^2 + q + 2*s*x + 2*x^2) * (∑ i : Fin 9, y i) +
      2*(s+x) * (∑ i : Fin 9, v i * y i) +
      2 * (∑ i : Fin 9, (v i)^2 * y i) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem sum_y_vertex (g y v : Fin 9 → ℤ) (s q : ℤ) (a : Fin 9) :
    (∑ b : Fin 9, g a * y b * (1 + delta a b) *
      ((s + v a + v b)^2 + q + (v a)^2 + (v b)^2)) =
      g a * ((s^2 + q + 2*s*v a + 2*(v a)^2) * (∑ i : Fin 9, y i) +
        2*(s+v a) * (∑ i : Fin 9, v i * y i) +
        2 * (∑ i : Fin 9, (v i)^2 * y i) +
        y a * (s^2 + q + 4*s*v a + 6*(v a)^2)) := by
  let f (b : Fin 9) := y b * ((s + v a + v b)^2 + q + (v a)^2 + (v b)^2)
  calc
    _ = g a * ∑ b : Fin 9, f b * (1 + delta a b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      dsimp [f]
      ring
    _ = g a * ((∑ b : Fin 9, f b) + f a) := by rw [contract_one]
    _ = _ := by
      dsimp only [f]
      rw [sum_vertex_polynomial]
      ring

private theorem sum_gap_vertex (g y v : Fin 9 → ℤ) (s q h t u : ℤ) :
    (∑ a : Fin 9, g a * ((s^2 + q + 2*s*v a + 2*(v a)^2) * h +
      2*(s+v a)*t + 2*u + y a * (s^2 + q + 4*s*v a + 6*(v a)^2))) =
      6 * (∑ i : Fin 9, g i * (v i)^2 * y i) +
      2 * (s * (2 * ∑ i : Fin 9, g i * v i * y i) +
        t * (∑ i : Fin 9, g i * v i)) +
      (s^2 + q) * (∑ i : Fin 9, g i * y i) +
      (2*s*t + 2*u) * (∑ i : Fin 9, g i) +
      h * (2 * (∑ i : Fin 9, g i * (v i)^2) + 2*s * (∑ i : Fin 9, g i * v i) +
        (s*s + q) * (∑ i : Fin 9, g i)) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Expand the equality-partition kernel under signed weights. The
right side is precisely the frozen degree-one coefficient, after the
source's finite `doubled_one` and `mixed_numerator_one` rewrites. -/
theorem weighted_kernel_mixedNumerator (d : SimplexData) (j : Fin 10) :
    (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
      (d.gaps a : ℤ) * (d.y b : ℤ) * d.deviations j c *
        d.deviations j e * kernel a b c e) =
      mixedNumerator d j 1 := by
  let g (i : Fin 9) : ℤ := d.gaps i
  let y (i : Fin 9) : ℤ := d.y i
  let v := d.deviations j
  let s := ∑ i : Fin 9, v i
  let q := ∑ i : Fin 9, (v i)^2
  have he (a b c : Fin 9) :
      (∑ e : Fin 9, g a * y b * v c * v e * kernel a b c e) =
        g a * y b * (1 + delta a b) *
          (v c * (1 + delta a c + delta b c) * (s + v a + v b + v c)) := by
    dsimp only [s]
    rw [← contract_three v a b c]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [kernel_factors]
    ring
  have hc (a b : Fin 9) :
      (∑ c : Fin 9, g a * y b * (1 + delta a b) *
        (v c * (1 + delta a c + delta b c) * (s + v a + v b + v c))) =
        g a * y b * (1 + delta a b) * ((s + v a + v b)^2 + q + (v a)^2 + (v b)^2) := by
    rw [← Finset.mul_sum, sum_deviation_pair]
  change (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
    g a * y b * v c * v e * kernel a b c e) = _
  simp_rw [he, hc, sum_y_vertex g y v s q]
  rw [sum_gap_vertex g y v s q]
  rw [mixed_numerator_one, doubled_one, homogeneous_one]
  dsimp only [s, q, g, y, v]
  norm_num [doubled, conv_zero, B1, B2, W0, W1, W2] <;> ring

private theorem fourthMoment_kernel (a b c e : Fin 9) :
    (((fourExponent a b c e 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c e q.succ)) : Nat) : ℝ) /
        (((fourExponent a b c e 0) +
          (List.ofFn (fun q : Fin 8 => fourExponent a b c e q.succ)).sum + 8).factorial : ℝ) =
      (kernel a b c e : ℝ) / ((12 : ℕ).factorial : ℝ) := by
  rw [fourExponent_degree]
  have h : (((fourExponent a b c e 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c e q.succ)) : Nat) : ℝ) =
      (kernel a b c e : ℝ) := by
    exact_mod_cast fourFactorial_kernel a b c e
  rw [h]

/-- Source-only candidate for the exact selected k=1 identity.
It uses the actual measured factorial sum and the bounded finite kernel,
not the analytic identity (M) as a hypothesis. -/
theorem actualMixedExpectation_eq_candidate (d : SimplexData) (j : Fin 10) :
    actualMixedExpectation d j =
      (mixedNumerator d j 1 : ℝ) /
        ((gapTotal d.gaps : ℝ) * d.U * d.L^2 * (10 * 11 * 12)) := by
  rw [actualMixedExpectation_eq_factorial_sum]
  simp_rw [fourthMoment_kernel]
  have hU : (d.U : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.UPos)
  have hL : (d.L : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt d.LPos)
  have hG : (gapTotal d.gaps : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt d.gapsPos)
  have hf : (((12 : ℕ).factorial : ℕ) : ℝ) ≠ 0 := by norm_num
  have ht (a b c e : Fin 9) :
      (gapVertices d a * yVertices d b * bVertices d j c * bVertices d j e) *
        ((kernel a b c e : ℝ) / ((12 : ℕ).factorial : ℝ)) =
      (((d.gaps a : ℤ) * (d.y b : ℤ) * d.deviations j c * d.deviations j e *
        kernel a b c e : ℤ) : ℝ) / ((d.U : ℝ) * d.L^2 * ((12 : ℕ).factorial : ℝ)) := by
    simp only [gapVertices, yVertices, bVertices, Int.cast_mul, Int.cast_natCast]
    field_simp [hU, hL, hf] <;> ring
  simp_rw [ht]
  simp only [← Finset.sum_div, ← Int.cast_sum, weighted_kernel_mixedNumerator]
  norm_num [Nat.factorial]
  field_simp [hG, hU, hL] <;> ring

end

end ImbalancedChen.P2Winner9MixedKOneFiniteCollapse
