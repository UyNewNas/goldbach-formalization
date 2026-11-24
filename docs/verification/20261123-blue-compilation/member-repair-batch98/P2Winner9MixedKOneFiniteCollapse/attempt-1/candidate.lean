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

private theorem closed_four_labels :
    (∀ a b c d : Fin 9,
    fourExponent a b c d 0 +
      (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)).sum + 8 = 12) ∧
    (∀ a b c d : Fin 9,
    (((fourExponent a b c d 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c d q.succ)) : Nat) : ℤ) =
      kernel a b c d) := by
  decide +kernel

/-- The degree is exactly four for every four labelled vertices, even
when indices repeat. This finite proof uses no certificate data. -/
theorem fourExponent_degree (a b c d : Fin 9) :
    fourExponent a b c d 0 +
      (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)).sum + 8 = 12 := by
  exact closed_four_labels.1 a b c d

/-- The factorial multiplicity is 1,2,4,6 or 24 according to the
equality partition. The 15-term kernel encodes all five cases. -/
theorem fourFactorial_kernel (a b c d : Fin 9) :
    (((fourExponent a b c d 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c d q.succ)) : Nat) : ℤ) =
      kernel a b c d := by
  exact closed_four_labels.2 a b c d

/-- A bounded n=1 complete-homogeneous coefficient, independent of
moment calculus. -/
theorem homogeneous_one (y : Fin 9 → Nat) :
    (homogeneous y 1 : ℤ) = ∑ i : Fin 9, (y i : ℤ) := by
  classical
  let oneHot (i : Fin 9) : Fin 9 → Fin 2 :=
    fun r => if r = i then 1 else 0
  have hsum (i : Fin 9) : (∑ r : Fin 9, (oneHot i r).val) = 1 := by
    simp [oneHot, apply_ite]
  have hprod (i : Fin 9) :
      (∏ r : Fin 9, y r ^ (oneHot i r).val) = y i := by
    calc
      _ = ∏ r : Fin 9, if r = i then y r else 1 := by
        apply Finset.prod_congr rfl
        intro r hr
        by_cases h : r = i <;> simp [oneHot, h]
      _ = _ := by simp
  have hnat : homogeneous y 1 = ∑ i : Fin 9, y i := by
    unfold homogeneous
    change (∑ α : Fin 9 → Fin 2,
      if (∑ r : Fin 9, (α r).val) = 1 then
        ∏ r : Fin 9, y r ^ (α r).val else 0) = ∑ i : Fin 9, y i
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun i _ => oneHot i) ?_ ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsum i⟩
    · intro i hi k hk heq
      by_contra hne
      have hv := congrArg (fun f : Fin 9 → Fin 2 => (f i).val) heq
      have : (1 : ℕ) = 0 := by simpa [oneHot, hne] using hv
      omega
    · intro α hα
      have htotal : (∑ r : Fin 9, (α r).val) = 1 :=
        (Finset.mem_filter.mp hα).2
      have hsome : ∃ i : Fin 9, α i ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hz : (∑ r : Fin 9, (α r).val) = 0 := by simp [hn]
        omega
      obtain ⟨i, hi⟩ := hsome
      have hione : (α i).val = 1 := by
        have hlt := (α i).isLt
        have hne : (α i).val ≠ 0 := by
          intro hz
          apply hi
          apply Fin.ext
          simpa using hz
        omega
      have hrest : (∑ r ∈ (Finset.univ : Finset (Fin 9)).erase i,
          (α r).val) = 0 := by
        have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 9))
          (fun r => (α r).val) (Finset.mem_univ i)
        rw [htotal, hione] at he
        omega
      refine ⟨i, Finset.mem_univ i, ?_⟩
      funext r
      by_cases hr : r = i
      · subst r
        simp only [oneHot, if_pos rfl]
        apply Fin.ext
        simpa using hione.symm
      · simp only [oneHot, if_neg hr]
        have hmem : r ∈ (Finset.univ : Finset (Fin 9)).erase i := by
          simp [hr]
        have hle := Finset.single_le_sum
          (fun r (_ : r ∈ (Finset.univ : Finset (Fin 9)).erase i) =>
            Nat.zero_le (α r).val) hmem
        rw [hrest] at hle
        apply Fin.ext
        simpa using (Nat.eq_zero_of_le_zero hle).symm
    · intro i hi
      exact (hprod i).symm
  exact_mod_cast hnat

/-- Expand the equality-partition kernel under signed weights. The
right side is precisely the frozen degree-one coefficient, after the
source's finite `doubled_one` and `mixed_numerator_one` rewrites. -/
theorem weighted_kernel_mixedNumerator (d : SimplexData) (j : Fin 10) :
    (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
      (d.gaps a : ℤ) * (d.y b : ℤ) * d.deviations j c *
        d.deviations j e * kernel a b c e) =
      mixedNumerator d j 1 := by
  classical
  have sep2 (F : Fin 9 → Fin 9 → ℤ)
      (f g : Fin 9 → ℤ) (k : ℤ)
      (hp : ∀ a b, F a b = k * f a * g b) :
      (∑ a : Fin 9, ∑ b : Fin 9, F a b) = k * (∑ i : Fin 9, f i) * (∑ i : Fin 9, g i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact hp a b
  have sep3 (F : Fin 9 → Fin 9 → Fin 9 → ℤ)
      (f g h : Fin 9 → ℤ) (k : ℤ)
      (hp : ∀ a b c, F a b c = k * f a * g b * h c) :
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, F a b c) = k * (∑ i : Fin 9, f i) * (∑ i : Fin 9, g i) * (∑ i : Fin 9, h i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    exact hp a b c
  have sep4 (F : Fin 9 → Fin 9 → Fin 9 → Fin 9 → ℤ)
      (f g h r : Fin 9 → ℤ) (k : ℤ)
      (hp : ∀ a b c e, F a b c e = k * f a * g b * h c * r e) :
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9, F a b c e) = k * (∑ i : Fin 9, f i) * (∑ i : Fin 9, g i) * (∑ i : Fin 9, h i) * (∑ i : Fin 9, r i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro e he
    exact hp a b c e
  have hk (g y z : Fin 9 → ℤ) :
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
        g a * y b * z c * z e * kernel a b c e) =
      (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i)^2 +
      (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i)^2 +
      2 * (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) +
      2 * (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i * y i) * (∑ i : Fin 9, z i) +
      (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i^2) +
      (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i^2) +
      2 * (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, z i * y i) +
      4 * (∑ i : Fin 9, g i * z i * y i) * (∑ i : Fin 9, z i) +
      2 * (∑ i : Fin 9, g i * z i^2) * (∑ i : Fin 9, y i) +
      2 * (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i^2 * y i) +
      6 * (∑ i : Fin 9, g i * z i^2 * y i) := by
    have t0 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9, g a * y b * z c * z e) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep4
        (fun a b c e => g a * y b * z c * z e)
        g y z z 1 (by intro a b c e; ring)
    have t1 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y a * z b * z c) =
        (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y a * z b * z c)
        (fun a => g a * y a) z z 1 (by intro a b c; ring)
    have t2 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z a * z c) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z a * z c)
        (fun a => g a * z a) y z 1 (by intro a b c; ring)
    have t3 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z c * z a) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z c * z a)
        (fun a => g a * z a) y z 1 (by intro a b c; ring)
    have t4 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z b * z c) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z b * z c)
        g (fun b => z b * y b) z 1 (by intro a b c; ring)
    have t5 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z c * z b) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z c * z b)
        g (fun b => z b * y b) z 1 (by intro a b c; ring)
    have t6 : (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, g a * y b * z c^2) =
        (∑ i : Fin 9, g i) * (∑ i : Fin 9, y i) * (∑ i : Fin 9, z i^2) := by
      simpa only [one_mul] using sep3
        (fun a b c => g a * y b * z c^2)
        g y (fun c => z c^2) 1 (by intro a b c; ring)
    have t7 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y a * z b^2) =
        (∑ i : Fin 9, g i * y i) * (∑ i : Fin 9, z i^2) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y a * z b^2)
        (fun a => g a * y a) (fun b => z b^2) 1 (by intro a b; ring)
    have t8 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z a * z b) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, z i * y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z a * z b)
        (fun a => g a * z a) (fun b => z b * y b) 1 (by intro a b; ring)
    have t9 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z b * z a) =
        (∑ i : Fin 9, g i * z i) * (∑ i : Fin 9, z i * y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z b * z a)
        (fun a => g a * z a) (fun b => z b * y b) 1 (by intro a b; ring)
    have t10 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y a * z a * z b * 2) =
        2 * (∑ i : Fin 9, g i * z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y a * z a * z b * 2)
        (fun a => g a * z a * y a) z 2 (by intro a b; ring)
    have t11 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y a * z b * z a * 2) =
        2 * (∑ i : Fin 9, g i * z i * y i) * (∑ i : Fin 9, z i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y a * z b * z a * 2)
        (fun a => g a * z a * y a) z 2 (by intro a b; ring)
    have t12 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z a^2 * 2) =
        2 * (∑ i : Fin 9, g i * z i^2) * (∑ i : Fin 9, y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z a^2 * 2)
        (fun a => g a * z a^2) y 2 (by intro a b; ring)
    have t13 : (∑ a : Fin 9, ∑ b : Fin 9, g a * y b * z b^2 * 2) =
        2 * (∑ i : Fin 9, g i) * (∑ i : Fin 9, z i^2 * y i) := by
      simpa only [one_mul] using sep2
        (fun a b => g a * y b * z b^2 * 2)
        g (fun b => z b^2 * y b) 2 (by intro a b; ring)
    have t14 : (∑ a : Fin 9, g a * y a * z a^2 * 6) =
        6 * (∑ a : Fin 9, g a * z a^2 * y a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    conv_lhs =>
      simp [kernel, delta, Finset.sum_add_distrib, Finset.sum_mul,
        Finset.mul_sum, mul_add, add_mul, mul_ite]
    simp only [mul_assoc, ← pow_two] at t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ⊢
    linear_combination t0 + t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 + t9 + t10 + t11 + t12 + t13 + t14
  rw [hk, mixed_numerator_one, doubled_one, homogeneous_one]
  simp [doubled, conv_zero, B1, B2, W0, W1, W2] <;> ring

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
  have hsum :
      (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
        (d.gaps a : ℝ) * (d.y b : ℝ) * (d.deviations j c : ℝ) *
          (d.deviations j e : ℝ) * (kernel a b c e : ℝ)) =
        (mixedNumerator d j 1 : ℝ) := by
    exact_mod_cast (weighted_kernel_mixedNumerator d j)
  have hterm (a b c e : Fin 9) :
      (gapVertices d a * yVertices d b *
        bVertices d j c * bVertices d j e) *
          ((kernel a b c e : ℝ) / ((12 : ℕ).factorial : ℝ)) =
      ((d.gaps a : ℝ) * (d.y b : ℝ) * (d.deviations j c : ℝ) *
        (d.deviations j e : ℝ) * (kernel a b c e : ℝ)) /
          ((d.U : ℝ) * (d.L : ℝ)^2 * ((12 : ℕ).factorial : ℝ)) := by
    simp only [gapVertices, yVertices, bVertices, div_eq_mul_inv,
      mul_inv_rev, inv_pow]
    ring
  simp_rw [hterm]
  simp_rw [← Finset.sum_div]
  rw [hsum]
  norm_num [Nat.factorial]
  field_simp [hU, hL, hG]
  <;> ring

end

end ImbalancedChen.P2Winner9MixedKOneFiniteCollapse
