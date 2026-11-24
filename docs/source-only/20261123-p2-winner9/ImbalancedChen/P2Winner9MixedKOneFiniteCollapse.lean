import ImbalancedChen.P2Winner9BarycentricMixedDegreeOne
import ImbalancedChen.P2Winner9MomentNormalization
import Mathlib.Tactic

/-!
The actual Lebesgue mixed moment of degree one on the eight-dimensional
simplex equals the signed rational coefficient used by the certificate.
The fourth factorial moment is evaluated by the equality partitions of
its four labelled vertices.
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

open scoped BigOperators

abbrev delta := P2Winner9FiniteMomentKernel.delta
abbrev kernel := P2Winner9FiniteMomentKernel.kernel

/-- The degree is exactly four for every four labelled vertices, even
when indices repeat. This finite proof uses no certificate data. -/
theorem fourExponent_degree (a b c d : Fin 9) :
    fourExponent a b c d 0 +
      (List.ofFn (fun q : Fin 8 => fourExponent a b c d q.succ)).sum + 8 = 12 := by
  exact P2Winner9FiniteMomentKernel.fourExponent_degree a b c d

private theorem coreFactorial_eq :
    P2Winner9FiniteMomentKernel.factorial = Nat.factorial := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (n + 1) * P2Winner9FiniteMomentKernel.factorial n = (n + 1).factorial
    rw [Nat.factorial_succ, ih]

/-- The factorial multiplicity is 1,2,4,6 or 24 according to the
equality partition. The 15-term kernel encodes all five cases. -/
theorem fourFactorial_kernel (a b c d : Fin 9) :
    (((fourExponent a b c d 0).factorial *
      factorialProduct (List.ofFn
        (fun q : Fin 8 => fourExponent a b c d q.succ)) : Nat) : ℤ) =
      kernel a b c d := by
  let f := P2Winner9FiniteMomentKernel.fourExponent a b c d
  change Int.ofNat (Nat.factorial (f 0) *
    (List.map Nat.factorial (List.ofFn (fun q : Fin 8 => f q.succ))).prod) = _
  have h := P2Winner9FiniteMomentKernel.fourFactorial_kernel a b c d
  rw [P2Winner9FiniteMomentKernel.factorialProduct, coreFactorial_eq] at h
  exact h

/-- A bounded n=1 complete-homogeneous coefficient, independent of
moment calculus. -/
theorem homogeneous_one (y : Fin 9 → Nat) :
    (homogeneous y 1 : ℤ) = ∑ i : Fin 9, (y i : ℤ) := by
  classical
  let basis : Fin 9 → Fin 9 → Fin 2 := fun i q => if q = i then 1 else 0
  let degree : (Fin 9 → Fin 2) → ℕ := fun α => ∑ q, (α q).val
  let value : (Fin 9 → Fin 2) → ℕ := fun α => ∏ q, y q ^ (α q).val
  have basis_degree (i : Fin 9) : degree (basis i) = 1 := by
    simp [degree, basis, apply_ite Fin.val, Finset.sum_ite_eq']
  have basis_value (i : Fin 9) : value (basis i) = y i := by
    unfold value
    trans ∏ q : Fin 9, if q = i then y q else 1
    · apply Finset.prod_congr rfl
      intro q _
      by_cases h : q = i <;> simp [basis, h]
    · simp
  have basis_injective : Function.Injective basis := by
    intro i j h
    by_contra hne
    have hi := congrFun h i
    simp [basis, hne] at hi
  have basis_cover (α : Fin 9 → Fin 2) (hα : degree α = 1) : ∃ i, basis i = α := by
    obtain ⟨i, hi⟩ : ∃ i, α i = 1 := by
      by_contra! h
      have hz (q : Fin 9) : (α q).val = 0 := by
        have hne : (α q).val ≠ 1 := fun hv => h q (Fin.ext hv)
        have hlt := (α q).isLt
        omega
      simp [degree, hz] at hα
    refine ⟨i, funext fun q => ?_⟩
    by_cases hqi : q = i
    · subst q
      simp [basis, hi]
    · have hle : (α i).val + (α q).val ≤ degree α := by
        simpa [degree, Finset.sum_pair (Ne.symm hqi)] using
          (Finset.sum_le_sum_of_subset (f := fun r : Fin 9 => (α r).val)
            (Finset.subset_univ ({i, q} : Finset (Fin 9))))
      have hval : (α i).val = 1 := by simp [hi]
      have hz : α q = 0 := Fin.ext (by change (α q).val = 0; omega)
      simp [basis, hqi, hz]
  have hset : Finset.univ.filter (fun α => degree α = 1) =
      Finset.univ.image basis := by
    ext α
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨basis_cover α, fun ⟨i, hi⟩ => hi ▸ basis_degree i⟩
  have hsum : homogeneous y 1 = ∑ i : Fin 9, y i := by
    change (∑ α : Fin 9 → Fin 2, if degree α = 1 then value α else 0) = _
    rw [← Finset.sum_filter, hset, Finset.sum_image basis_injective.injOn]
    simp [basis_value]
  exact_mod_cast hsum

private theorem sumFin_eq_sum {n : Nat} (f : Fin n → ℤ) :
    P2Winner9FiniteMomentKernel.sumFin f = ∑ i, f i := by
  exact Fin.sum_ofFn f

/-- Expand the equality-partition kernel under signed weights. The
right side is precisely the frozen degree-one coefficient, after the
source's finite `doubled_one` and `mixed_numerator_one` rewrites. -/
theorem weighted_kernel_mixedNumerator (d : SimplexData) (j : Fin 10) :
    (∑ a : Fin 9, ∑ b : Fin 9, ∑ c : Fin 9, ∑ e : Fin 9,
      (d.gaps a : ℤ) * (d.y b : ℤ) * d.deviations j c *
        d.deviations j e * kernel a b c e) =
      mixedNumerator d j 1 := by
  rw [mixed_numerator_one, doubled_one, homogeneous_one]
  have h := P2Winner9FiniteMomentKernel.weighted_kernel_expansion
    (fun i => (d.gaps i : ℤ)) (fun i => (d.y i : ℤ)) (d.deviations j)
  simp only [sumFin_eq_sum] at h
  refine h.trans ?_
  norm_num [doubled, conv_zero, B1, B2, W0, W1, W2, Nat.choose]

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

/-- Normalize the measured factorial sum to the certificate's exact
signed degree-one numerator and scales. -/
theorem actualMixedExpectation_eq_candidate (d : SimplexData) (j : Fin 10) :
    actualMixedExpectation d j =
      (mixedNumerator d j 1 : ℝ) /
        ((gapTotal d.gaps : ℝ) * d.U * d.L^2 * (10 * 11 * 12)) := by
  rw [actualMixedExpectation_eq_factorial_sum]
  simp_rw [fourthMoment_kernel]
  simpa only [gapVertices, yVertices, bVertices] using
    (P2Winner9MomentNormalization.from_weighted_sum (R := ℝ)
      d.gaps d.y (d.deviations j) (gapTotal d.gaps) d.U d.L
      (mixedNumerator d j 1) (weighted_kernel_mixedNumerator d j))

/-- The measured moment is the real image of the candidate defined for the
rational mixed-term checker. -/
theorem actualMixedExpectation_eq_momentOneCandidate (d : SimplexData) (j : Fin 10) :
    actualMixedExpectation d j = (momentOneCandidate d j : ℝ) := by
  rw [actualMixedExpectation_eq_candidate]
  unfold momentOneCandidate
  push_cast
  rfl

end

end ImbalancedChen.P2Winner9MixedKOneFiniteCollapse
