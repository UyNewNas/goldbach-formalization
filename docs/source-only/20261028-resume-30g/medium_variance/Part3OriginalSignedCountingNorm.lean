import ImbalancedChen.Part3LichtmanSignedDifferenceMultiplicity
import ImbalancedChen.Part3ActualReciprocalSquarePoisson
import Mathlib.Tactic

/-! SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
The original nonzero signed-difference coefficient is connected to the
existing ACTUAL reciprocal-square Poisson output and the proved finite
multiplicity theorem. Fixed lambda/omega and an output unit phase are
independent of the future completed m variable. No spectral/bare bound
or identification of every original Abel prefix with this kernel is a
premise or conclusion here.
-/

namespace ImbalancedChen.Part3.OriginalSignedCountingNorm20261028
noncomputable section
open Classical Finset
open scoped BigOperators
open LichtmanSignedDifferenceMultiplicity OriginalSmoothPoissonTail
open ActualReciprocalSquarePoissonSourceOnly (fixedUnit atomCoeff)

abbrev Tuple := (ℕ × ℕ × ℕ) × (ℤ × ℤ)

def squareLeft (t : Tuple) : ℕ × ℤ := (t.1.2.1,t.2.1)
def squareRight (t : Tuple) : ℕ × ℤ := (t.1.1,t.2.2)

/-- The crossed difference in the actual reciprocal-square expansion
is exactly the counting output after this explicit ordered relabeling. -/
theorem output_eq_actual_square_output (t : Tuple) :
    output t =
      (ActualReciprocalSquarePoissonSourceOnly.level (squareLeft t) (squareRight t),
       ActualReciprocalSquarePoissonSourceOnly.outputY (t.1.2.2 : ℤ)
         (squareLeft t) (squareRight t)) := by
  simp only [output,LichtmanSignedDifferenceMultiplicity.difference,
    ActualReciprocalSquarePoissonSourceOnly.level,
    ActualReciprocalSquarePoissonSourceOnly.outputY,
    ActualReciprocalSquarePoissonSourceOnly.difference,squareLeft,squareRight]
  exact Prod.ext (Nat.mul_comm _ _) rfl

def tupleCoefficient (A : ℕ) (a : ℤ) (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (t : Tuple) : ℂ :=
  if fixedUnit A a t.1.1 ∧ fixedUnit A a t.1.2.1 then
    atomCoeff lambda omega (squareLeft t) * star (atomCoeff lambda omega (squareRight t))
  else 0

def countCoefficient (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (zy : ℕ × ℤ) : ℂ :=
  eps zy * ∑ t ∈ (sourceCarrier S H F).filter (fun t => output t = zy),
    tupleCoefficient A a lambda omega t

def countingNorm (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ) : ℝ :=
  ∑ zy ∈ (sourceCarrier S H F).image output,
    if (nu : ℤ) ∣ zy.2 then ‖countCoefficient S H F A a lambda omega eps zy‖^2 else 0

private theorem tupleCoefficient_norm_le_one {S H F : ℝ} (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    {t : Tuple} (ht : t ∈ sourceCarrier S H F) :
    ‖tupleCoefficient A a lambda omega t‖ ≤ 1 := by
  obtain ⟨hprod,hne⟩ := mem_filter.mp ht
  obtain ⟨hs,hh⟩ := mem_product.mp hprod
  obtain ⟨hs1,hs2f⟩ := mem_product.mp hs
  obtain ⟨hs2,hf⟩ := mem_product.mp hs2f
  obtain ⟨hh1,hh2⟩ := mem_product.mp hh
  have hleft : ‖atomCoeff lambda omega (squareLeft t)‖ ≤ 1 := by
    simp only [atomCoeff,squareLeft,norm_mul]
    simpa only [one_mul] using
      mul_le_mul (hlambda _ hs2) (homega _ hh1) (norm_nonneg _) zero_le_one
  have hright : ‖atomCoeff lambda omega (squareRight t)‖ ≤ 1 := by
    simp only [atomCoeff,squareRight,norm_mul]
    simpa only [one_mul] using
      mul_le_mul (hlambda _ hs1) (homega _ hh2) (norm_nonneg _) zero_le_one
  unfold tupleCoefficient
  split_ifs
  · simpa only [norm_mul,norm_star,one_mul] using
      mul_le_mul hleft hright (norm_nonneg _) zero_le_one
  · simp

/-- The COMPLEX coefficient, with its original fixed one-bounded
factors, is bounded by the actual positive fibre cardinality. -/
theorem countCoefficient_norm_le_multiplicity (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (zy : ℕ × ℤ) :
    ‖countCoefficient S H F A a lambda omega eps zy‖ ≤
      (multiplicity S H F zy.1 zy.2 : ℝ) := by
  let T := (sourceCarrier S H F).filter (fun t => output t = zy)
  have hsum : ‖∑ t ∈ T, tupleCoefficient A a lambda omega t‖ ≤ (T.card : ℝ) := by
    calc
      _ ≤ ∑ t ∈ T, ‖tupleCoefficient A a lambda omega t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ T, (1 : ℝ) := sum_le_sum (fun t ht =>
        tupleCoefficient_norm_le_one A a lambda omega hlambda homega (mem_filter.mp ht).1)
      _ = _ := by simp
  unfold countCoefficient
  rw [norm_mul]
  calc
    _ ≤ 1*(T.card : ℝ) := mul_le_mul (heps zy) hsum (norm_nonneg _) zero_le_one
    _ = _ := by simp only [one_mul,multiplicity,T]

theorem countingNorm_nonneg (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ) :
    0 ≤ countingNorm S H F A a lambda omega eps nu := by
  unfold countingNorm
  apply sum_nonneg
  intro zy hzy
  split_ifs <;> positivity

/-- The literal real H<1 source is empty. Rounding never creates a
singleton to which the nonempty counting estimate would be applied. -/
theorem sourceCarrier_empty_of_short_H (S H F : ℝ) (hH0 : 0 ≤ H) (hH : H < 1) :
    sourceCarrier S H F = ∅ := by
  have hf : Nat.floor H = 0 := by
    by_contra hn
    have hn1 : 1 ≤ Nat.floor H := Nat.one_le_iff_ne_zero.mpr hn
    have hnR : (1 : ℝ) ≤ Nat.floor H := by exact_mod_cast hn1
    have hfloor := Nat.floor_le hH0
    linarith
  simp [sourceCarrier,frequencyCarrier,hf]

theorem countingNorm_zero_of_short_H (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (nu : ℕ)
    (hH0 : 0 ≤ H) (hH : H < 1) :
    countingNorm S H F A a lambda omega eps nu = 0 := by
  simp only [countingNorm,sourceCarrier_empty_of_short_H S H F hH0 hH,
    image_empty,sum_empty]

theorem countingNorm_le_native_multiplicity (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nu : ℕ) :
    countingNorm S H F A a lambda omega eps nu ≤ multiplicityL2 S H F nu := by
  unfold countingNorm multiplicityL2
  apply sum_le_sum
  intro zy hzy
  split_ifs
  · exact pow_le_pow_left₀ (norm_nonneg _)
      (countCoefficient_norm_le_multiplicity S H F A a lambda omega eps
        hlambda homega heps zy) 2
  · rfl

/-- Original (23), with an explicit finite divisor/harmonic cost and
exact zero beyond nonzero y support. No large-nu +1 is inserted. -/
theorem actual_countingNorm_bound (S H F : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ)
    (hS : 1 ≤ S) (hH : 1 ≤ H) (hF : 1 ≤ F)
    (hlambda : ∀ s ∈ dyadicCarrier S, ‖lambda s‖ ≤ 1)
    (homega : ∀ h ∈ frequencyCarrier H, ‖omega h‖ ≤ 1)
    (heps : ∀ zy, ‖eps zy‖ ≤ 1) (nu : ℕ) (hnu : 0 < nu) :
    countingNorm S H F A a lambda omega eps nu ≤
      576*(divisorMaximum S H F : ℝ)^5*(harmonic (Nat.floor (2*S)) : ℝ)*
        (1+H/S)*(H*S)^2*F/(nu : ℝ) ∧
      (8*F*H*S ≤ (nu : ℝ) → countingNorm S H F A a lambda omega eps nu = 0) := by
  have hn := countingNorm_le_native_multiplicity S H F A a lambda omega eps
    hlambda homega heps nu
  obtain ⟨hbound,hzero⟩ := signedDifference_multiplicityL2_bound S H F hS hH hF nu hnu
  refine ⟨hn.trans hbound,?_⟩
  intro hlarge
  exact le_antisymm (hn.trans_eq (hzero hlarge))
    (countingNorm_nonneg S H F A a lambda omega eps nu)

/-- The genuine completed physical kernel retains inverse(z), all m
and the c-unit gate. The coefficient is independent of m and c. -/
def physicalKernel (M : ℝ) (c : ℕ) (a : ℤ) (zy : ℕ × ℤ) : ℂ :=
  if c.Coprime zy.1 then
    ∑' m : ℤ, frequency M c a zy.2 (zy.1 : ℤ) m else 0

/-- Finite source grouping uses the actual Poisson frequency, without
changing its amplitude or interchanging an unjustified infinite sum. -/
theorem physical_count_source_eq_grouped (S H F : ℝ) (A c : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) (M : ℝ) :
    (∑ t ∈ sourceCarrier S H F, eps (output t)*tupleCoefficient A a lambda omega t*
      physicalKernel M c a (output t)) =
      ∑ zy ∈ (sourceCarrier S H F).image output,
        countCoefficient S H F A a lambda omega eps zy*physicalKernel M c a zy := by
  have hf := sum_fiberwise_of_maps_to (s := sourceCarrier S H F)
    (t := (sourceCarrier S H F).image output) (g := output)
    (fun t ht => mem_image_of_mem output ht)
    (fun t => eps (output t)*tupleCoefficient A a lambda omega t*
      physicalKernel M c a (output t))
  rw [← hf]
  apply sum_congr rfl
  intro zy hzy
  unfold countCoefficient
  simp only [mul_sum,sum_mul]
  apply sum_congr rfl
  intro t ht
  rw [(mem_filter.mp ht).2]

end
end ImbalancedChen.Part3.OriginalSignedCountingNorm20261028
