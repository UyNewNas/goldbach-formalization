import ImbalancedChen.P3ActualEvenLowerIntegerRho
import ImbalancedChen.P3ActualRetainedRoughEulerMass
import ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment
import Mathlib.Tactic

/-!
P3.6, fixed manuscript UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b, PP completion §§1,3(T),4(F).

The previous physical Euler estimate used ODD first-exit UPPER rho.
The actual quotient P5 source is EVEN first-exit LOWER and chooses the
opposite Rosser sign branch. This file derives a genuinely separate
finite physical totient budget for that same even-lower integer rho.

In contrast to a rank-cap hypothesis, the rough mass uses only the
ACTUAL squarefree prime carrier and its finite Euler product. The small
factor uses only the strict ACTIVE Rosser level, not all displayed small
supports. No assertion identifies this with the final compiler rho_N,
or bounds the Euler product by a uniform power of log N. No PP count
or arithmetic discrepancy is assumed or paid. SOURCE_ONLY, uncompiled.
-/

namespace ImbalancedChen.P3ActualEvenLowerEulerMass
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualEvenLowerIntegerRho
open ImbalancedChen.P3ActualRawActiveLevelTotientCap
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualRawPhysicalRhoTotientCap
open ImbalancedChen.P3ActualSignedPairTotientCap
open ImbalancedChen.P3ActualPhysicalTotientConvolution
open ImbalancedChen.P3ActualWholeProductPrimitiveMeanPayment

/-- Exact positive reciprocal totient mass for the REAL even-first-exit
LOWER physical source, without the preceding odd-exit upper coefficient. -/
def actualEvenLowerRealMass (retainEven : List ℕ → Bool)
    (N cap : ℕ) (w z L : ℝ) : ℝ :=
  ∑ q ∈ actualLowerSmallRoughModuli retainEven N cap w z,
    |actualLowerSmallRoughRho retainEven N cap w z L q| *
      (Nat.totient q : ℝ)⁻¹

/-- Every actual EVEN retained rough modulus is squarefree, with all
prime factors from the same original roughPrimeUniverse. No retention
rank, product-cap, sieve sign, or analytic prime estimate is presumed. -/
theorem actual_even_retained_rough_totient_mass_le_euler
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z : ℝ) :
    (∑ b ∈ fixedEvenRoughSupport retainEven N cap w z,
      (Nat.totient b : ℝ)⁻¹) ≤ roughEulerMass N cap w z := by
  classical
  let S := fixedEvenRoughSupport retainEven N cap w z
  let P := (roughPrimeUniverse N cap w z).toFinset
  have hsq : ∀ b ∈ S, Squarefree b := by
    intro b hb
    exact fixedEvenRoughSupport_squarefree retainEven N cap w z hb
  have hprime : ∀ b ∈ S, b.primeFactors ⊆ P := by
    intro b hb p hp
    change p ∈ (roughPrimeUniverse N cap w z).toFinset
    simpa using fixedEvenRoughSupport_primeFactors_mem
      retainEven N cap w z hb hp
  have h := squarefree_support_mass_le_explicit_euler S P hsq hprime
  simpa only [S, P, roughPrimeUniverse_toFinset, roughEulerMass] using h

/-- The same finite product controls the literal EVEN-EXIT LOWER
physical rho, with its actual sign-sensitive Rosser branch.
Only nonzero small factors require a<L; a displayed Rosser divisor
above L is not given a fictitious polynomial cap. -/
theorem actual_even_lower_real_mass_le_euler
    (retainEven : List ℕ → Bool) (N cap A : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) :
    actualEvenLowerRealMass retainEven N cap w z L ≤
      logTotientCap A * roughEulerMass N cap w z := by
  classical
  let s := actualSmallRosserSupport N cap w
  let r := fixedEvenRoughSupport retainEven N cap w z
  let t := activeSmallRosserByLevel N cap w L
  let Q := actualLowerSmallRoughModuli retainEven N cap w z
  let Q' := smallRoughModuli t r
  let rho := actualLowerSmallRoughRho retainEven N cap w z L
  let F : ℕ → ℝ := fun q => |rho q| * (Nat.totient q : ℝ)⁻¹
  have hs : ∀ a ∈ t, SmallPrimeSupportedAt w a := by
    intro a ha
    exact actualSmallRosserSupport_smallPrimeSupportedAt N cap w
      (Finset.mem_filter.mp ha).1
  have hr : ∀ b ∈ r, RoughPrimeSupportedAt w b := by
    intro b hb
    exact fixedEvenRoughSupport_roughPrimeSupportedAt retainEven N cap w z hb
  have htcap : t ⊆ Finset.Icc 1 A := by
    intro a ha
    have ha0 : 0 < a := Nat.pos_of_ne_zero (hs a ha).1
    have haReal : (a : ℝ) ≤ (A : ℝ) :=
      (le_of_lt (Finset.mem_filter.mp ha).2).trans hLA
    exact Finset.mem_Icc.mpr ⟨ha0, by exact_mod_cast haReal⟩
  have hqsub : Q' ⊆ Q := by
    change (smallRoughPairs t r).image (fun x => x.1 * x.2) ⊆
      (smallRoughPairs s r).image (fun x => x.1 * x.2)
    apply Finset.image_mono
    change t.product r ⊆ s.product r
    exact Finset.product_mono (Finset.filter_subset _ _) (Finset.Subset.rfl)
  have hzero : ∀ q ∈ Q, q ∉ Q' → F q = 0 := by
    intro q hq hnot
    have hrho : rho q = 0 := by
      by_contra hnz
      obtain ⟨a, ha, b, hb, hqeq, hlt, hc⟩ :=
        actualLowerSmallRoughRho_ne_zero_factors
          retainEven N cap w z L hnz
      apply hnot
      change q ∈ smallRoughModuli t r
      apply Finset.mem_image.mpr
      refine ⟨(a, b), Finset.mem_product.mpr ?_, hqeq.symm⟩
      exact ⟨Finset.mem_filter.mpr ⟨ha, hlt⟩, hb⟩
    simp [F, hrho]
  have hdrop : (∑ q ∈ Q, F q) = ∑ q ∈ Q', F q :=
    (Finset.sum_subset hqsub hzero).symm
  change (∑ q ∈ Q, F q) ≤ _
  rw [hdrop, sum_smallRoughModuli hs hr F]
  calc
    (∑ x ∈ smallRoughPairs t r, F (x.1 * x.2)) ≤
      ∑ x ∈ smallRoughPairs t r,
        (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hx
      have hpos : 0 < x.1 ∧ 0 < x.2 :=
        ⟨Nat.pos_of_ne_zero (hs x.1 ha).1,
          Nat.pos_of_ne_zero (hr x.2 hb).1⟩
      have hcoeff : |rho (x.1 * x.2)| ≤ 1 :=
        actualLowerSmallRoughRho_abs_le_one retainEven N cap w z L _
      calc
        F (x.1 * x.2) ≤ (Nat.totient (x.1 * x.2) : ℝ)⁻¹ := by
          simpa only [F, one_mul] using
            mul_le_mul_of_nonneg_right hcoeff (by positivity)
        _ ≤ (Nat.totient x.1 : ℝ)⁻¹ *
            (Nat.totient x.2 : ℝ)⁻¹ :=
          reciprocal_totient_product_le x.1 x.2 hpos.1 hpos.2
    _ ≤ ∑ x ∈ (Finset.Icc 1 A).product r,
          (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹ := by
      change (∑ x ∈ t.product r,
        (Nat.totient x.1 : ℝ)⁻¹ * (Nat.totient x.2 : ℝ)⁻¹) ≤ _
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.product_mono htcap (Finset.Subset.rfl))
        (fun x hx hnot => by positivity)
    _ = (∑ a ∈ Finset.Icc 1 A, (Nat.totient a : ℝ)⁻¹) *
        (∑ b ∈ r, (Nat.totient b : ℝ)⁻¹) := by
      rw [Finset.sum_product, Finset.sum_mul_sum]
    _ ≤ logTotientCap A *
          (∑ b ∈ r, (Nat.totient b : ℝ)⁻¹) := by
      exact mul_le_mul_of_nonneg_right
        (sum_reciprocal_totient_le_log A)
        (Finset.sum_nonneg (fun b hb => by positivity))
    _ ≤ logTotientCap A * roughEulerMass N cap w z := by
      exact mul_le_mul_of_nonneg_left
        (actual_even_retained_rough_totient_mass_le_euler
          retainEven N cap w z) (logTotientCap_nonneg A)

/-- Genuine INTEGER even-lower rho in the original COMPLEX physical
reciprocal-totient ledger. No replacement real, odd or unsigned rho. -/
theorem actual_even_lower_integer_physical_mass_eq
    (retainEven : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) :
    physicalReciprocalTotientMass
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualEvenLowerIntegerRho retainEven N cap w z L) =
    actualEvenLowerRealMass retainEven N cap w z L := by
  unfold physicalReciprocalTotientMass actualEvenLowerRealMass
  apply Finset.sum_congr rfl
  intro q hq
  have hcast : (actualEvenLowerIntegerRho retainEven N cap w z L q : ℂ) =
      ((actualEvenLowerIntegerRho retainEven N cap w z L q : ℝ) : ℂ) := by
    norm_cast
  rw [hcast, norm_mul, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (show 0 ≤ (Nat.totient q : ℝ)⁻¹ by positivity)]
  rw [actualEvenLowerIntegerRho_cast]

/-- This is the same INTEGER even-lower rho present in the production
P5 pair rows, at the original physical q and the exact Euler phi(q).
The remaining rough Euler factor is FINITE, not a proved log^E(N). -/
theorem actual_even_lower_integer_physical_mass_le_euler
    (retainEven : List ℕ → Bool) (N cap A : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) :
    physicalReciprocalTotientMass
      (actualLowerSmallRoughModuli retainEven N cap w z)
      (actualEvenLowerIntegerRho retainEven N cap w z L) ≤
      logTotientCap A * roughEulerMass N cap w z := by
  rw [actual_even_lower_integer_physical_mass_eq]
  exact actual_even_lower_real_mass_le_euler
    retainEven N cap A w z L hLA

/-- Full COMPLETE-product B, exact gcd(B,q)=1 filter, exact signed
INTEGER even-lower rho and true physical phi(q). This is a MEAN budget
only; it neither asserts PP nor pays the complete product=B diagonal. -/
theorem actual_even_lower_primitive_mean_le_euler
    (retainEven : List ℕ → Bool) (N cap A B : ℕ) (w z L : ℝ)
    (hLA : L ≤ (A : ℝ)) :
    ‖primitivePhysicalMean B
        (actualLowerSmallRoughModuli retainEven N cap w z)
        (actualEvenLowerIntegerRho retainEven N cap w z L)‖ ≤
      logTotientCap A * roughEulerMass N cap w z := by
  exact (primitivePhysicalMean_norm_le B
    (actualLowerSmallRoughModuli retainEven N cap w z)
    (actualEvenLowerIntegerRho retainEven N cap w z L)).trans
    (actual_even_lower_integer_physical_mass_le_euler
      retainEven N cap A w z L hLA)

end
end ImbalancedChen.P3ActualEvenLowerEulerMass
