import ImbalancedChen.Part3OriginalSignedCountingNorm
import ImbalancedChen.P0RamanujanMultiplicativeGcdBound
import Mathlib.Tactic

/-!
Source only; uncompiled; zero formal credit.

The actual m=0 branch of the reciprocal-square Poisson kernel in the
medium completion, section 7 before (24). This is an estimate of the
physical frequency, not an assumed spectral-return inequality. The
existing finite Ramanujan identity and gcd mean are sufficient for this
branch. The nonzero completed frequencies remain an explicit remainder.
-/

namespace ImbalancedChen.Part3.ActualZeroPoissonKernel20261102
noncomputable section
open Classical Finset CommonSmoothCutoff OriginalSmoothPoissonTail
open OriginalSmoothPoissonTail.Physical OriginalSmoothPoissonTail.Physical.ZeroMode
open RamanujanMultiplicativeGcdBound20261025a
open OriginalSignedCountingNorm20261028 LichtmanSignedDifferenceMultiplicity
open scoped BigOperators SchwartzMap FourierTransform

def smoothModuli (C : ℝ) : Finset ℕ := Ioc 0 (Nat.floor (3*C))

def zeroFourierMass : ℝ := ‖(𝓕 dyadicCutoffSchwartz) 0‖

def zeroKernel (C D : ℝ) (a : ℤ) (zy : ℕ × ℤ) : ℂ :=
  ∑ c ∈ smoothModuli C, (scaledDyadicCutoff C c : ℂ) *
    (if c.Coprime zy.1 then frequency D c a zy.2 (zy.1 : ℤ) 0 else 0)

def nonzeroKernel (C D : ℝ) (a : ℤ) (zy : ℕ × ℤ) : ℂ :=
  ∑ c ∈ smoothModuli C, (scaledDyadicCutoff C c : ℂ) *
    (if c.Coprime zy.1 then
      ∑' m : ℤ, if m = 0 then 0 else frequency D c a zy.2 (zy.1 : ℤ) m
     else 0)

def completedKernel (C D : ℝ) (a : ℤ) (zy : ℕ × ℤ) : ℂ :=
  ∑ c ∈ smoothModuli C, (scaledDyadicCutoff C c : ℂ) *
    OriginalSignedCountingNorm20261028.physicalKernel D c a zy

/-- The natural cutoff is exhaustive, not a truncation of the c sum. -/
theorem mem_smoothModuli_of_cutoff_ne_zero {C : ℝ} (hC : 0 < C) (c : ℕ)
    (hc : scaledDyadicCutoff C c ≠ 0) : c ∈ smoothModuli C := by
  obtain ⟨hlo,hhi⟩ := scaledDyadicCutoff_mem_Icc_of_ne_zero hC hc
  have hcR : (0 : ℝ) < c := lt_of_lt_of_le (half_pos hC) hlo
  exact mem_Ioc.mpr ⟨by exact_mod_cast hcR, Nat.le_floor hhi⟩

/-- Absolute summability of the actual Poisson series licenses the split.
The c-unit gate and inverse(z) remain unchanged in the nonzero branch. -/
theorem completedKernel_eq_zero_add_nonzero {D : ℝ} (hD : 0 < D)
    (C : ℝ) (a : ℤ) (zy : ℕ × ℤ) :
    completedKernel C D a zy = zeroKernel C D a zy + nonzeroKernel C D a zy := by
  unfold completedKernel zeroKernel nonzeroKernel
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro c hc
  have hcpos : 0 < c := (mem_Ioc.mp hc).1
  letI : NeZero c := ⟨hcpos.ne'⟩
  by_cases hcz : c.Coprime zy.1
  · have hz : IsUnit ((zy.1 : ℤ) : ZMod c) := by
      apply (isUnit_intCast_iff_natAbs_coprime (c := c) (zy.1 : ℤ)).mpr
      simpa only [Int.natAbs_natCast] using hcz.symm
    have hs := (completed_summable_norm (c := c) hD a zy.2 (zy.1 : ℤ) hz).of_norm
    simp only [OriginalSignedCountingNorm20261028.physicalKernel,if_pos hcz]
    rw [hs.tsum_eq_add_tsum_ite 0, mul_add]
  · simp only [OriginalSignedCountingNorm20261028.physicalKernel,if_neg hcz,
      mul_zero,add_zero]

private theorem weighted_zero_frequency_le {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (a : ℤ) (zy : ℕ × ℤ) {c : ℕ} (hc : 0 < c) :
    ‖(scaledDyadicCutoff C c : ℂ) *
      (if c.Coprime zy.1 then frequency D c a zy.2 (zy.1 : ℤ) 0 else 0)‖ ≤
      (2*D*zeroFourierMass/C) * (c.gcd (a*zy.2).natAbs : ℝ) := by
  letI : NeZero c := ⟨hc.ne'⟩
  by_cases hcz : c.Coprime zy.1
  · rw [if_pos hcz]
    by_cases hw : scaledDyadicCutoff C c = 0
    · simp only [hw,Complex.ofReal_zero,zero_mul,norm_zero]
      unfold zeroFourierMass
      positivity
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hlo := (scaledDyadicCutoff_mem_Icc_of_ne_zero hC hw).1
    have hdiv : D/(c : ℝ) ≤ 2*D/C := by
      apply (div_le_div_iff₀ hcR hC).mpr
      nlinarith only [mul_nonneg hD (show 0 ≤ 2*(c : ℝ)-C by linarith)]
    have hw0 := scaledDyadicCutoff_nonneg C c
    have hw1 := scaledDyadicCutoff_le_one C c
    rw [frequency_zero_eq_ramanujan, norm_mul, norm_mul, norm_smul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0,
      Real.norm_eq_abs, abs_of_nonneg (div_nonneg hD hcR.le)]
    change scaledDyadicCutoff C c *
      (D/(c : ℝ)*zeroFourierMass*‖ramanujan c (a*zy.2)‖) ≤ _
    calc
      _ ≤ 1 * (D/(c : ℝ)*zeroFourierMass*‖ramanujan c (a*zy.2)‖) :=
        mul_le_mul_of_nonneg_right hw1 (by unfold zeroFourierMass; positivity)
      _ ≤ 1 * ((2*D/C)*zeroFourierMass*(c.gcd (a*zy.2).natAbs : ℝ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (mul_le_mul_of_nonneg_right hdiv (norm_nonneg _))
            (norm_ramanujan_le_gcd c (a*zy.2)) (norm_nonneg _) (by
              unfold zeroFourierMass
              positivity)) zero_le_one
      _ = _ := by ring
  · simp only [if_neg hcz,mul_zero,norm_zero]
    unfold zeroFourierMass
    positivity

/-- Genuine physical m=0 estimate. The modulus average uses the already
proved gcd mean; neither Kuznetsov nor a desired kernel bound is a premise.
It is uniform in positive C, including empty sub-unit modulus supports. -/
theorem zeroKernel_norm_le {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (a : ℤ) (zy : ℕ × ℤ) (hay : a*zy.2 ≠ 0) :
    ‖zeroKernel C D a zy‖ ≤
      6*D*zeroFourierMass*((a*zy.2).natAbs.divisors.card : ℝ) := by
  have hn : (a*zy.2).natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hay
  have hgcd :
      (∑ c ∈ smoothModuli C, (c.gcd (a*zy.2).natAbs : ℝ)) ≤
        (Nat.floor (3*C) : ℝ)*((a*zy.2).natAbs.divisors.card : ℝ) := by
    simpa only [smoothModuli,Nat.gcd_comm,Nat.cast_sum,Nat.cast_mul] using
      (show ((∑ c ∈ Ioc 0 (Nat.floor (3*C)), (a*zy.2).natAbs.gcd c) : ℝ) ≤
          ((Nat.floor (3*C) * (a*zy.2).natAbs.divisors.card : ℕ) : ℝ) by
        exact_mod_cast ActualLargeGCDBetaMass.sum_gcd_le hn (Nat.floor (3*C)))
  have hfactor : 0 ≤ 2*D*zeroFourierMass/C := by
    unfold zeroFourierMass
    positivity
  calc
    ‖zeroKernel C D a zy‖ ≤
        ∑ c ∈ smoothModuli C, ‖(scaledDyadicCutoff C c : ℂ) *
          (if c.Coprime zy.1 then frequency D c a zy.2 (zy.1 : ℤ) 0 else 0)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ c ∈ smoothModuli C,
        (2*D*zeroFourierMass/C)*(c.gcd (a*zy.2).natAbs : ℝ) :=
      sum_le_sum (fun c hc => weighted_zero_frequency_le hC hD a zy (mem_Ioc.mp hc).1)
    _ = (2*D*zeroFourierMass/C)*
        ∑ c ∈ smoothModuli C, (c.gcd (a*zy.2).natAbs : ℝ) := (mul_sum _ _ _).symm
    _ ≤ (2*D*zeroFourierMass/C)*
        ((Nat.floor (3*C) : ℝ)*((a*zy.2).natAbs.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hgcd hfactor
    _ ≤ (2*D*zeroFourierMass/C)*
        ((3*C)*((a*zy.2).natAbs.divisors.card : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)) hfactor
    _ = _ := by field_simp [hC.ne']; ring

def outputCarrier (S H F : ℝ) : Finset (ℕ × ℤ) :=
  (sourceCarrier S H F).image output

def residueDivisorMaximum (S H F : ℝ) (a : ℤ) : ℕ :=
  (outputCarrier S H F).sup (fun zy => (a*zy.2).natAbs.divisors.card)

/-- This is the original ordered reciprocal-square source, not a new beta.
Only its independently completed m=0 kernel is inserted. -/
def actualZeroSource (S H F C D : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) : ℂ :=
  ∑ t ∈ sourceCarrier S H F,
    eps (output t)*tupleCoefficient A a lambda omega t*zeroKernel C D a (output t)

theorem actualZeroSource_eq_grouped (S H F C D : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) :
    actualZeroSource S H F C D A a lambda omega eps =
      ∑ zy ∈ outputCarrier S H F,
        countCoefficient S H F A a lambda omega eps zy*zeroKernel C D a zy := by
  have hf := sum_fiberwise_of_maps_to (s := sourceCarrier S H F)
    (t := outputCarrier S H F) (g := output)
    (fun t ht => mem_image_of_mem output ht)
    (fun t => eps (output t)*tupleCoefficient A a lambda omega t*zeroKernel C D a (output t))
  rw [actualZeroSource,← hf]
  apply sum_congr rfl
  intro zy hzy
  unfold countCoefficient
  simp only [mul_sum,sum_mul]
  apply sum_congr rfl
  intro t ht
  rw [(mem_filter.mp ht).2]

/-- All completed frequencies split on the actual coefficient before any
norm or estimate. This preserves the independent nonzero-m obligation. -/
theorem actualCompletedSource_eq_zero_add_nonzero {D : ℝ} (hD : 0 < D)
    (S H F C : ℝ) (A : ℕ) (a : ℤ)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) :
    (∑ t ∈ sourceCarrier S H F,
      eps (output t)*tupleCoefficient A a lambda omega t*completedKernel C D a (output t)) =
      actualZeroSource S H F C D A a lambda omega eps +
        ∑ t ∈ sourceCarrier S H F,
          eps (output t)*tupleCoefficient A a lambda omega t*nonzeroKernel C D a (output t) := by
  simp only [completedKernel_eq_zero_add_nonzero hD,mul_add,sum_add_distrib,
    actualZeroSource]

theorem output_y_ne_zero {S H F : ℝ} {zy : ℕ × ℤ}
    (hzy : zy ∈ outputCarrier S H F) : zy.2 ≠ 0 := by
  obtain ⟨t,ht,rfl⟩ := mem_image.mp hzy
  obtain ⟨hprod,hne⟩ := mem_filter.mp ht
  have hf := (mem_product.mp (mem_product.mp hprod).1).2
  have hfpos : 0 < t.1.2.2 := (mem_Ioc.mp (mem_filter.mp (mem_product.mp hf).2).1).1
  exact mul_ne_zero (by exact_mod_cast hfpos.ne') hne

/-- The physical zero branch is bounded by the actual all-source norm.
The finite support cardinality and divisor maximum remain explicit here. -/
theorem actualZeroSource_sq_le {C D : ℝ} (hC : 0 < C) (hD : 0 ≤ D)
    (S H F : ℝ) (A : ℕ) (a : ℤ) (ha : a ≠ 0)
    (lambda : ℕ → ℂ) (omega : ℤ → ℂ) (eps : ℕ × ℤ → ℂ) :
    ‖actualZeroSource S H F C D A a lambda omega eps‖^2 ≤
      (6*D*zeroFourierMass*(residueDivisorMaximum S H F a : ℝ))^2 *
        ((outputCarrier S H F).card : ℝ)*countingNorm S H F A a lambda omega eps 1 := by
  let K : ℝ := 6*D*zeroFourierMass*(residueDivisorMaximum S H F a : ℝ)
  have hK : 0 ≤ K := by dsimp [K,zeroFourierMass]; positivity
  have hpoint (zy : ℕ × ℤ) (hzy : zy ∈ outputCarrier S H F) :
      ‖zeroKernel C D a zy‖ ≤ K := by
    apply (zeroKernel_norm_le hC hD a zy (mul_ne_zero ha (output_y_ne_zero hzy))).trans
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast (le_sup hzy : (a*zy.2).natAbs.divisors.card ≤
        residueDivisorMaximum S H F a)) (by unfold zeroFourierMass; positivity)
  rw [actualZeroSource_eq_grouped]
  have hnorm : ‖∑ zy ∈ outputCarrier S H F,
      countCoefficient S H F A a lambda omega eps zy*zeroKernel C D a zy‖ ≤
      K*∑ zy ∈ outputCarrier S H F, ‖countCoefficient S H F A a lambda omega eps zy‖ := by
    calc
      _ ≤ ∑ zy ∈ outputCarrier S H F,
          ‖countCoefficient S H F A a lambda omega eps zy*zeroKernel C D a zy‖ := norm_sum_le _ _
      _ ≤ ∑ zy ∈ outputCarrier S H F,
          ‖countCoefficient S H F A a lambda omega eps zy‖*K := by
        apply sum_le_sum
        intro zy hzy
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpoint zy hzy) (norm_nonneg _)
      _ = _ := by rw [sum_mul]; ring
  have hcs := sum_mul_sq_le_sq_mul_sq (outputCarrier S H F) (fun _ => (1 : ℝ))
    (fun zy => ‖countCoefficient S H F A a lambda omega eps zy‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have hnormId : (∑ zy ∈ outputCarrier S H F,
      ‖countCoefficient S H F A a lambda omega eps zy‖^2) =
        countingNorm S H F A a lambda omega eps 1 := by
    simp [countingNorm,outputCarrier]
  rw [hnormId] at hcs
  calc
    _ ≤ (K*∑ zy ∈ outputCarrier S H F,
        ‖countCoefficient S H F A a lambda omega eps zy‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = K^2*(∑ zy ∈ outputCarrier S H F,
        ‖countCoefficient S H F A a lambda omega eps zy‖)^2 := mul_pow _ _ _
    _ ≤ K^2*((outputCarrier S H F).card : ℝ)*
        countingNorm S H F A a lambda omega eps 1 := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hcs (sq_nonneg K)

end
end ImbalancedChen.Part3.ActualZeroPoissonKernel20261102
