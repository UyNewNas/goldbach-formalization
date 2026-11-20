import ImbalancedChen.P4BOriginalCoprimeSmoothE1
import ImbalancedChen.Part3TwoLongHBMellinBrunProfiles
import ImbalancedChen.P5OriginalOneLongLiteralBrunDictionary

/-! SOURCE ONLY / UNCOMPILED. E1 for the exact current upper/gap Brun
polynomial and original smooth long profiles. The support is the same
inclusive smallPrimes Z alphabet and original order. Nonunit short
products delete the mean; q-primes are deleted only in the density.
No rough=polynomial equality, E3, or endpoint statement is made. -/
namespace ImbalancedChen.P4BOriginalBrunCoprimeE1
noncomputable section
open Classical Set MeasureTheory
open scoped BigOperators SchwartzMap
open P4BOriginalCoprimeSmoothE1
open Part3.TwoLongLiteralMellinModes (wideWindow)
open Part3.TwoLongLiteralBrunSubstitution (brunPolynomial brunCoefficient)
open Part3.TwoLongActualLowerBrunMoment (brunSupport brunSupport_bounds brunSupport_card)
open OriginalOneLongLiteralBrunDictionary (upperCoefficient gapCoefficient coefficient_bounds actual_B2)
open OriginalOneLongSharpBrun (compatibleGapDensity)
open OriginalOneLongE5FiniteBudget (brunEpsilon)
open Part3.RoughSlotCharacterLift20261026b (smallPrimes smallPrimes_prime)
open Part3.TwoLongTransitionMellinN2
open Part3.TwoLongN2FourierDecay (fourierDecayConstant fourierDecayConstant_pos)

def density (Z : ℝ) (j : ℕ) (gap : Bool) (q m : ℕ) : ℂ :=
  ∑ d∈brunSupport Z (2*j+1),
    if (m*d).Coprime q then brunCoefficient Z j gap d/(d:ℂ) else 0

def mean (F : ℝ→ℂ) (U Z : ℝ) (j : ℕ) (gap : Bool) (q m : ℕ) : ℂ :=
  ∑ n∈wideWindow U,F ((n:ℝ)/U)*brunPolynomial Z j gap n*
    (if (m*n).Coprime q then (1:ℂ) else 0)

def main (F : ℝ→ℂ) (U Z : ℝ) (j : ℕ) (gap : Bool) (q m : ℕ) : ℂ :=
  (U*((q.totient:ℝ)/q)) • (mass F*density Z j gap q m)

theorem coefficient_norm (Z : ℝ) (j : ℕ) (gap : Bool) (d : ℕ) :
    ‖brunCoefficient Z j gap d‖≤1 := by
  have H := coefficient_bounds (smallPrimes Z) (2*j) (2*j+1) d
  cases gap
  · simpa only [brunCoefficient,Bool.false_eq_true,if_false,Complex.norm_real,Real.norm_eq_abs] using H.1
  · simpa only [brunCoefficient,if_true,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg H.2.1] using H.2.2

/-- Directly reuses the polynomial's literal divisor support; no new
subset/subproduct or prime-word bijection is introduced. -/
theorem mean_eq_divisor_sum (F : 𝓢(ℝ,ℂ)) (U Z : ℝ) (j : ℕ) (gap : Bool) (q m : ℕ) :
    mean F U Z j gap q m=
      ∑ d∈brunSupport Z (2*j+1),brunCoefficient Z j gap d*divisorMean F U q m d := by
  unfold mean brunPolynomial divisorMean
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem main_eq_divisor_sum (F : 𝓢(ℝ,ℂ)) (U Z : ℝ) (j : ℕ) (gap : Bool) (q m : ℕ) :
    main F U Z j gap q m=
      ∑ d∈brunSupport Z (2*j+1),brunCoefficient Z j gap d*
        (if (m*d).Coprime q then ((U/d)*((q.totient:ℝ)/q)) • mass F else 0) := by
  unfold main density
  simp only [smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : (m*d).Coprime q
  · simp only [if_pos h,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_natCast]
    ring
  · simp [h]

/-- Complete finite E1, for every positive q and arbitrary short m.
The extra derivative in N2 costs only the existing fixed profile log
price. The original integral, phi(q)/q and q-deletion stay exact. -/
theorem actual_E1 (F : 𝓢(ℝ,ℂ))
    (hF : Function.support (F : ℝ→ℂ)⊆Icc (1/2:ℝ) (5/2))
    {U Z : ℝ} (hU : 0<U) (hZ : 1≤Z) (j : ℕ) (gap : Bool) (q m : ℕ) (hq : 0<q) :
    ‖mean F U Z j gap q m-main F U Z j gap q m‖≤
      price F*(q.divisors.card:ℝ)*Z^(2*j+1) := by
  rw [mean_eq_divisor_sum,main_eq_divisor_sum,←Finset.sum_sub_distrib]
  have hcost : 0≤price F*(q.divisors.card:ℝ) :=
    mul_nonneg (price_nonneg F) (Nat.cast_nonneg _)
  calc
    _≤∑ d∈brunSupport Z (2*j+1),‖brunCoefficient Z j gap d*
        (divisorMean F U q m d-
          (if (m*d).Coprime q then ((U/d)*((q.totient:ℝ)/q)) • mass F else 0))‖ := by
      simp_rw [←mul_sub]
      exact norm_sum_le _ _
    _≤∑ _d∈brunSupport Z (2*j+1),price F*(q.divisors.card:ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have H := divisor_E1 F hF hU q m d hq (brunSupport_bounds hZ _ hd).1
      have H' : ‖divisorMean F U q m d-
          (if (m*d).Coprime q then ((U/d)*((q.totient:ℝ)/q)) • mass F else 0)‖≤
          price F*(q.divisors.card:ℝ) := by
        apply H.trans
        split_ifs <;> first | exact le_rfl | exact hcost
      rw [norm_mul]
      exact (mul_le_mul (coefficient_norm Z j gap d) H' (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _=((brunSupport Z (2*j+1)).card:ℝ)*(price F*(q.divisors.card:ℝ)) := by simp
    _≤_ := (mul_le_mul_of_nonneg_right (brunSupport_card hZ _) hcost).trans_eq (by ring)

theorem mean_nonunit (F : 𝓢(ℝ,ℂ)) (U Z : ℝ) (j : ℕ) (gap : Bool) (q m : ℕ)
    (hm : ¬m.Coprime q) : mean F U Z j gap q m=0 ∧ main F U Z j gap q m=0 := by
  have hmn (n : ℕ) : ¬(m*n).Coprime q := fun h => hm (Nat.coprime_mul_iff_left.mp h).1
  constructor
  · simp [mean,hmn]
  · simp [main,density,hmn]

theorem modulus_one_mean (F : ℝ→ℂ) (U Z : ℝ) (j : ℕ) (gap : Bool) (m : ℕ) :
    mean F U Z j gap 1 m=∑ n∈wideWindow U,F ((n:ℝ)/U)*brunPolynomial Z j gap n := by
  simp [mean]

/-- The existing compatible-gap/B2 theorem is applied to the SAME
smallPrimes Z divisor bank, for every q and every (possibly nonunit) m. -/
theorem gap_density_B2 (Z : ℝ) (j q m : ℕ) :
    ‖density Z j true q m‖≤brunEpsilon j (smallPrimes Z) := by
  have heq : density Z j true q m=
      (compatibleGapDensity (brunSupport Z (2*j+1))
        (gapCoefficient (smallPrimes Z) (2*j+1)) q m:ℂ) := by
    simp [density,brunCoefficient,compatibleGapDensity,Complex.ofReal_sum,
      Complex.ofReal_div,Complex.ofReal_natCast]
  have hnon : 0≤compatibleGapDensity (brunSupport Z (2*j+1))
      (gapCoefficient (smallPrimes Z) (2*j+1)) q m := by
    unfold compatibleGapDensity
    apply Finset.sum_nonneg
    intro d hd
    split_ifs
    · exact div_nonneg (coefficient_bounds (smallPrimes Z) (2*j) (2*j+1) d).2.1 (Nat.cast_nonneg _)
    · exact le_rfl
  rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hnon]
  exact actual_B2 j (smallPrimes Z) q m (fun p hp => smallPrimes_prime hp)

def profilePrice (delta U H : ℝ) : ℝ :=
  2*fourierDecayConstant*(profileConstant*logSize U*(1+H)^2/delta^2)

theorem profile_price (isGap isLog : Bool) {delta U H t : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hH : 0≤H) (ht : |t|≤H) :
    price (profileSchwartz isGap isLog hd hs U t)≤profilePrice delta U H := by
  unfold price profilePrice
  exact mul_le_mul_of_nonneg_left (profile_N2_cube isGap isLog hd hs hH ht U)
    (mul_nonneg (by norm_num) fourierDecayConstant_pos.le)

/-- The actual long profile keeps log U even at inserted divisor d;
both rough-polynomial labels and smooth-profile labels are independent. -/
theorem actual_profile_E1 (isGap isLog gap : Bool) {delta U H t Z : ℝ}
    (hd : 0<delta) (hs : delta≤1/4) (hU : 0<U) (hH : 0≤H) (ht : |t|≤H)
    (hZ : 1≤Z) (j q m : ℕ) (hq : 0<q) :
    let F := profileSchwartz isGap isLog hd hs U t
    ‖mean F U Z j gap q m-main F U Z j gap q m‖≤
      profilePrice delta U H*(q.divisors.card:ℝ)*Z^(2*j+1) := by
  exact (actual_E1 _ (profile_support isGap isLog hd hs U t) hU hZ j gap q m hq).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (profile_price isGap isLog hd hs hH ht) (Nat.cast_nonneg _))
      (pow_nonneg (zero_le_one.trans hZ) _))

end
end ImbalancedChen.P4BOriginalBrunCoprimeE1
