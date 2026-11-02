import ImbalancedChen.P2GammaInducedCharacterDictionary
import MathlibNt.AnalyticNumberTheory.LargeSieve.RankOneRectangularPrimitiveL1
import ImbalancedChen.TotientReciprocalBudget

/-!
SOURCE ONLY. UNCOMPILED. ZERO FORMAL CREDIT.

A genuine finite part of the original low-rank convolution proof. At fixed
k the TWO masked coefficient rows are independent of the conductor r. The
primitive large sieve is applied to the complete rows, not separately to
every complementary integer. The 1/R gain comes from the dyadic range
R<r<=2R before Cauchy. The exact induced-level denominator is phi(r*k).

The terminal k charge has a uniform finite bound 8, so a Q/k term does not
cost Q separate complete-scale prime-BV errors. No source energy bound,
small-conductor estimate, BV estimate or distribution conclusion is assumed.
The right sides retain explicit original coefficient energies.
-/

namespace ImbalancedChen.P2GammaConvolutionLargeConductor
noncomputable section
open scoped Classical BigOperators
open AnalyticNumberTheory.LargeSieve
open P2GammaInducedCharacterDictionary

def unitMask (k : ℕ) (a : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n.natAbs.Coprime k then a n else 0

def rowEnergy (a : ℤ → ℂ) (M : ℤ) (L : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (M+1) (M+L), ‖a n‖^2

theorem rowEnergy_nonneg (a : ℤ → ℂ) (M : ℤ) (L : ℕ) :
    0≤rowEnergy a M L := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem unitMask_energy_le (k : ℕ) (a : ℤ → ℂ) (M : ℤ) (L : ℕ) :
    rowEnergy (unitMask k a) M L≤rowEnergy a M L := by
  apply Finset.sum_le_sum
  intro n hn
  by_cases h : n.natAbs.Coprime k
  · simp only [unitMask,h,if_true]
  · simp only [unitMask,h,if_false,norm_zero,zero_pow (by omega : 2≠0)]
    exact sq_nonneg _

def rowAmplitude (a : ℤ → ℂ) (M : ℤ) (L r : ℕ)
    (psi : PrimitiveCharacter r) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M+1) (M+L), a n*psi.1 (n : ZMod r)‖

/-- Induced level r*k, with both k-unit projectors and the exact weight. -/
def inducedShell (a b : ℤ → ℂ) (Ma Mb : ℤ) (La Lb k : ℕ)
    (S : Finset ℕ) : ℝ :=
  ∑ r ∈ S, (1/((r*k).totient : ℝ))*
    ∑ psi : PrimitiveCharacter r,
      rowAmplitude (unitMask k a) Ma La r psi *
        rowAmplitude (unitMask k b) Mb Lb r psi

theorem inducedShell_nonneg (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb k : ℕ) (S : Finset ℕ) :
    0≤inducedShell a b Ma Mb La Lb k S := by
  unfold inducedShell rowAmplitude
  positivity

/-- The dyadic lower conductor is used before Cauchy, preserving the
factor 1/R that is absent from an unweighted full-cutoff first moment. -/
theorem inducedShell_le_rectangular (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb R k : ℕ) (hR : 0<R) (hk : 0<k) (S : Finset ℕ)
    (hS : S⊆Finset.Ioc R (2*R)) :
    inducedShell a b Ma Mb La Lb k S ≤
      (1/((R : ℝ)*(k.totient : ℝ))) *
        rankOneRectangularWeightedPrimitiveMean
          (unitMask k a) (unitMask k b) Ma Mb La Lb S := by
  unfold inducedShell rankOneRectangularWeightedPrimitiveMean
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrR : R<r := (Finset.mem_Ioc.mp (hS hr)).1
  have hr0 : 0<r := hR.trans hrR
  have hRR : (0 : ℝ)<R := by exact_mod_cast hR
  have hphiR : (0 : ℝ)<r.totient := by exact_mod_cast Nat.totient_pos.mpr hr0
  have hphiK : (0 : ℝ)<k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hRr : (R : ℝ)≤r := by exact_mod_cast hrR.le
  have hden : (1 : ℝ)/((r*k).totient : ℝ) ≤
      (1/((R : ℝ)*(k.totient : ℝ)))*((r : ℝ)/(r.totient : ℝ)) := by
    calc
      _ ≤ 1/((r.totient : ℝ)*(k.totient : ℝ)) :=
        inv_totient_product_le r k hr0 hk
      _ ≤ (r : ℝ)/((R : ℝ)*((r.totient : ℝ)*(k.totient : ℝ))) := by
        apply (div_le_div_iff₀ (mul_pos hphiR hphiK)
          (mul_pos hRR (mul_pos hphiR hphiK))).mpr
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hRr (mul_nonneg hphiR.le hphiK.le)
      _ = _ := by ring
  have hn : 0≤∑ psi : PrimitiveCharacter r,
      rowAmplitude (unitMask k a) Ma La r psi *
        rowAmplitude (unitMask k b) Mb Lb r psi := by
    unfold rowAmplitude
    positivity
  simpa only [rowAmplitude,mul_assoc] using mul_le_mul_of_nonneg_right hden hn

/-- Genuine large-sieve payment for the induced dyadic rectangle.
The only analytic supplier is the proved primitive rectangular theorem;
all original energies survive explicitly. No convolution-BV premise. -/
theorem inducedShell_largeSieve (a b : ℤ → ℂ) (Ma Mb : ℤ)
    (La Lb R k : ℕ) (hR : 0<R) (hk : 0<k) (S : Finset ℕ)
    (hS : S⊆Finset.Ioc R (2*R)) :
    inducedShell a b Ma Mb La Lb k S ≤
      (1/((R : ℝ)*(k.totient : ℝ))) *
        (Real.sqrt (largeSieveBound La (1/((2*R : ℕ) : ℝ)^2)*rowEnergy a Ma La) *
          Real.sqrt (largeSieveBound Lb (1/((2*R : ℕ) : ℝ)^2)*rowEnergy b Mb Lb)) := by
  have h2R : 0<2*R := by omega
  have hSS : S⊆Finset.Icc 1 (2*R) := by
    intro r hr
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioc.mp (hS hr)
    exact Finset.mem_Icc.mpr ⟨by omega,hhi⟩
  have hLS := rankOneRectangularWeightedPrimitiveMean_le
    (unitMask k a) (unitMask k b) Ma Mb La Lb (2*R) h2R S hSS
  have hc (L : ℕ) : 0≤largeSieveBound L (1/((2*R : ℕ) : ℝ)^2) := by
    unfold largeSieveBound
    positivity
  have hleft :
      Real.sqrt (largeSieveBound La (1/((2*R : ℕ) : ℝ)^2)*
        rowEnergy (unitMask k a) Ma La) ≤
      Real.sqrt (largeSieveBound La (1/((2*R : ℕ) : ℝ)^2)*rowEnergy a Ma La) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (unitMask_energy_le k a Ma La) (hc La))
  have hright :
      Real.sqrt (largeSieveBound Lb (1/((2*R : ℕ) : ℝ)^2)*
        rowEnergy (unitMask k b) Mb Lb) ≤
      Real.sqrt (largeSieveBound Lb (1/((2*R : ℕ) : ℝ)^2)*rowEnergy b Mb Lb) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (unitMask_energy_le k b Mb Lb) (hc Lb))
  refine (inducedShell_le_rectangular a b Ma Mb La Lb R k hR hk S hS).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact hLS.trans (mul_le_mul hleft hright (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private def invSquare : ArithmeticFunction ℝ :=
  ⟨fun n => 1/(n : ℝ)^2,by simp⟩

private def invCube : ArithmeticFunction ℝ :=
  ⟨fun n => 1/(n : ℝ)^3,by simp⟩

private theorem invCube_mul_invSquare (n : ℕ) :
    (invCube*invSquare) n =
      (1/(n : ℝ)^2)*(∑ d ∈ n.divisors,1/(d : ℝ)) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => invCube i*invSquare j),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  change (1/(d : ℝ)^3)*(1/((n/d : ℕ) : ℝ)^2)=
    (1/(n : ℝ)^2)*(1/(d : ℝ))
  have hprod : (d : ℝ)*((n/d : ℕ) : ℝ)=n := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  rw [← hprod]
  simp only [one_div,mul_inv_rev,inv_pow]
  ring

private theorem inverse_cube_sum_le_two (Q : ℕ) :
    (∑ d ∈ Finset.Icc 1 Q,1/(d : ℝ)^3)≤2 := by
  refine le_trans (Finset.sum_le_sum fun d hd => ?_) (totientBudget_inverse_square_sum Q)
  have hd1 : (1 : ℝ)≤d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hd0 : (0 : ℝ)<d := zero_lt_one.trans_le hd1
  apply one_div_le_one_div_of_le (pow_pos hd0 2)
  rw [pow_succ]
  exact le_mul_of_one_le_right (pow_nonneg hd0.le 2) hd1

private theorem inverse_square_divisor_sum_le_four (Q : ℕ) :
    (∑ n ∈ Finset.Icc 1 Q,(1/(n : ℝ)^2)*∑ d ∈ n.divisors,1/(d : ℝ))≤4 := by
  have hI : Finset.Ioc 0 Q=Finset.Icc 1 Q := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hconv := ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter invCube invSquare Q
  rw [hI] at hconv
  simp_rw [invCube_mul_invSquare] at hconv
  rw [hconv]
  calc
    _ ≤ ∑ p ∈ Finset.Icc 1 Q ×ˢ Finset.Icc 1 Q,invCube p.1*invSquare p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p _ _ => by change 0≤(1/(p.1 : ℝ)^3)*(1/(p.2 : ℝ)^2); positivity)
    _ = (∑ d ∈ Finset.Icc 1 Q,1/(d : ℝ)^3)*
        (∑ m ∈ Finset.Icc 1 Q,1/(m : ℝ)^2) := by
      rw [Finset.sum_product,Finset.sum_mul_sum]
      rfl
    _ ≤ 2*2 := mul_le_mul (inverse_cube_sum_le_two Q)
      (totientBudget_inverse_square_sum Q) (by positivity) (by norm_num)
    _ = 4 := by norm_num

/-- The full induced-quotient k sum is uniformly bounded, not O(Q).
This finite proof needs no zeta-value evaluation or asymptotic premise. -/
theorem sum_inv_mul_totient_le_eight (Q : ℕ) :
    (∑ k ∈ Finset.Icc 1 Q,1/((k : ℝ)*(k.totient : ℝ)))≤8 := by
  have hp : (∑ k ∈ Finset.Icc 1 Q,1/((k : ℝ)*(k.totient : ℝ))) ≤
      2*(∑ k ∈ Finset.Icc 1 Q,(1/(k : ℝ)^2)*∑ d ∈ k.divisors,1/(d : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h := mul_le_mul_of_nonneg_left
      (reciprocal_totient_le_divisor_sum (Finset.mem_Icc.mp hk).1)
      (show (0 : ℝ)≤1/(k : ℝ) by positivity)
    convert h using 1 <;> ring
  exact hp.trans (by nlinarith [inverse_square_divisor_sum_le_four Q])

/-- Arithmetic assembly for the actual form U+V/k of the dyadic conductor
payment. The final Q/k lane is charged through the convergent k sum. -/
theorem induced_quotient_charge (Q : ℕ) (U V : ℝ) (hU : 0≤U) (hV : 0≤V) :
    (∑ k ∈ Finset.Icc 1 Q,(U+V/(k : ℝ))/(k.totient : ℝ)) ≤
      4*(1+Real.log (max 1 (Q : ℝ)))*U+8*V := by
  have hid : (∑ k ∈ Finset.Icc 1 Q,(U+V/(k : ℝ))/(k.totient : ℝ)) =
      U*(∑ k ∈ Finset.Icc 1 Q,1/(k.totient : ℝ))+
        V*(∑ k ∈ Finset.Icc 1 Q,1/((k : ℝ)*(k.totient : ℝ))) := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hid]
  have h1 := mul_le_mul_of_nonneg_left (sum_reciprocal_totient_le_log Q) hU
  have h2 := mul_le_mul_of_nonneg_left (sum_inv_mul_totient_le_eight Q) hV
  nlinarith

end
end ImbalancedChen.P2GammaConvolutionLargeConductor
