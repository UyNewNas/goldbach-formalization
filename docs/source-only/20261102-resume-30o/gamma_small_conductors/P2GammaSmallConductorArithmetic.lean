import ImbalancedChen.TotientReciprocalBudget
import MathlibNt.AnalyticNumberTheory.LargeSieve.PrimitiveCharacterElementaryPeriodBound

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The auxiliary divisor exponent is the literal one. Expanding tau(n) and
using supermultiplicativity of phi gives a square of the finite reciprocal-
totient sum. Its logarithmic exponent is two, independent of SW accuracy.
-/

namespace ImbalancedChen.P2GammaSmallConductorArithmetic
noncomputable section
open Classical Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

def reciprocalPhi : ArithmeticFunction ℝ :=
  ⟨fun n => 1 / (n.totient : ℝ), by simp⟩

/-- No coprimality between the two factors is required. -/
theorem inv_totient_mul_le (r k : ℕ) (hr : 0 < r) (hk : 0 < k) :
    (1 : ℝ) / ((r*k).totient : ℝ) ≤
      (1 / (r.totient : ℝ)) * (1 / (k.totient : ℝ)) := by
  have hp : (0 : ℝ) < (r.totient : ℝ) * (k.totient : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.totient_pos.mpr hr) (Nat.totient_pos.mpr hk)
  have hh : (r.totient : ℝ) * (k.totient : ℝ) ≤ ((r*k).totient : ℝ) := by
    exact_mod_cast Nat.totient_super_multiplicative r k
  simpa only [one_div, mul_inv_rev, mul_comm] using
    one_div_le_one_div_of_le hp hh

/-- Each divisor of n gives one ordered factorization of n. -/
theorem tau_div_totient_le_convolution {n : ℕ} (hn : 0 < n) :
    (n.divisors.card : ℝ) / (n.totient : ℝ) ≤
      (reciprocalPhi * reciprocalPhi) n := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun i j => reciprocalPhi i * reciprocalPhi j)]
  calc
    _ = ∑ _d ∈ n.divisors, (1 : ℝ) / (n.totient : ℝ) := by simp
    _ ≤ ∑ d ∈ n.divisors, reciprocalPhi d * reciprocalPhi (n/d) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have hquot : 0 < n/d := Nat.div_pos (Nat.le_of_dvd hn
        (Nat.dvd_of_mem_divisors hd)) hd0
      have hmul : d*(n/d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      simpa only [reciprocalPhi, ArithmeticFunction.coe_mk, hmul] using
        inv_totient_mul_le d (n/d) hd0 hquot

/-- Fixed C0=1: the complete quotient loss costs only a fixed log square. -/
theorem sum_tau_div_totient_le_log_sq (Q : ℕ) :
    (∑ k ∈ Finset.Icc 1 Q,
      (k.divisors.card : ℝ) / (k.totient : ℝ)) ≤
        16 * (1 + Real.log (max 1 (Q : ℝ)))^2 := by
  have hI : Finset.Ioc 0 Q = Finset.Icc 1 Q := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  have hid := ArithmeticFunction.sum_Ioc_mul_eq_sum_prod_filter
    reciprocalPhi reciprocalPhi Q
  rw [hI] at hid
  have hsum :
      (∑ k ∈ Finset.Icc 1 Q, (k.divisors.card : ℝ)/(k.totient : ℝ)) ≤
        (∑ d ∈ Finset.Icc 1 Q, 1/(d.totient : ℝ))^2 := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 Q, (reciprocalPhi*reciprocalPhi) k := by
        exact Finset.sum_le_sum fun k hk =>
          tau_div_totient_le_convolution (Finset.mem_Icc.mp hk).1
      _ = _ := hid
      _ ≤ ∑ z ∈ Finset.Icc 1 Q ×ˢ Finset.Icc 1 Q,
          reciprocalPhi z.1 * reciprocalPhi z.2 := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun z _ _ => by change 0 ≤ (1/(z.1.totient : ℝ)) *
            (1/(z.2.totient : ℝ)); positivity)
      _ = _ := by rw [pow_two,Finset.sum_mul_sum,Finset.sum_product]; rfl
  have hnonneg : 0 ≤ ∑ d ∈ Finset.Icc 1 Q, 1/(d.totient : ℝ) := by positivity
  have hbudget := sum_reciprocal_totient_le_log Q
  have hsq := pow_le_pow_left₀ hnonneg hbudget 2
  exact hsum.trans (by nlinarith only [hsq])

/-- The character-count factor is distinct from the residue-sum factor. -/
theorem primitive_character_count_le_phi (r : ℕ) (hr : 0 < r) :
    (Fintype.card (PrimitiveCharacter r) : ℝ) ≤ (r.totient : ℝ) := by
  exact_mod_cast primitiveCharacter_card_le_totient_basic r hr

/-- The residual sum of phi(r) is retained and paid by R squared. -/
theorem sum_phi_small_le_square (R : ℕ) :
    (∑ r ∈ Finset.Icc 2 R, (r.totient : ℝ)) ≤ (R : ℝ)^2 := by
  calc
    _ ≤ ∑ r ∈ Finset.Icc 2 R, (R : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact_mod_cast (Nat.totient_le r).trans (Finset.mem_Icc.mp hr).2
    _ = ((Finset.Icc 2 R).card : ℝ) * (R : ℝ) := by simp
    _ ≤ (R : ℝ) * (R : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg R)
      have hc : (Finset.Icc 2 R).card ≤ R := by
        calc
          _ ≤ (Finset.Icc 1 R).card := Finset.card_le_card (by
            intro r hr
            exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hr).1; omega,
              (Finset.mem_Icc.mp hr).2⟩)
          _ = R := by simp
      exact_mod_cast hc
    _ = _ := (pow_two _).symm

end
end ImbalancedChen.P2GammaSmallConductorArithmetic
