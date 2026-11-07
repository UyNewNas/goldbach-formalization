import ImbalancedChen.P2EnhancedNativeLowerConditionalPrefix
import ImbalancedChen.P5OriginalOrdinaryResidualArithmeticFactor

/-!
SOURCE_ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The literal LOWER native coefficient factors conditionally at the actual
rough product d. Its small level is L/d. Even rough prime-factor rank
retains LOWER small parity and odd rough rank switches to UPPER parity.

The existing upper arithmetic factor source supplies its proved exact
separated-support equivalence; no upper coefficient identity is cloned.
The main identity includes inactive rows, repeated powers, omitted cap
primes, forbidden target primes and zero factors. It is an arithmetic
identity, not an independent beta identification or an AP/count licence.
-/

namespace ImbalancedChen.P2EnhancedNativeLowerResidualFactor

noncomputable section

open scoped BigOperators Classical
open P5Z.OriginalOrdinaryBetaRegroup
open P5Z.OriginalOrdinaryConditionalPrefix
open P5Z.OriginalOrdinaryResidualArithmeticFactor
open P2EnhancedNativeLowerConditionalPrefix
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

def lowerRoughWeight (N cap : ℕ) (w Z L : ℝ) (d : ℕ) : ℝ :=
  lowerWeight (roughProduct N cap w Z) L d

def lowerResidualSmallWeight (N cap : ℕ) (w L : ℝ) (d e : ℕ) : ℝ :=
  if Even d.primeFactors.card then actualSmallRosserMinus N cap w (L / (d : ℝ)) e
  else actualSmallRosserPlus N cap w (L / (d : ℝ)) e

/-- Exact supported coefficient identity. No coefficient nonvanishing or
final-prefix admissibility is assumed. -/
theorem native_lower_residual_factor_on_support {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w ≤ Z) (he : e ∈ actualSmallRosserSupport N cap w)
    (hd : d ∈ roughSupport N cap w Z) :
    actualSmallRosserMinus N cap Z L (e * d) =
      lowerRoughWeight N cap w Z L d * lowerResidualSmallWeight N cap w L d e := by
  have heS := actualSmallRosserSupport_smallPrimeSupportedAt N cap w he
  have hdR := roughSupport_rough hd
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hdR.1
  have heone : (1 : ℝ) ≤ e := by exact_mod_cast Nat.pos_of_ne_zero heS.1
  have hmem : e * d ∈ actualSmallRosserSupport N cap Z :=
    (separated_support_iff hwZ heS hdR).mpr ⟨he, hd⟩
  have hcut : (e : ℝ) < L / (d : ℝ) ↔ ((e * d : ℕ) : ℝ) < L := by
    rw [lt_div_iff₀ hdpos, Nat.cast_mul]
  have hroughcut : (((e * d : ℕ) : ℝ) < L) → ((d : ℝ) < L) := by
    intro h
    have hm := mul_le_mul_of_nonneg_right heone (Nat.cast_nonneg d)
    simp only [one_mul] at hm
    rw [Nat.cast_mul] at h
    exact hm.trans_lt h
  have hcard : (e * d).primeFactors.card = d.primeFactors.card + e.primeFactors.card := by
    rw [Nat.primeFactors_mul heS.1 hdR.1,
      Finset.card_union_of_disjoint (separated_disjoint hdR.2 heS.2).symm]
    omega
  have hmemE : e ∈ (actualSmallPrimeProduct N cap w).divisors := he
  have hmemD : d ∈ (roughProduct N cap w Z).divisors := hd
  have hmemZ : e * d ∈ (actualSmallPrimeProduct N cap Z).divisors := hmem
  by_cases hp : Even d.primeFactors.card
  · have hg := actual_lower_gates_even (L := L) he hd hp
    simp only [lowerRoughWeight, lowerResidualSmallWeight, if_pos hp,
      actualSmallRosserMinus, ActualSmallRosserProvider.lowerWeight, lowerWeight_apply,
      hmemE, hmemD, hmemZ, true_and, hg, hcut, hcard, pow_add]
    by_cases hc : ((e * d : ℕ) : ℝ) < L
    · have hr := hroughcut hc
      by_cases hu : LowerAdmissibleSet L d.primeFactors <;>
        by_cases hv : LowerAdmissibleSet (L / (d : ℝ)) e.primeFactors <;>
        simp [hc, hr, hu, hv]
    · simp [hc]
  · have hg := actual_lower_gates_odd (L := L) he hd hp
    simp only [lowerRoughWeight, lowerResidualSmallWeight, if_neg hp,
      actualSmallRosserMinus, actualSmallRosserPlus, ActualSmallRosserProvider.lowerWeight,
      ActualSmallRosserProvider.upperWeight, lowerWeight_apply, upperWeight_apply,
      hmemE, hmemD, hmemZ, true_and, hg, hcut, hcard, pow_add]
    by_cases hc : ((e * d : ℕ) : ℝ) < L
    · have hr := hroughcut hc
      by_cases hu : LowerAdmissibleSet L d.primeFactors <;>
        by_cases hv : UpperAdmissibleSet (L / (d : ℝ)) e.primeFactors <;>
        simp [hc, hr, hu, hv]
    · simp [hc]

theorem lowerResidualSmallWeight_eq_zero_of_not_mem {N cap d e : ℕ} {w L : ℝ}
    (he : e ∉ actualSmallRosserSupport N cap w) :
    lowerResidualSmallWeight N cap w L d e = 0 := by
  unfold lowerResidualSmallWeight
  split_ifs
  · by_contra h
    exact he (actualSmallRosserMinus_active h).1
  · by_contra h
    exact he (actualSmallRosserPlus_active h).1

theorem lowerRoughWeight_eq_zero_of_not_mem {N cap d : ℕ} {w Z L : ℝ}
    (hd : d ∉ roughSupport N cap w Z) : lowerRoughWeight N cap w Z L d = 0 := by
  by_contra h
  exact hd (lowerWeight_active h).1

/-- Full cutoff-separated arithmetic identity. Actual finite support,
squarefreeness and nonvanishing are conclusions of active coefficients,
rather than additional hypotheses on this identity. -/
theorem native_lower_residual_factor {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w ≤ Z) (he : SmallPrimeSupportedAt w e) (hd : RoughPrimeSupportedAt w d) :
    actualSmallRosserMinus N cap Z L (e * d) =
      lowerRoughWeight N cap w Z L d * lowerResidualSmallWeight N cap w L d e := by
  by_cases heM : e ∈ actualSmallRosserSupport N cap w
  · by_cases hdM : d ∈ roughSupport N cap w Z
    · exact native_lower_residual_factor_on_support hwZ heM hdM
    · have hz : actualSmallRosserMinus N cap Z L (e * d) = 0 := by
        by_contra h
        exact hdM ((separated_support_iff hwZ he hd).mp (actualSmallRosserMinus_active h).1).2
      rw [hz, lowerRoughWeight_eq_zero_of_not_mem hdM, zero_mul]
  · have hz : actualSmallRosserMinus N cap Z L (e * d) = 0 := by
      by_contra h
      exact heM ((separated_support_iff hwZ he hd).mp (actualSmallRosserMinus_active h).1).1
    rw [hz, lowerResidualSmallWeight_eq_zero_of_not_mem heM, mul_zero]

/-- Literal zero coefficients need no artificial positive-level input. -/
theorem native_lower_residual_factor_zero_left (N cap d : ℕ) (w Z L : ℝ) :
    actualSmallRosserMinus N cap Z L (0 * d) =
      lowerRoughWeight N cap w Z L d * lowerResidualSmallWeight N cap w L d 0 := by
  simp [lowerResidualSmallWeight, actualSmallRosserPlus, actualSmallRosserMinus]

theorem native_lower_residual_factor_zero_right (N cap e : ℕ) (w Z L : ℝ) :
    actualSmallRosserMinus N cap Z L (e * 0) =
      lowerRoughWeight N cap w Z L 0 * lowerResidualSmallWeight N cap w L 0 e := by
  simp [lowerRoughWeight, actualSmallRosserMinus]

/-- Total native lower factorization, including either zero factor. -/
theorem native_lower_residual_factor_total {N cap e d : ℕ} {w Z L : ℝ}
    (hwZ : w ≤ Z) (he : e = 0 ∨ SmallPrimeSupportedAt w e)
    (hd : d = 0 ∨ RoughPrimeSupportedAt w d) :
    actualSmallRosserMinus N cap Z L (e * d) =
      lowerRoughWeight N cap w Z L d * lowerResidualSmallWeight N cap w L d e := by
  rcases he with rfl | he
  · exact native_lower_residual_factor_zero_left N cap d w Z L
  rcases hd with rfl | hd
  · exact native_lower_residual_factor_zero_right N cap e w Z L
  exact native_lower_residual_factor hwZ he hd

end
end ImbalancedChen.P2EnhancedNativeLowerResidualFactor
