import ImbalancedChen.ActualSmallRoughAttachment
import ImbalancedChen.ActualExtendedThirdCompactUpperRho
import ImbalancedChen.P4ARetainedSupportDifferenceMass

/-!
SOURCEONLY / UNCOMPILED. The actual small Rosser weights are the pinned
provider's literal cutoffs of (-1)^omega on divisors of the squarefree
small prime product. A nonzero small coefficient therefore equals Mobius.
The actual rough coefficient is Mobius on its retained support. Strictly
small and inclusively rough prime ranges give the unique decomposition
and coprimality needed to multiply these signs. The sign-sensitive choice
of small upper/lower weight is preserved throughout.
-/

namespace ImbalancedChen.P4APhysicalMoebiusLookup

noncomputable section
open P4ARetainedSupportDifferenceMass

private theorem moebius_eq_negOnePow_card_of_squarefree {d : ℕ} (hd : Squarefree d) :
    (ArithmeticFunction.moebius d : ℝ) = (-1 : ℝ) ^ d.primeFactors.card := by
  have hcard : ArithmeticFunction.cardFactors d = d.primeFactors.card := by
    change d.primeFactorsList.length = d.primeFactors.card
    rw [← Nat.toFinset_factors]
    exact (List.toFinset_card_of_nodup hd.nodup_primeFactorsList).symm
  have hmu : ArithmeticFunction.moebius d = (-1 : ℤ) ^ d.primeFactors.card := by
    rw [ArithmeticFunction.moebius_apply_of_squarefree hd, hcard]
  exact_mod_cast hmu

/-- This is derived from the provider's actual lower-weight formula and
the actual small support's squarefreeness, for every real level L. -/
theorem actualMinus_eq_moebius_of_ne_zero (N cap : ℕ) (w L : ℝ) {d : ℕ}
    (hd : actualSmallRosserMinus N cap w L d ≠ 0) :
    actualSmallRosserMinus N cap w L d = (ArithmeticFunction.moebius d : ℝ) := by
  have hactive := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_active hd
  have hsf := actualSmallRosserSupport_squarefree N cap w (actualSmallRosserMinus_active hd).1
  change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight
    (actualSmallPrimeProduct N cap w) L d = _
  rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.lowerWeight_apply, if_pos hactive]
  exact (moebius_eq_negOnePow_card_of_squarefree hsf).symm

/-- The provider's actual upper-weight formula has the same Mobius sign;
its distinct odd-prefix admission test only changes whether it vanishes. -/
theorem actualPlus_eq_moebius_of_ne_zero (N cap : ℕ) (w L : ℝ) {d : ℕ}
    (hd : actualSmallRosserPlus N cap w L d ≠ 0) :
    actualSmallRosserPlus N cap w L d = (ArithmeticFunction.moebius d : ℝ) := by
  have hactive := MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_active hd
  have hsf := actualSmallRosserSupport_squarefree N cap w (actualSmallRosserPlus_active hd).1
  change MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight
    (actualSmallPrimeProduct N cap w) L d = _
  rw [MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser.upperWeight_apply, if_pos hactive]
  exact (moebius_eq_negOnePow_card_of_squarefree hsf).symm

theorem actualMinus_zero_or_moebius (N cap : ℕ) (w L : ℝ) (d : ℕ) :
    actualSmallRosserMinus N cap w L d = 0 ∨
      actualSmallRosserMinus N cap w L d = (ArithmeticFunction.moebius d : ℝ) := by
  by_cases hd : actualSmallRosserMinus N cap w L d = 0
  · exact Or.inl hd
  · exact Or.inr (actualMinus_eq_moebius_of_ne_zero N cap w L hd)

theorem actualPlus_zero_or_moebius (N cap : ℕ) (w L : ℝ) (d : ℕ) :
    actualSmallRosserPlus N cap w L d = 0 ∨
      actualSmallRosserPlus N cap w L d = (ArithmeticFunction.moebius d : ℝ) := by
  by_cases hd : actualSmallRosserPlus N cap w L d = 0
  · exact Or.inl hd
  · exact Or.inr (actualPlus_eq_moebius_of_ne_zero N cap w L hd)

/-- The occupied-fibre lookup retains the literal sign-sensitive choice.
No average, absolute-value envelope or multiplicity factor appears. -/
theorem actualRho_mul_eq_signSensitive_lookup
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {a b : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z) :
    actualSmallRoughRho retainOdd N cap w z L (a * b) =
      fixedRoughCoefficient retainOdd N cap w z b *
        (if 0 ≤ fixedRoughCoefficient retainOdd N cap w z b then
          actualSmallRosserPlus N cap w L a else actualSmallRosserMinus N cap w L a) := by
  exact smallRoughRho_mul
    (fun _ hd => actualSmallRosserSupport_smallPrimeSupportedAt N cap w hd)
    (fun _ hd => fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hd)
    (fixedRoughCoefficient retainOdd N cap w z)
    (actualSmallRosserMinus N cap w L) (actualSmallRosserPlus N cap w L) ha hb

/-- A nonzero physical coefficient has one unique actual small/rough pair.
Uniqueness concerns the complete pair, not merely its product. -/
theorem actualRho_ne_zero_unique_factors
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho retainOdd N cap w z L q ≠ 0) :
    ∃! x : ℕ × ℕ, x.1 ∈ actualSmallRosserSupport N cap w ∧
      x.2 ∈ fixedRoughSupport retainOdd N cap w z ∧ q = x.1 * x.2 := by
  obtain ⟨a, ha, b, hb, hprod, _hlevel, _hrough⟩ :=
    actualSmallRoughRho_ne_zero_factors retainOdd N cap w z L hq
  refine ⟨(a, b), ⟨ha, hb, hprod⟩, ?_⟩
  intro x hx
  exact smallRough_factorization_unique
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w hx.1)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hx.2.1)
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb)
    (hx.2.2.symm.trans hprod)

/-- On an occupied nonzero fibre, the chosen small weight is itself Mobius.
The sign test is on the actual rough coefficient, as in the original rho. -/
theorem actual_selected_small_eq_moebius_of_rho_ne_zero
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {a b : ℕ}
    (ha : a ∈ actualSmallRosserSupport N cap w)
    (hb : b ∈ fixedRoughSupport retainOdd N cap w z)
    (hq : actualSmallRoughRho retainOdd N cap w z L (a * b) ≠ 0) :
    (if 0 ≤ fixedRoughCoefficient retainOdd N cap w z b then
      actualSmallRosserPlus N cap w L a else actualSmallRosserMinus N cap w L a) =
        (ArithmeticFunction.moebius a : ℝ) := by
  rw [actualRho_mul_eq_signSensitive_lookup retainOdd N cap w z L ha hb] at hq
  have hbeta := (mul_ne_zero_iff.mp hq).2
  by_cases hsign : 0 ≤ fixedRoughCoefficient retainOdd N cap w z b
  · rw [if_pos hsign] at hbeta ⊢
    exact actualPlus_eq_moebius_of_ne_zero N cap w L hbeta
  · rw [if_neg hsign] at hbeta ⊢
    exact actualMinus_eq_moebius_of_ne_zero N cap w L hbeta

/-- The literal complete physical rho equals Mobius wherever nonzero.
The proof uses its unique actual fibre and coprime small/rough factors. -/
theorem actualRho_eq_moebius_of_ne_zero
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho retainOdd N cap w z L q ≠ 0) :
    actualSmallRoughRho retainOdd N cap w z L q = (ArithmeticFunction.moebius q : ℝ) := by
  obtain ⟨a, ha, b, hb, hprod, _hlevel, _hrough⟩ :=
    actualSmallRoughRho_ne_zero_factors retainOdd N cap w z L hq
  have hcop := smallPrimeSupportedAt_coprime_roughPrimeSupportedAt
    (actualSmallRosserSupport_smallPrimeSupportedAt N cap w ha)
    (fixedRoughSupport_roughPrimeSupportedAt retainOdd N cap w z hb)
  have hmul : (ArithmeticFunction.moebius (a * b) : ℝ) =
      (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) := by
    simpa only [Int.cast_mul] using congrArg (fun n : ℤ => (n : ℝ))
      (ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop)
  have hrough : fixedRoughCoefficient retainOdd N cap w z b =
      (ArithmeticFunction.moebius b : ℝ) := by
    rw [coefficient_eq_moebius_indicator, if_pos hb]
  have hnonzero : actualSmallRoughRho retainOdd N cap w z L (a * b) ≠ 0 := by
    rwa [← hprod]
  rw [hprod, actualRho_mul_eq_signSensitive_lookup retainOdd N cap w z L ha hb,
    actual_selected_small_eq_moebius_of_rho_ne_zero retainOdd N cap w z L ha hb hnonzero,
    hrough]
  exact (mul_comm _ _).trans hmul.symm

/-- No discreteness premise: it follows from the actual weights and fibre. -/
theorem actualRho_zero_or_moebius
    (retainOdd : List ℕ → Bool) (N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    actualSmallRoughRho retainOdd N cap w z L q = 0 ∨
      actualSmallRoughRho retainOdd N cap w z L q = (ArithmeticFunction.moebius q : ℝ) := by
  by_cases hq : actualSmallRoughRho retainOdd N cap w z L q = 0
  · exact Or.inl hq
  · exact Or.inr (actualRho_eq_moebius_of_ne_zero retainOdd N cap w z L hq)

/-- The same literal physical coefficient for the actual compact third policy. -/
theorem actualCompactThirdRho_zero_or_moebius
    (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) (q : ℕ) :
    actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L q = 0 ∨
      actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L q =
        (ArithmeticFunction.moebius q : ℝ) := by
  exact actualRho_zero_or_moebius (actualExtendedThirdCompactUpperPolicy e h m N false)
    N cap w z L q

theorem actualCompactThirdRho_eq_moebius_of_ne_zero
    (e h : ℝ) (m N cap : ℕ) (w z L : ℝ) {q : ℕ}
    (hq : actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L q ≠ 0) :
    actualSmallRoughRho (actualExtendedThirdCompactUpperPolicy e h m N false) N cap w z L q =
      (ArithmeticFunction.moebius q : ℝ) := by
  exact actualRho_eq_moebius_of_ne_zero (actualExtendedThirdCompactUpperPolicy e h m N false)
    N cap w z L hq

end
end ImbalancedChen.P4APhysicalMoebiusLookup
