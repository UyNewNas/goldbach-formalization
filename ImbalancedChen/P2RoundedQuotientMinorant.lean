import ImbalancedChen.P2LowerFiniteCellBetaCompiler
import ImbalancedChen.CurrentChenP5CausalRhoQuotientBridge

/-! Existing generic quotient minorant, extracted without proof changes.
Source: P2RoundedU6NativeJointLedger at c6b89774822580c731a236ac66dcd7466ac8a0e6.
This module changes dependency ownership only; verification is pending. -/

namespace ImbalancedChen.P2RoundedU6NativeJointLedger

noncomputable section
open scoped Classical BigOperators

/-- The new lower row is tested on the actual quotient receivers. It is
not obtained by pretending the rounded support is a retained tree. -/
theorem rounded_quotient_sum_le_sifted (keep : List ℕ → Bool)
    (N b cap : ℕ) (w z tau L : ℝ)
    (hL : 1 < L) (hwL : w ≤ L) (hwz : w ≤ z) (hzcap : z ≤ (cap : ℝ)) :
    (∑ d ∈ P2LowerFiniteCellBetaCompiler.support N cap w z,
      P2LowerFiniteCellBetaCompiler.rho keep N cap w z tau L d *
        (chenPrimeAPCount N N (b * d) - chenCentrePrimeAPCount N N (b * d))) ≤
      ((chenSiftedQuotientPrimeSource N b z).card : ℝ) := by
  rw [← P5CausalRhoQuotientBridge.quotient_sum_physicalDivisorSum]
  calc
    _ ≤ ∑ q ∈ chenQuotientPrimeSource N b,
        if ChenPrimeRough z q then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      have h := P2LowerFiniteCellBetaCompiler.rho_minorant keep N cap
        w z tau L hL hwL hwz hzcap (q : ℤ)
      have hind : actualSmallRoughIndicator N z (q : ℤ) =
          if Nat.Coprime q (sieveProduct N (Nat.ceil z)) then (1 : ℝ) else 0 := by
        unfold actualSmallRoughIndicator
        rw [← actualSmallPrimeProduct_coprime_natAbs_iff N cap z hzcap (q : ℤ)]
        simp only [Int.natAbs_natCast,
          currentChen_actualSmallPrimeProduct_eq_sieveProduct N cap z hzcap,
          Nat.coprime_comm]
      have hr := chenPrimeRough_iff_coprime_sieveProduct z
        (chenQuotientPrimeSource_data hq).2.2
      simpa only [Int.natAbs_natCast, hind, ← hr] using h
    _ = _ := by
      rw [← Finset.sum_filter]
      simp only [chenSiftedQuotientPrimeSource, Finset.sum_const, nsmul_eq_mul, mul_one]

end
end ImbalancedChen.P2RoundedU6NativeJointLedger
