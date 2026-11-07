import ImbalancedChen.P5OriginalOrdinaryResidualArithmeticFactor

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

Global arithmetic-function reconstruction by the actual small/rough fibres.
The small coefficient is allowed to depend on the actual rough divisor d.
The equality is on all natural arguments, including zero and arguments
outside the prime carrier. It is not a convolution with a fixed beta.
-/

namespace ImbalancedChen.P5Z.OriginalOrdinaryResidualFibre

noncomputable section
open scoped BigOperators
open Classical
open OriginalOrdinaryBetaRegroup OriginalOrdinaryResidualArithmeticFactor
open MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

/-- Conditional fibre sum, retaining the actual rough divisor in the
residual level and in the upper/lower selection. -/
def residualArithmeticFunction (N cap : ℕ) (w Z L : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun q => ∑ d∈roughSupport N cap w Z, ∑ e∈actualSmallRosserSupport N cap w,
    if e*d=q then roughWeight N cap w Z L d * residualSmallWeight N cap w L d e else 0,
    by
      apply Finset.sum_eq_zero
      intro d hd
      apply Finset.sum_eq_zero
      intro e he
      have hne : e*d≠0 := mul_ne_zero
        (actualSmallRosserSupport_smallPrimeSupportedAt N cap w he).1
        (roughSupport_rough hd).1
      simp only [hne,if_false]⟩

@[simp] theorem residualArithmeticFunction_apply (N cap q : ℕ) (w Z L : ℝ) :
    residualArithmeticFunction N cap w Z L q =
      ∑ d∈roughSupport N cap w Z, ∑ e∈actualSmallRosserSupport N cap w,
        if e*d=q then roughWeight N cap w Z L d * residualSmallWeight N cap w L d e else 0 := rfl

/-- Equality of genuine arithmetic functions, not just an identity at an
active row. Every q is reconstructed from its unique separated fibre when
one exists, and receives zero when no fibre exists. -/
theorem upperWeight_eq_residualArithmeticFunction (N cap : ℕ) {w Z : ℝ}
    (hwZ : w≤Z) (L : ℝ) :
    upperWeight (actualSmallPrimeProduct N cap Z) L =
      residualArithmeticFunction N cap w Z L := by
  ext q
  change actualSmallRosserPlus N cap Z L q = residualArithmeticFunction N cap w Z L q
  have hdelta : (∑ r∈actualSmallRosserSupport N cap Z,
      actualSmallRosserPlus N cap Z L r * (if r=q then (1:ℝ) else 0)) =
      actualSmallRosserPlus N cap Z L q := by
    rw [Finset.sum_eq_single q]
    · simp
    · intro r _hr hne
      simp only [hne,if_false,mul_zero]
    · intro hnot
      have hz : actualSmallRosserPlus N cap Z L q=0 := by
        by_contra h
        exact hnot (actualSmallRosserPlus_active h).1
      simp only [hz,zero_mul]
  calc
    actualSmallRosserPlus N cap Z L q =
        ∑ r∈actualSmallRosserSupport N cap Z,
          actualSmallRosserPlus N cap Z L r * (if r=q then (1:ℝ) else 0) := hdelta.symm
    _ = ∑ e∈actualSmallRosserSupport N cap w, ∑ d∈roughSupport N cap w Z,
          actualSmallRosserPlus N cap Z L (e*d) * (if e*d=q then (1:ℝ) else 0) :=
      native_sum_split N cap hwZ L (fun r=>if r=q then (1:ℝ) else 0)
    _ = ∑ d∈roughSupport N cap w Z, ∑ e∈actualSmallRosserSupport N cap w,
          if e*d=q then roughWeight N cap w Z L d * residualSmallWeight N cap w L d e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [native_upper_residual_factor_on_support hwZ he hd]
      by_cases h : e*d=q <;> simp only [h,if_true,if_false,mul_one,mul_zero]
    _ = residualArithmeticFunction N cap w Z L q := rfl

/-- Exact signed action on every test function. The small sum remains
inside the rough sum with its literal d-dependent level L/d. -/
theorem native_test_residual_factor (N cap : ℕ) {w Z : ℝ} (hwZ : w≤Z)
    (L : ℝ) (F : ℕ→ℝ) :
    (∑ q∈actualSmallRosserSupport N cap Z,actualSmallRosserPlus N cap Z L q*F q)=
    ∑ d∈roughSupport N cap w Z,roughWeight N cap w Z L d *
      ∑ e∈actualSmallRosserSupport N cap w,residualSmallWeight N cap w L d e*F (e*d) := by
  rw [native_sum_split N cap hwZ L F,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [native_upper_residual_factor_on_support hwZ he hd]
  ring

end
end ImbalancedChen.P5Z.OriginalOrdinaryResidualFibre
