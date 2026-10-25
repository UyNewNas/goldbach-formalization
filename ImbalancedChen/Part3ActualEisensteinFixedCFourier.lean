import ImbalancedChen.Part3ActualEisensteinPrimitiveResidues
import ImbalancedChen.Part3RealPowerSeedConstantMode
import ImbalancedChen.Part3RamanujanSpecialCase
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED, 2026-10-25.

Fourier coefficients of the ACTUAL full primitive d block at each positive
c with N|c. The genuine residue/translate reindex gives finite unit sums of
periodized power seeds. The shift phase is proved by periodic interval
integration; its finite unit sum is the actual project Ramanujan sum.
Thus n=0 gives phi(c) times the proved Gamma quotient, while n!=0 gives
the actual Ramanujan(c,n) times the actual real-order K coefficient.
This does not yet assert convergence or evaluation of the infinite c sum.
-/

namespace ImbalancedChen.Part3.ActualEisensteinFixedCFourier20261025a

noncomputable section

open Set MeasureTheory
open scoped UpperHalfPlane
open ImbalancedChen.Part3.RealEisensteinSeedConvergence
open ImbalancedChen.Part3.PowerSeedGaussianLaplace
open ImbalancedChen.Part3.PowerSeedFourierLaplaceFubini
open ImbalancedChen.Part3.PowerSeedPeriodization
open ImbalancedChen.Part3.ActualEisensteinFourierInterchange20261025a
open ImbalancedChen.Part3.ActualEisensteinPrimitiveResidues20261025a
open ImbalancedChen.Part3.OriginalSmoothPoissonTail.Physical.ZeroMode

/-- The true integer periodization has period one, by integer reindexing. -/
theorem periodizedPowerSeed_periodic (s y : ℝ) :
    Function.Periodic (periodizedPowerSeed s y) 1 := by
  intro x
  change (∑' k : ℤ, powerSeed s y (x + 1 + (k : ℝ))) =
    ∑' k : ℤ, powerSeed s y (x + (k : ℝ))
  calc
    _ = ∑' k : ℤ, powerSeed s y (x + ((k + 1 : ℤ) : ℝ)) := by
      apply tsum_congr
      intro k
      congr 1
      push_cast
      ring
    _ = _ := (Equiv.addRight (1 : ℤ)).tsum_eq _

theorem shifted_periodized_phase_integrable {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (n : ℤ) (a : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => fourierPhase n x * (periodizedPowerSeed s y (x + a) : ℂ))
      volume 0 1 := by
  have hp : Continuous (fourierPhase n) := by unfold fourierPhase; fun_prop
  exact (hp.mul (Complex.continuous_ofReal.comp
    ((periodizedPowerSeed_continuous hs hy).comp (continuous_id.add_const a)))).intervalIntegrable 0 1

/-- The positive shift phase is proved, with the literal period-one sign. -/
theorem shifted_periodized_fourier {s y : ℝ}
    (hs : (1 / 2 : ℝ) < s) (hy : 0 < y) (n : ℤ) (a : ℝ) :
    (∫ x in (0 : ℝ)..1,
      fourierPhase n x * (periodizedPowerSeed s y (x + a) : ℂ)) =
      fourierPhase (-n) a *
        ∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ) := by
  have hphase (x : ℝ) :
      fourierPhase n x = fourierPhase (-n) a * fourierPhase n (x + a) := by
    unfold fourierPhase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hperiod : Function.Periodic
      (fun x : ℝ => fourierPhase n x * (periodizedPowerSeed s y x : ℂ)) 1 := by
    intro x
    have hp : fourierPhase n (x + 1) = fourierPhase n x := by
      simpa using fourierPhase_add_int n 1 x
    rw [hp, periodizedPowerSeed_periodic s y x]
  calc
    _ = fourierPhase (-n) a *
        ∫ x in (0 : ℝ)..1,
          fourierPhase n (x + a) * (periodizedPowerSeed s y (x + a) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _hx
      rw [hphase]
      ring
    _ = fourierPhase (-n) a *
        ∫ x in a..a + 1,
          fourierPhase n x * (periodizedPowerSeed s y x : ℂ) := by
      rw [intervalIntegral.integral_comp_add_right]
      simp only [zero_add, add_comm (1 : ℝ) a]
    _ = _ := by
      simpa only [zero_add] using congrArg (fun v : ℂ => fourierPhase (-n) a * v)
        (hperiod.intervalIntegral_add_eq a 0)

/-- Finite shift phases at the actual unit residues equal the ACTUAL
Ramanujan sum, with the positive arithmetic sign. -/
theorem unit_shift_phase_sum (c : ℕ) [NeZero c] (n : ℤ) :
    (∑ u : (ZMod c)ˣ,
      fourierPhase (-n) (((u : ZMod c).val : ℝ) / (c : ℝ))) = ramanujan c n := by
  rw [ramanujan_eq_units]
  apply Finset.sum_congr rfl
  intro u _hu
  have harg : (n : ZMod c) * (u : ZMod c) =
      ((n * ((u : ZMod c).val : ℤ) : ℤ) : ZMod c) := by simp
  rw [harg, ZMod.stdAddChar_coe]
  unfold fourierPhase
  congr 1
  push_cast
  ring

/-- The actual positive-c primitive block. -/
def fixedFirstBlock (N c : ℕ) (s y : ℝ) (hy : 0 < y) (x : ℝ) : ℝ :=
  ∑' d : PrimitiveD N (c : ℤ), seed s (horizontalPoint y hy x) ![(c : ℤ), d.1]

def fixedFirstFourier (N c : ℕ) (s y : ℝ) (hy : 0 < y) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, fourierPhase n x * (fixedFirstBlock N c s y hy x : ℂ)

/-- The coefficient of the FULL primitive d block, with actual c,N and
arithmetic Ramanujan factor, before the Gamma/K evaluation. -/
theorem fixedFirstFourier_eq_ramanujan (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) :
    fixedFirstFourier N c s y hy n =
      ((c : ℝ) ^ (-(2 * s)) : ℂ) * ramanujan c n *
        ∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ) := by
  have hs' : (1 / 2 : ℝ) < s := by linarith
  have hpoint (x : ℝ) :
      fourierPhase n x * (fixedFirstBlock N c s y hy x : ℂ) =
        ((c : ℝ) ^ (-(2 * s)) : ℂ) * ∑ u : (ZMod c)ˣ,
          fourierPhase n x *
            (periodizedPowerSeed s y (x + ((u : ZMod c).val : ℝ) / (c : ℝ)) : ℂ) := by
    rw [fixedFirstBlock, fixed_first_seed_eq_unit_periodization N c hNc s hs]
    push_cast
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _hu
    ring
  rw [fixedFirstFourier]
  calc
    _ = ∫ x in (0 : ℝ)..1,
        ((c : ℝ) ^ (-(2 * s)) : ℂ) * ∑ u : (ZMod c)ˣ,
          fourierPhase n x *
            (periodizedPowerSeed s y (x + ((u : ZMod c).val : ℝ) / (c : ℝ)) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      exact hpoint x
    _ = ((c : ℝ) ^ (-(2 * s)) : ℂ) * ∑ u : (ZMod c)ˣ,
        ∫ x in (0 : ℝ)..1, fourierPhase n x *
          (periodizedPowerSeed s y (x + ((u : ZMod c).val : ℝ) / (c : ℝ)) : ℂ) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun u _hu =>
          shifted_periodized_phase_integrable hs' hy n _)]
    _ = ((c : ℝ) ^ (-(2 * s)) : ℂ) *
        (∑ u : (ZMod c)ˣ,
          fourierPhase (-n) (((u : ZMod c).val : ℝ) / (c : ℝ))) *
        ∫ x in (0 : ℝ)..1, fourierPhase n x * (periodizedPowerSeed s y x : ℂ) := by
      simp_rw [shifted_periodized_fourier hs' hy]
      rw [← Finset.sum_mul]
      ring
    _ = _ := by rw [unit_shift_phase_sum]

/-- Zero mode of the ACTUAL primitive block: phi(c), with the exact
canonical Beta/Gamma height factor, is derived rather than supplied. -/
theorem fixedFirstFourier_zero (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) :
    fixedFirstFourier N c s y hy 0 =
      (((c : ℝ) ^ (-(2 * s)) * (c.totient : ℝ) *
        (Real.sqrt Real.pi * Real.Gamma (s - 1 / 2) / Real.Gamma s) * y ^ (1 - s) : ℝ) : ℂ) := by
  have hs' : (1 / 2 : ℝ) < s := by linarith
  rw [fixedFirstFourier_eq_ramanujan N c hNc s hs y hy 0,
    ramanujan_at_zero, periodizedPowerSeed_fourier_unfold hs' hy]
  simp only [fourierPhase, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
  rw [integral_ofReal, ImbalancedChen.Part3RealPowerSeedConstantMode.integral_powerSeed hs' hy]
  push_cast
  ring

/-- Nonzero mode of the ACTUAL primitive block: the arithmetic factor is
ramanujan(c,n), multiplied by the proved actual real-order K coefficient. -/
theorem fixedFirstFourier_nonzero (N c : ℕ) [NeZero c]
    (hNc : (N : ℤ) ∣ (c : ℤ)) (s : ℝ) (hs : 1 < s)
    (y : ℝ) (hy : 0 < y) (n : ℤ) (hn : n ≠ 0) :
    fixedFirstFourier N c s y hy n =
      ((c : ℝ) ^ (-(2 * s)) : ℂ) * ramanujan c n *
        (((2 * Real.pi ^ s / Real.Gamma s * |(n : ℝ)| ^ (s - 1 / 2) * Real.sqrt y *
          RealOrderKExceptionalSourceOnly.realOrderK (s - 1 / 2)
            (2 * Real.pi * |(n : ℝ)| * y) : ℝ) : ℂ)) := by
  rw [fixedFirstFourier_eq_ramanujan N c hNc s hs y hy n,
    periodizedPowerSeed_nonzero_fourier_actualK (by linarith : (1 / 2 : ℝ) < s) hy hn]

end
end ImbalancedChen.Part3.ActualEisensteinFixedCFourier20261025a