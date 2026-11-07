import ImbalancedChen.P3ActualMarkedResidualExactProduct
import ImbalancedChen.P3ShiftedDivisorFiniteMoment

/-!
P3.6 original marked full-product nonzero-shift divisor bridge.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Manuscript 9731290, completion note sections 1, 3 (T), 4 (F).

The actual physical integer is r*n, not the residual n.
The same original q and signed rho, literal Mobius factor and exact
coprime mean survive. The zero shift is excluded before divisors.
No arithmetic moment, Fourier regularity or all-atom coverage is assumed.
-/

namespace ImbalancedChen.P3ActualMarkedOffShiftDivisors
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualWeightedFineSameRho
open ImbalancedChen.P3ActualMarkedResidualExactProduct
open ImbalancedChen.P3FullModulusShiftedMoment
open ImbalancedChen.P3ShiftedDivisorFiniteMoment

/-- Divisor argument for the COMPLETE marked physical product. -/
def markedShiftAbs (r T n : ℕ) : ℕ :=
  ((T : ℤ) - ((r * n : ℕ) : ℤ)).natAbs

/-- The off-complete-product source never calls divisors at zero. -/
theorem markedShiftAbs_ne_zero (r T n : ℕ)
    (hne : r * n ≠ T) : markedShiftAbs r T n ≠ 0 := by
  have hp : (∏ _j : Fin 1, r * n) ≠ T := by simpa using hne
  simpa [markedShiftAbs, shiftAbs] using
    (shiftAbs_ne_zero T (fun _ : Fin 1 => r * n) hp)

/-- Exact diagonal if and only if the full marked shift vanishes. -/
theorem markedShiftAbs_eq_zero_iff (r T n : ℕ) :
    markedShiftAbs r T n = 0 ↔ r * n = T := by
  constructor
  · intro hz
    by_contra hn
    exact (markedShiftAbs_ne_zero r T n hn) hz
  · intro heq
    simp [markedShiftAbs, heq]

/-- Literal physical congruence is divisibility by the NONZERO signed
shift T-r*n, retaining the complete-product coprime mean. -/
theorem fineKernel_marked_off_divisors (r T q n : ℕ)
    (hne : r * n ≠ T) :
    fineKernel T q (r * n) =
      (if q ∈ (markedShiftAbs r T n).divisors then (1 : ℝ) else 0) -
      (if Nat.Coprime (r * n) q
        then (Nat.totient q : ℝ)⁻¹ else 0) := by
  have hp : (∏ _j : Fin 1, r * n) ≠ T := by simpa using hne
  have hmod :
      (r * n) % q = T % q ↔
        (q : ℤ) ∣ (T : ℤ) - ((r * n : ℕ) : ℤ) := by
    simpa only [Nat.ModEq] using
      (Nat.modEq_iff_dvd (n := q) (a := r * n) (b := T))
  have hindicator :
      (if (r * n) % q = T % q then (1 : ℝ) else 0) =
        shiftedResidueKernel T q (fun _ : Fin 1 => r * n) := by
    unfold shiftedResidueKernel
    have hs : (∏ _j : Fin 1, r * n) = r * n := by simp
    rw [hs]
    by_cases hc : (r * n) % q = T % q
    · simp [hc, hmod.mp hc]
    · have hd : ¬ ((q : ℤ) ∣ (T : ℤ) - ((r * n : ℕ) : ℤ)) :=
        fun hh => hc (hmod.mpr hh)
      simp [hc, hd]
  have hshift := shiftedResidueKernel_eq_divisors
    T q (fun _ : Fin 1 => r * n) hp
  calc
    fineKernel T q (r * n) =
      (if (r * n) % q = T % q then (1 : ℝ) else 0) -
      (if Nat.Coprime (r * n) q
        then (Nat.totient q : ℝ)⁻¹ else 0) :=
        fineKernel_literal T q (r * n)
    _ = shiftedResidueKernel T q (fun _ : Fin 1 => r * n) -
      (if Nat.Coprime (r * n) q
        then (Nat.totient q : ℝ)⁻¹ else 0) := by rw [hindicator]
    _ = _ := by rw [hshift]; simp [markedShiftAbs, shiftAbs]

/-- Actual complex marked Möbius kernel, with no residual-only
congruence or uncontrolled mean substitution. -/
theorem markedResidualKernel_off_divisors (r T q n : ℕ)
    (hne : r * n ≠ T) :
    markedResidualKernel r T q n =
      (((ArithmeticFunction.moebius (r * n) : ℝ) : ℂ) *
       (((if q ∈ (markedShiftAbs r T n).divisors
            then (1 : ℝ) else 0) -
         (if Nat.Coprime (r * n) q
            then (Nat.totient q : ℝ)⁻¹ else 0)) : ℂ)) := by
  unfold markedResidualKernel
  rw [fineKernel_marked_off_divisors r T q n hne]

/-- On the genuinely sorted original prime source with arbitrary
tuple-dependent real W, the OFF full-product error is an exact divisor
sum minus the literal coprime mean. The SAME signed rho is retained. -/
theorem weightedSortedPP_off_divisors
    (N : ℕ) (τ : ℝ) (blocks : List (ℕ × ℕ))
    (Q : Finset ℕ) (rho : ℕ → ℝ) (T r : ℕ)
    (c : ℝ) (W : List ℕ → ℝ) :
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun ps => r * ps.prod ≠ T),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps * fineKernel T q (r * ps.prod)) =
    (∑ q ∈ Q, rho q *
      ∑ ps ∈ (actualPrimeFineLabelSortedTuples N τ blocks).filter
          (fun ps => r * ps.prod ≠ T),
        (c * (ArithmeticFunction.moebius (r * ps.prod) : ℝ)) *
          W ps *
            ((if q ∈ (markedShiftAbs r T ps.prod).divisors
              then (1 : ℝ) else 0) -
             (if Nat.Coprime (r * ps.prod) q
              then (Nat.totient q : ℝ)⁻¹ else 0))) := by
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  apply Finset.sum_congr rfl
  intro ps hps
  rw [fineKernel_marked_off_divisors
    r T q ps.prod (Finset.mem_filter.mp hps).2]

end
end ImbalancedChen.P3ActualMarkedOffShiftDivisors
