import ImbalancedChen.P3ActualEvenLowerActiveSmallLogMoment
import Mathlib.Tactic

/-!
P3.6: eliminate the independent first-prime moment input for the
ACTUAL even-first-exit LOWER quotient-prime correction.
Frozen manuscript: UyNewNas/chen-imbalanced-semiprimes@
9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §1(PP), §3(T), §4(F).

For a finite set of nonnegative weights, the full Euler product
dominates ONE PLUS their sum. This is a genuine elementary payment:
the previous actual U6 bound needed both roughEulerMass E and its
separate prime sum J. Here J <= E, leaving just E. No fixed rank cap,
unproved prime estimate, extra rho field, or source replacement.

This does NOT show E <= log(N)^O(1). The original causal rho_N,
all PP sources, arithmetic discrepancy and Fourier tail remain open.
SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
-/

namespace ImbalancedChen.P3ActualEvenLowerOneEulerMoment
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen
open ImbalancedChen.P3ActualRetainedRoughEulerMass
open ImbalancedChen.P3ActualEvenLowerRoughPrimeMoment
open ImbalancedChen.P3ActualEvenLowerActiveSmallLogMoment
open ImbalancedChen.P3ActualRawActiveLevelTotientCap

/-- Elementary finite Euler inequality. The +1 is the empty subset;
all other singleton terms are already inside the product. -/
theorem finite_euler_one_add_sum_le_prod
    (P : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, 0 ≤ f p) :
    1 + (∑ p ∈ P, f p) ≤ ∏ p ∈ P, (1 + f p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      have hfp : 0 ≤ f p := hf p (Finset.mem_insert_self p P)
      have hfP : ∀ q ∈ P, 0 ≤ f q := by
        intro q hq
        exact hf q (Finset.mem_insert_of_mem hq)
      have hih :
          1 + (∑ q ∈ P, f q) ≤ ∏ q ∈ P, (1 + f q) := ih hfP
      have hsum : 0 ≤ ∑ q ∈ P, f q :=
        Finset.sum_nonneg (fun q hq => hfP q hq)
      have hprod : 1 ≤ ∏ q ∈ P, (1 + f q) := by
        linarith
      have hscale :
          f p ≤ f p * (∏ q ∈ P, (1 + f q)) := by
        calc
          f p = f p * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hprod hfp
      rw [Finset.sum_insert hp, Finset.prod_insert hp]
      calc
        1 + (f p + ∑ q ∈ P, f q) =
            (1 + ∑ q ∈ P, f q) + f p := by ring
        _ ≤ (∏ q ∈ P, (1 + f q)) + f p :=
          add_le_add_right hih _
        _ ≤ (∏ q ∈ P, (1 + f q)) +
            f p * (∏ q ∈ P, (1 + f q)) :=
          add_le_add_left hscale _
        _ = (1 + f p) * (∏ q ∈ P, (1 + f q)) := by ring

/-- Same original finite rough universe. The first moment requires
NO additional analytic upper bound once the Euler mass is controlled. -/
theorem rough_prime_sum_add_one_le_euler
    (N cap : ℕ) (w z : ℝ) :
    1 + (∑ p ∈ roughPrimeFinset N cap w z, roughPrimeInvPhi p) ≤
      roughEulerMass N cap w z := by
  simpa only [roughEulerMass, roughPrimeInvPhi] using
    (finite_euler_one_add_sum_le_prod
      (roughPrimeFinset N cap w z) roughPrimeInvPhi
      (fun p hp => by
        unfold roughPrimeInvPhi
        positivity))

/-- A deliberately weaker no-subtraction form, convenient for the
nonnegative signed-correction bound. -/
theorem rough_prime_sum_le_euler
    (N cap : ℕ) (w z : ℝ) :
    (∑ p ∈ roughPrimeFinset N cap w z, roughPrimeInvPhi p) ≤
      roughEulerMass N cap w z := by
  have h := rough_prime_sum_add_one_le_euler N cap w z
  linarith

/-- The exact INTEGER even-first-exit LOWER rho, its ORIGINAL U6 row,
the STRICT small Rosser activity, and the full physical b*q denominator
now need only a SINGLE rough Euler quantity E, not an independent J.

No log(N)-power upper bound for E is asserted: its uniform control is
still an internal mathematical obligation, not an external axiom. -/
theorem actual_U6_lower_quotient_prime_correction_abs_le_one_euler
    (N A : ℕ) (t : ℕ × ℕ) (ht : t ∈ sixthSupport N)
    (policy : (ℕ × ℕ) → List ℕ → Bool)
    (w L : (ℕ × ℕ) → ℝ)
    (hwz : w t ≤ P5CausalRhoQuotientBridge.cutoff N)
    (hLA : L t ≤ (A : ℝ)) :
    let z := P5CausalRhoQuotientBridge.cutoff N
    let cap := Nat.ceil z
    let b := t.1 * t.2
    let Q := actualLowerSmallRoughModuli (policy t) N cap (w t) z
    let rho := actualEvenLowerIntegerRho (policy t) N cap (w t) z (L t)
    |∑ q ∈ Q, (rho q : ℝ) *
      (chenPrimeDivisorCount N q / (Nat.totient (b * q) : ℝ))| ≤
    (Nat.totient b : ℝ)⁻¹ *
      (logTotientCap A * roughEulerMass N cap (w t) z *
        ((Nat.log 2 A : ℝ) + roughEulerMass N cap (w t) z)) := by
  have hstart :=
    actual_U6_lower_quotient_prime_correction_abs_le_log_euler
      N A t ht policy w L hwz hLA
  dsimp at hstart ⊢
  let z := P5CausalRhoQuotientBridge.cutoff N
  let cap := Nat.ceil z
  let E := roughEulerMass N cap (w t) z
  let J := ∑ p ∈ roughPrimeFinset N cap (w t) z, roughPrimeInvPhi p
  have hJplus : 1 + J ≤ E :=
    rough_prime_sum_add_one_le_euler N cap (w t) z
  have hJ0 : 0 ≤ J := Finset.sum_nonneg (fun p hp => by
    unfold roughPrimeInvPhi
    positivity)
  have hJ : J ≤ E := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hterm :
      logTotientCap A * (E * J) ≤
        logTotientCap A * (E * E) := by
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hJ hE0)
      (logTotientCap_nonneg A)
  calc
    _ ≤ (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (((Nat.log 2 A : ℝ) * logTotientCap A) * E +
          logTotientCap A * (E * J)) := hstart
    _ ≤ (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (((Nat.log 2 A : ℝ) * logTotientCap A) * E +
          logTotientCap A * (E * E)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_left hterm _) (by positivity)
    _ = (Nat.totient (t.1 * t.2) : ℝ)⁻¹ *
        (logTotientCap A * E * ((Nat.log 2 A : ℝ) + E)) := by ring

end
end ImbalancedChen.P3ActualEvenLowerOneEulerMoment
