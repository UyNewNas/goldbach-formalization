import ImbalancedChen.P4BSmoothPrimeVariableProfile
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget

/-!
# All-order Euler-flow normalization of the genuine prime-variable profile

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED, 2026-10-25.

The curve is the actual multiplicative flow p_i exp(t h_i), on positive
real prime variables. Its normalized logarithm is an affine line with
slope h/log N. The exact all-order chain rule and the existing proved
affine-line budget therefore cancel the physical wall's log N growth.
The resulting constant is independent of N, T, p and h, at fixed order,
b and positive width. No derivative estimate is assumed as a premise.

This module bounds derivatives along one Euler flow at every order.
Identification with iterates of the differential operator and bounds for
arbitrary mixed Euler words still require a separate polarization or
mixed-partial argument. It asserts no Part 3 licence or PP estimate.
-/

namespace ImbalancedChen.P4B

noncomputable section

/-- The genuine positive multiplicative flow in the two prime variables. -/
def primeEulerFlow (p h : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => p i * Real.exp (t * h i)

theorem primeEulerFlow_mem_positivePrimeOrthant
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (h : Fin 2 → ℝ) (t : ℝ) :
    primeEulerFlow p h t ∈ positivePrimeOrthant := by
  intro i
  exact mul_pos (hp i) (Real.exp_pos _)

@[simp] theorem primeEulerFlow_zero (p h : Fin 2 → ℝ) :
    primeEulerFlow p h 0 = p := by
  funext i
  simp [primeEulerFlow]

/-- The flow law holds pointwise, so the curve stays in its genuine
positive coordinate domain for arbitrarily large positive or negative time. -/
theorem primeEulerFlow_add (p h : Fin 2 → ℝ) (s t : ℝ) :
    primeEulerFlow p h (s + t) = primeEulerFlow (primeEulerFlow p h s) h t := by
  funext i
  simp only [primeEulerFlow, add_mul, Real.exp_add]
  ring

/-- Exact normalized log-coordinate identity; no asymptotic error and
no derivative licence enter this equation. Totalized division covers N=1. -/
theorem primeVariableLogPoint_primeEulerFlow (N : ℕ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (h : Fin 2 → ℝ) (t : ℝ) :
    primeVariableLogPoint N (primeEulerFlow p h t) =
      primeVariableLogPoint N p + ((Real.log (N : ℝ))⁻¹ * t) • h := by
  funext i
  simp only [primeVariableLogPoint, primeEulerFlow, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul,
    Real.log_mul (hp i).ne' (Real.exp_pos (t * h i)).ne', Real.log_exp]
  simp only [div_eq_mul_inv]
  ring

/-- Equality of genuine scalar functions before applying any derivative. -/
theorem smoothPrimeVariableProfile_primeEulerFlow_eq_line
    (b : ℝ) (N : ℕ) (T width : ℝ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) (h : Fin 2 → ℝ) :
    (fun t => smoothPrimeVariableProfile b N T width (primeEulerFlow p h t)) =
      fun t => smoothPhysicalProfileLine b N T width
        (primeVariableLogPoint N p) h ((Real.log (N : ℝ))⁻¹ * t) := by
  funext t
  unfold smoothPrimeVariableProfile smoothPhysicalProfileLine
  rw [primeVariableLogPoint_primeEulerFlow N hp]

/-- Exact all-order normalization, including order zero. The derivative
on the left is taken in the actual continuous prime-variable flow. -/
theorem iteratedDeriv_smoothPrimeVariableProfile_primeEulerFlow
    (k : ℕ) (b : ℝ) (N : ℕ) (T width : ℝ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (h : Fin 2 → ℝ) (t : ℝ) :
    iteratedDeriv k
      (fun s => smoothPrimeVariableProfile b N T width (primeEulerFlow p h s)) t =
      (Real.log (N : ℝ))⁻¹ ^ k *
        iteratedDeriv k (smoothPhysicalProfileLine b N T width
          (primeVariableLogPoint N p) h) ((Real.log (N : ℝ))⁻¹ * t) := by
  rw [smoothPrimeVariableProfile_primeEulerFlow_eq_line b N T width hp h]
  have hline : ContDiff ℝ ∞ (smoothPhysicalProfileLine b N T width
      (primeVariableLogPoint N p) h) := by
    exact (contDiff_smoothPhysicalProfile b N T width).comp
      (contDiff_const.add (contDiff_id.smul contDiff_const))
  simpa only [zero_add] using iteratedDeriv_comp_real_affine k
    (smoothPhysicalProfileLine b N T width (primeVariableLogPoint N p) h)
    hline 0 (Real.log (N : ℝ))⁻¹ t

/-- N-uniform normalization of the physical log-wall growth. -/
theorem physical_log_growth_normalized_le {N : ℕ} (hN : 2 ≤ N) :
    (Real.log (N : ℝ))⁻¹ * (1 + Real.log (N : ℝ)) ≤
      1 + (Real.log 2)⁻¹ := by
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogle : Real.log 2 ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by norm_num) hNreal
  have hlog : 0 < Real.log (N : ℝ) := htwo.trans_le hlogle
  have hinv : (Real.log (N : ℝ))⁻¹ ≤ (Real.log 2)⁻¹ := by
    simpa only [one_div] using
      div_le_div_of_nonneg_left zero_le_one htwo hlogle
  calc
    (Real.log (N : ℝ))⁻¹ * (1 + Real.log (N : ℝ)) =
        1 + (Real.log (N : ℝ))⁻¹ := by
      field_simp [hlog.ne']
      <;> ring
    _ ≤ 1 + (Real.log 2)⁻¹ := add_le_add_left hinv 1

/-- A constant chosen after k,b and before width,N,T,p,h controls all
orders of the genuine prime-variable Euler-flow curve at time zero.
There is no residual power of log N. The only scale loss is width^-k. -/
theorem exists_smoothPrimeVariableProfile_EulerFlow_derivative_budget
    (k : ℕ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ width : ℝ, 0 < width →
      ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ, ∀ p : Fin 2 → ℝ,
      p ∈ positivePrimeOrthant → ∀ h : Fin 2 → ℝ,
        |iteratedDeriv k
          (fun t => smoothPrimeVariableProfile b N T width (primeEulerFlow p h t)) 0| ≤
          (C / width ^ k) * ‖h‖ ^ k := by
  obtain ⟨C, hC, hbudget⟩ :=
    exists_smoothPhysicalProfile_directional_derivative_budget k b
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hscale : 0 ≤ 1 + (Real.log 2)⁻¹ :=
    add_nonneg zero_le_one (inv_nonneg.mpr htwo.le)
  refine ⟨C * (1 + (Real.log 2)⁻¹) ^ k,
    mul_nonneg hC (pow_nonneg hscale k), ?_⟩
  intro width hwidth N hN T p hp h
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hi : 0 ≤ (Real.log (N : ℝ))⁻¹ := inv_nonneg.mpr hlog.le
  have hnormalized : 0 ≤ (Real.log (N : ℝ))⁻¹ * (1 + Real.log (N : ℝ)) :=
    mul_nonneg hi (add_nonneg zero_le_one hlog.le)
  rw [iteratedDeriv_smoothPrimeVariableProfile_primeEulerFlow k b N T width hp h,
    mul_zero, abs_mul, abs_pow, abs_of_nonneg hi]
  calc
    (Real.log (N : ℝ))⁻¹ ^ k *
        |iteratedDeriv k (smoothPhysicalProfileLine b N T width
          (primeVariableLogPoint N p) h) 0| ≤
        (Real.log (N : ℝ))⁻¹ ^ k *
          ((C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k * ‖h‖ ^ k) :=
      mul_le_mul_of_nonneg_left
        (hbudget width hwidth N hN T (primeVariableLogPoint N p) h)
        (pow_nonneg hi k)
    _ = (C / width ^ k) * ‖h‖ ^ k *
        ((Real.log (N : ℝ))⁻¹ * (1 + Real.log (N : ℝ))) ^ k := by
      rw [mul_pow]
      ring
    _ ≤ (C / width ^ k) * ‖h‖ ^ k * (1 + (Real.log 2)⁻¹) ^ k :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hnormalized (physical_log_growth_normalized_le hN) k)
        (mul_nonneg (div_nonneg hC (pow_nonneg hwidth.le k))
          (pow_nonneg (norm_nonneg h) k))
    _ = ((C * (1 + (Real.log 2)⁻¹) ^ k) / width ^ k) * ‖h‖ ^ k := by ring

end

end ImbalancedChen.P4B
