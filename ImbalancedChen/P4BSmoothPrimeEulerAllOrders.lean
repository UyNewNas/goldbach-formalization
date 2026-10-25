import ImbalancedChen.P4BSmoothPrimeVariableProfile
import ImbalancedChen.P4BSmoothProfileDirectionalDerivativeBudget
import ImbalancedChen.P4BSmoothProfileCommonCompactSupport

/-!
# All-order Euler-line budget for the actual four-wall prime profile

SOURCE ONLY / YELLOW / UNCOMPILED (2026-10-25).

The prime coordinates vary on a genuine multiplicative real orbit. Their
normalized logarithms are exactly an affine line, so the all-order actual
four-gate directional theorem applies. The resulting constant is independent
of N, of the prime-variable base point, and of the Euler direction. This
proves repeated Euler derivatives along every fixed direction; identifying
all mixed Euler partials with a uniform family of constants is a separate
multivariable polarization step and is not asserted here.
-/

namespace ImbalancedChen.P4B

noncomputable section

open ImbalancedChen.P4BSmoothProfileCommonCompactSupport

/-- Multiplicative orbit in the genuine positive prime-variable space. -/
def primeEulerOrbit (p h : Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => p i * Real.exp (t * h i)

theorem primeEulerOrbit_mem_positivePrimeOrthant
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (h : Fin 2 → ℝ) (t : ℝ) :
    primeEulerOrbit p h t ∈ positivePrimeOrthant := by
  intro i
  exact mul_pos (hp i) (Real.exp_pos _)

/-- The exact varying-log identity; there is no affine approximation. -/
theorem primeVariableLogPoint_primeEulerOrbit
    (N : ℕ) {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant)
    (h : Fin 2 → ℝ) (t : ℝ) :
    primeVariableLogPoint N (primeEulerOrbit p h t) =
      primeVariableLogPoint N p + t •
        (fun i : Fin 2 => h i / Real.log (N : ℝ)) := by
  funext i
  simp only [primeVariableLogPoint, primeEulerOrbit, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Real.log_mul (hp i).ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- The actual prime-variable weight on an Euler orbit equals the existing
four-wall physical profile along its exact normalized logarithmic line. -/
theorem smoothPrimeVariableProfile_eulerOrbit_eq_line
    (b : ℝ) (N : ℕ) (T width : ℝ)
    {p : Fin 2 → ℝ} (hp : p ∈ positivePrimeOrthant) (h : Fin 2 → ℝ) :
    (fun t => smoothPrimeVariableProfile b N T width (primeEulerOrbit p h t)) =
      smoothPhysicalProfileLine b N T width (primeVariableLogPoint N p)
        (fun i : Fin 2 => h i / Real.log (N : ℝ)) := by
  funext t
  change smoothPhysicalProfile b N T width
    (primeVariableLogPoint N (primeEulerOrbit p h t)) =
      smoothPhysicalProfile b N T width
        (primeVariableLogPoint N p + t •
          (fun i : Fin 2 => h i / Real.log (N : ℝ)))
  rw [primeVariableLogPoint_primeEulerOrbit N hp h t]

/-- Exact four-wall support survives the varying-log pullback. -/
theorem smoothPrimeVariableProfile_nonzero_all_four_walls
    {b T width : ℝ} {N : ℕ} (hwidth : 0 < width)
    {p : Fin 2 → ℝ} (hnonzero : smoothPrimeVariableProfile b N T width p ≠ 0) :
    ∀ i : Fin 4,
      -width < smoothPhysicalProfileMargin b N T (primeVariableLogPoint N p) i := by
  exact smoothPhysicalProfile_nonzero_margin_support hwidth hnonzero

/-- Each fixed-order repeated Euler derivative has an explicit logarithmic
chain budget. The constant is selected before N, T, p, and h. -/
theorem exists_smoothPrimeVariableProfile_eulerLine_budget
    (k : ℕ) (b width : ℝ) (hwidth : 0 < width) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ p h : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
        |iteratedDeriv k
          (fun t => smoothPrimeVariableProfile b N T width (primeEulerOrbit p h t)) 0| ≤
          C * ((1 + Real.log (N : ℝ)) / Real.log (N : ℝ)) ^ k * ‖h‖ ^ k := by
  obtain ⟨C, hC, hphysical⟩ :=
    exists_smoothPhysicalProfile_directional_derivative_budget k b
  refine ⟨C / width ^ k, div_nonneg hC (pow_nonneg hwidth.le k), ?_⟩
  intro N hN T p h hp
  have hN1 : (1 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hscaled :
      ‖(fun i : Fin 2 => h i / Real.log (N : ℝ))‖ =
        (Real.log (N : ℝ))⁻¹ * ‖h‖ := by
    have heq : (fun i : Fin 2 => h i / Real.log (N : ℝ)) =
        (Real.log (N : ℝ))⁻¹ • h := by
      funext i
      simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlog)]
  rw [smoothPrimeVariableProfile_eulerOrbit_eq_line b N T width hp h]
  calc
    |iteratedDeriv k
      (smoothPhysicalProfileLine b N T width (primeVariableLogPoint N p)
        (fun i : Fin 2 => h i / Real.log (N : ℝ))) 0| ≤
      (C / width ^ k) * (1 + Real.log (N : ℝ)) ^ k *
        ‖(fun i : Fin 2 => h i / Real.log (N : ℝ))‖ ^ k :=
      hphysical width hwidth N hN T _ _
    _ = (C / width ^ k) * ((1 + Real.log (N : ℝ)) / Real.log (N : ℝ)) ^ k * ‖h‖ ^ k := by
      rw [hscaled, mul_pow, div_pow, inv_pow]
      ring

/-- The logarithmic chain factor has one N-independent upper bound for
all N at least two. This is the order-dependent PP-size conclusion for
Euler *lines*, with no polylogarithmic growth in N. -/
theorem exists_smoothPrimeVariableProfile_uniform_eulerLine_budget
    (k : ℕ) (b width : ℝ) (hwidth : 0 < width) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ T : ℝ,
      ∀ p h : Fin 2 → ℝ, p ∈ positivePrimeOrthant →
        |iteratedDeriv k
          (fun t => smoothPrimeVariableProfile b N T width (primeEulerOrbit p h t)) 0| ≤
          C * ‖h‖ ^ k := by
  obtain ⟨C, hC, hbudget⟩ :=
    exists_smoothPrimeVariableProfile_eulerLine_budget k b width hwidth
  let D : ℝ := C * (1 + 1 / Real.log 2) ^ k
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hbase : 0 ≤ 1 + 1 / Real.log 2 :=
    add_nonneg zero_le_one (div_nonneg zero_le_one hlog2.le)
  have hD : 0 ≤ D :=
    mul_nonneg hC (pow_nonneg hbase k)
  refine ⟨D, hD, ?_⟩
  intro N hN T p h hp
  have hNreal : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) hNreal)
  have hrecip : 1 / Real.log (N : ℝ) ≤ 1 / Real.log 2 :=
    div_le_div_of_nonneg_left (by norm_num) hlog2
      (Real.log_le_log (by norm_num) hNreal)
  have hratio : (1 + Real.log (N : ℝ)) / Real.log (N : ℝ) ≤
      1 + 1 / Real.log 2 := by
    have hid : (1 + Real.log (N : ℝ)) / Real.log (N : ℝ) =
        1 + 1 / Real.log (N : ℝ) := by
      field_simp [hlogN.ne']
      ring
    rw [hid]
    exact add_le_add_left hrecip 1
  have hpow : ((1 + Real.log (N : ℝ)) / Real.log (N : ℝ)) ^ k ≤
      (1 + 1 / Real.log 2) ^ k :=
    pow_le_pow_left₀ (div_nonneg (by positivity) hlogN.le) hratio k
  calc
    _ ≤ C * ((1 + Real.log (N : ℝ)) / Real.log (N : ℝ)) ^ k * ‖h‖ ^ k :=
      hbudget N hN T p h hp
    _ ≤ C * (1 + 1 / Real.log 2) ^ k * ‖h‖ ^ k :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hC) (pow_nonneg (norm_nonneg h) k)
    _ = D * ‖h‖ ^ k := rfl

end

end ImbalancedChen.P4B
