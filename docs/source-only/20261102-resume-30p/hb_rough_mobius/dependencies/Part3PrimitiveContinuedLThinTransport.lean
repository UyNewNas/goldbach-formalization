import ImbalancedChen.Part3PrimitiveInductionEulerThin

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Quantitative primitive-to-original transport for the actual continued
Dirichlet L-function on Re(s)>=3/4. The exact associated primitive
character and induction identity come from the existing primary supplier;
they are not reconstructed or replaced by abstract input data.

The reciprocal comparison is unconditional on either L-value being
nonzero: total complex inversion and the exact nonzero Euler product make
it valid even at zeros. A separate equivalence transports genuine
nonvanishing. Logarithmic derivative transport requires primitive
nonvanishing and pays the proved 3 log q finite correction.

The conductor divides q and is <=q by the primary conductor_dvd_level
and Nat.le_of_dvd. Primary primitiveCharacter_isPrimitive,
primitiveCharacter_ne_one_of_ne_one, primitiveCharacter_sq_eq_one supply
the primitive/nonprincipal/quadratic hypotheses to the contour consumer.
No unknown left-strip norm, rectangle zero-free statement, or L(1) lower
bound is assumed in the reciprocal comparison itself.
-/

namespace ImbalancedChen.Part3.PrimitiveContinuedLThinTransport20261026b
noncomputable section
open Classical Complex DirichletCharacter
open scoped BigOperators
open PrimitiveInductionEulerThin20261026b

variable {q : ℕ} [NeZero q]
local instance (χ : DirichletCharacter ℂ q) : NeZero χ.conductor :=
  ⟨χ.conductor_ne_zero⟩

/-- Actual original and primitive L-values have precisely the same zeros
on this complex half-strip, including s=1 for a nonprincipal character. -/
theorem continuedL_ne_zero_iff_primitive (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    χ.LFunction s ≠ 0 ↔ χ.primitiveCharacter.LFunction s ≠ 0 := by
  rw [LFunction_eq_primitive_mul_inductionEulerProduct χ (Or.inl hχ)]
  simp only [mul_ne_zero_iff,
    (inductionEulerProduct_bounds χ.primitiveCharacter q hs).1,and_true]

theorem continuedL_ne_zero_of_primitive (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re)
    (hprimitive : χ.primitiveCharacter.LFunction s ≠ 0) : χ.LFunction s ≠ 0 :=
  (continuedL_ne_zero_iff_primitive χ hχ hs).mpr hprimitive

/-- No nonvanishing or unknown magnitude bound is an input. This is the
exact primitive reciprocal norm with the explicit original-modulus loss. -/
theorem continuedL_inverse_norm_le_primitive (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    ‖(χ.LFunction s)⁻¹‖ ≤ (q : ℝ)^2*‖(χ.primitiveCharacter.LFunction s)⁻¹‖ := by
  calc
    _ = ‖(inductionEulerProduct χ.primitiveCharacter q s)⁻¹‖*
        ‖(χ.primitiveCharacter.LFunction s)⁻¹‖ := by
      rw [LFunction_eq_primitive_mul_inductionEulerProduct χ (Or.inl hχ),
        mul_inv_rev,norm_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (inductionEulerProduct_bounds χ.primitiveCharacter q hs).2.2 (norm_nonneg _)

theorem continuedL_norm_le_primitive (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re) :
    ‖χ.LFunction s‖ ≤ (q : ℝ)*‖χ.primitiveCharacter.LFunction s‖ := by
  rw [LFunction_eq_primitive_mul_inductionEulerProduct χ (Or.inl hχ),norm_mul]
  calc
    _ ≤ ‖χ.primitiveCharacter.LFunction s‖*(q : ℝ) :=
      mul_le_mul_of_nonneg_left
        (inductionEulerProduct_bounds χ.primitiveCharacter q hs).2.1 (norm_nonneg _)
    _ = _ := mul_comm _ _

/-- Differentiate the existing all-s identity, not an Euler product
confined to Re(s)>1. Nonprincipal primitive L is entire. -/
theorem continuedL_logDeriv (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re)
    (hprimitive : χ.primitiveCharacter.LFunction s ≠ 0) :
    logDeriv χ.LFunction s = logDeriv χ.primitiveCharacter.LFunction s +
      logDeriv (inductionEulerProduct χ.primitiveCharacter q) s := by
  have hfun : χ.LFunction = fun w => χ.primitiveCharacter.LFunction w *
      inductionEulerProduct χ.primitiveCharacter q w :=
    funext (fun w => LFunction_eq_primitive_mul_inductionEulerProduct χ (Or.inl hχ))
  rw [hfun]
  exact logDeriv_mul s hprimitive
    (inductionEulerProduct_bounds χ.primitiveCharacter q hs).1
    (differentiable_LFunction (primitiveCharacter_ne_one_of_ne_one hχ) s)
    (inductionEulerProduct_differentiable χ.primitiveCharacter q s)

theorem continuedL_logDeriv_eq_prime_sum (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re)
    (hprimitive : χ.primitiveCharacter.LFunction s ≠ 0) :
    logDeriv χ.LFunction s = logDeriv χ.primitiveCharacter.LFunction s +
      ∑ p ∈ q.primeFactors,
        (χ.primitiveCharacter p*(p : ℂ)^(-s)*Complex.log (p : ℂ))/
          (1-χ.primitiveCharacter p*(p : ℂ)^(-s)) := by
  rw [continuedL_logDeriv χ hχ hs hprimitive,
    inductionEulerProduct_logDeriv χ.primitiveCharacter q hs]

theorem continuedL_logDeriv_correction_norm_le (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re)
    (hprimitive : χ.primitiveCharacter.LFunction s ≠ 0) :
    ‖logDeriv χ.LFunction s-logDeriv χ.primitiveCharacter.LFunction s‖ ≤
      3*Real.log (q : ℝ) := by
  rw [continuedL_logDeriv χ hχ hs hprimitive,add_sub_cancel_left]
  exact inductionEulerProduct_logDeriv_norm_le χ.primitiveCharacter q hs

theorem continuedL_logDeriv_norm_le_primitive (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (3/4 : ℝ) ≤ s.re)
    (hprimitive : χ.primitiveCharacter.LFunction s ≠ 0) :
    ‖logDeriv χ.LFunction s‖ ≤ ‖logDeriv χ.primitiveCharacter.LFunction s‖+
      3*Real.log (q : ℝ) := by
  rw [continuedL_logDeriv χ hχ hs hprimitive]
  exact (norm_add_le _ _).trans (add_le_add_left
    (inductionEulerProduct_logDeriv_norm_le χ.primitiveCharacter q hs) _)

end
end ImbalancedChen.Part3.PrimitiveContinuedLThinTransport20261026b
