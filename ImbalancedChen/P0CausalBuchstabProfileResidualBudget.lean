import ImbalancedChen.P0CausalProfileParameterDifferentiation
import ImbalancedChen.P0BuchstabDifferentialResidualTransfer

/-!
Primitive polynomial residuals to actual currentK/profile causal error.

The exact source is currentK * seed * actual Buchstab(argument) times the
literal four-wall physical profile at b. The approximation uses the actual
rational polynomial method of steps and may use a different badness d.
Only finite anchor and differential residual records are inputs; no true-
Buchstab error or final causal response budget is assumed.

The computed local cell error retains each actual polynomial value and
each actual second log coordinate. The same signed-exit coefficients then
propagate that error by their constructed absolute finite resolvent. The
Boolean policy and the coefficient evaluation b are fixed on this last
comparison; variation of the coefficient matrix is handled separately by
the exact two-coefficient identity in the imported differentiation module.

SOURCE ONLY / UNCOMPILED / ZERO PROOF CREDIT. Actual full22 feedback-operator
identification and production of original residual records remain OPEN.
-/

namespace ImbalancedChen.P0CausalBuchstabProfileResidualBudget
noncomputable section

open Set P4B LiLiuPrereqBuchstab
open P0CausalProfileParameterDifferentiation
open P0BuchstabDifferentialResidualTransfer P0BuchstabRenewalErrorPropagation
open Certificates.P2BuchstabPolynomialStep

open scoped Classical BigOperators

/-- Exact weighted splitting, taking the source difference before its
absolute value. The two errors refer to different primitive operations. -/
theorem weighted_product_error {a x y p q E D : ℝ}
    (hxy : |x - y| ≤ E) (hp : |p| ≤ 1) (hpq : |p - q| ≤ D) :
    |a * x * p - a * y * q| ≤ |a| * (E + |y| * D) := by
  have hfirst : |x - y| * |p| ≤ E := by
    calc
      _ ≤ |x - y| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
      _ = |x - y| := mul_one _
      _ ≤ E := hxy
  calc
    _ = |a| * |(x - y) * p + y * (p - q)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |a| * (|(x - y) * p| + |y * (p - q)|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ = |a| * (|x - y| * |p| + |y| * |p - q|) := by rw [abs_mul, abs_mul]
    _ ≤ |a| * (E + |y| * D) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hfirst (mul_le_mul_of_nonneg_left hpq (abs_nonneg _))) (abs_nonneg _)

def exactSource {n : ℕ} (N : ℕ) (T width b : ℝ)
    (seed argument : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ) (i : Fin n) : ℝ :=
  (currentK * seed i) * buchstab (argument i) *
    smoothPhysicalProfile b N T width (point i)

def polynomialSource {n : ℕ} (N : ℕ) (T width d : ℝ)
    (seed argument : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ)
    (p : ℕ → List ℚ) (depth : ℕ) (i : Fin n) : ℝ :=
  (currentK * seed i) * polynomialStages p depth (argument i) *
    smoothPhysicalProfile d N T width (point i)

/-- Constructed local budget. Its coefficient is the literal currentK,
not a replacement constant and not an assumed upper source estimate. -/
def localBudget {n : ℕ} (C1 R alpha eta width b d : ℝ)
    (seed argument : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ)
    (p : ℕ → List ℚ) (depth : ℕ) (i : Fin n) : ℝ :=
  |currentK * seed i| * (R * (alpha / 2 + contraction R * eta) / 2 +
    |polynomialStages p depth (argument i)| *
      (((C1 / width) * |point i 1|) * |b - d|))

/-- A single universal scalar-step constant works for every actual source
cell, every N,T, both badness parameters, and every primitive residual bank. -/
theorem exists_source_budget {n : ℕ} :
    ∃ C1 : ℝ, 1 ≤ C1 ∧
      ∀ (N : ℕ) (T width b d R alpha eta : ℝ), 0 < width → 2 ≤ R →
      0 ≤ alpha → 0 ≤ eta →
      ∀ (seed argument : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ)
        (p : ℕ → List ℚ) (depth : ℕ),
      R ≤ (depth : ℝ) + 2 →
      (∀ k < depth, |eval (p k) 2 - 1| ≤ alpha) →
      (∀ k < depth, ∀ t ∈ Icc (2 : ℝ) R,
        |eval (derivative (p k)) t - polynomialStages p k (t - 1)| ≤ eta) →
      (∀ i, argument i ∈ Icc (1 : ℝ) R) →
      ∀ i, |exactSource N T width b seed argument point i -
        polynomialSource N T width d seed argument point p depth i| ≤
        localBudget C1 R alpha eta width b d seed argument point p depth i := by
  obtain ⟨C1, hC1, hprofile⟩ := exists_profile_badness_Lipschitz_budget
  refine ⟨C1, hC1, ?_⟩
  intro N T width b d R alpha eta hw hR halpha heta seed argument point
    p depth hdepth hanchor hresidual harg i
  have hp := smoothPhysicalProfile_bounds b N T width (point i)
  have hactual := polynomialStages_error_actual hR halpha heta p depth hdepth
    hanchor hresidual (argument i) (harg i)
  have hactual' : |buchstab (argument i) - polynomialStages p depth (argument i)| ≤
      R * (alpha / 2 + contraction R * eta) / 2 := by
    simpa only [abs_sub_comm] using hactual
  exact weighted_product_error hactual'
    (by simpa only [abs_of_nonneg hp.1] using hp.2)
    (hprofile width hw N T b d (point i))

/-- The original polynomial anchor/differential records feed a finite
signed same-policy feedback response. There is no assumed final response
error or truefunction approximation input, and no absolute row-norm loss. -/
theorem exists_causal_response_budget {α : Type*} {n : ℕ} :
    ∃ C1 : ℝ, 1 ≤ C1 ∧
      ∀ (retained : Bool → List α → Bool) (h : α → ℝ)
        (states : Fin n → FirstExitDepthState α)
        (N : ℕ) (T width b d R alpha eta : ℝ),
      0 < width → 2 ≤ R → 0 ≤ alpha → 0 ≤ eta →
      ∀ (seed argument : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ)
        (a : Fin n → Fin n → ℝ) (edgePoint : Fin n → Fin n → Fin 2 → ℝ)
        (p : ℕ → List ℚ) (depth L : ℕ),
      R ≤ (depth : ℝ) + 2 →
      (∀ k < depth, |eval (p k) 2 - 1| ≤ alpha) →
      (∀ k < depth, ∀ t ∈ Icc (2 : ℝ) R,
        |eval (derivative (p k)) t - polynomialStages p k (t - 1)| ≤ eta) →
      (∀ i, argument i ∈ Icc (1 : ℝ) R) →
      ∀ i,
      |p0CausalExitPartialSum retained h states
          (profileCoefficient N T width a edgePoint b) L
          (exactSource N T width b seed argument point) i -
        p0CausalExitPartialSum retained h states
          (profileCoefficient N T width a edgePoint b) L
          (polynomialSource N T width d seed argument point p depth) i| ≤
      p0CausalExitPartialSum retained h states
        (fun j k => |profileCoefficient N T width a edgePoint b j k|) L
        (localBudget C1 R alpha eta width b d seed argument point p depth) i := by
  obtain ⟨C1, hC1, hsource⟩ := exists_source_budget (n := n)
  refine ⟨C1, hC1, ?_⟩
  intro retained h states N T width b d R alpha eta hw hR halpha heta
    seed argument point a edgePoint p depth L hdepth hanchor hresidual harg i
  exact p0CausalExitPartialSum_error_le_budget retained h states
    (profileCoefficient N T width a edgePoint b) L
    (exactSource N T width b seed argument point)
    (polynomialSource N T width d seed argument point p depth)
    (localBudget C1 R alpha eta width b d seed argument point p depth)
    (hsource N T width b d R alpha eta hw hR halpha heta seed argument point
      p depth hdepth hanchor hresidual harg) i

end
end ImbalancedChen.P0CausalBuchstabProfileResidualBudget
