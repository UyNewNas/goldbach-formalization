import ImbalancedChen.P0CausalBuchstabProfileResidualBudget

/-!
Joint badness-parameter and polynomial-residual stability of the actual
sampled-profile causal system. Unlike a fixed-matrix source comparison,
both edge matrices are evaluated at their own badness parameters b,d.

The additional local error is an explicitly computed slope matrix applied
to the old polynomial response. It retains actual edge support and actual
signed approximate response values; no row norm or final sensitivity bound
is assumed. The source error is derived from primitive polynomial anchor
and differential residual records. SOURCE ONLY / UNCOMPILED / ZERO CREDIT.
The original full22 feedback-operator identification remains OPEN.
-/

namespace ImbalancedChen.P0CausalJointProfileResidualStability
noncomputable section
open Set P4B
open P0CausalProfileParameterDifferentiation P0CausalBuchstabProfileResidualBudget
open P0BuchstabDifferentialResidualTransfer
open Certificates.P2BuchstabPolynomialStep
open scoped Classical BigOperators

def edgeSlope {n : ℕ} (C width : ℝ) (a : Fin n → Fin n → ℝ)
    (point : Fin n → Fin n → Fin 2 → ℝ) (i j : Fin n) : ℝ :=
  |a i j| * ((C / width) * |point i j 1|)

/-- Actual physical-profile edge changes preserve the same literal causal
support and pay one inverse width and one second log coordinate. -/
theorem exists_kernel_profile_change_budget {α : Type*} {n : ℕ} :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (retained : Bool → List α → Bool) (h : α → ℝ)
        (states : Fin n → FirstExitDepthState α) (N : ℕ) (T width b d : ℝ),
      0 < width → ∀ (a : Fin n → Fin n → ℝ)
        (point : Fin n → Fin n → Fin 2 → ℝ) (i j : Fin n),
      |p0CausalExitKernel retained h states
        (fun i j => profileCoefficient N T width a point b i j -
          profileCoefficient N T width a point d i j) i j| ≤
        p0CausalExitKernel retained h states (edgeSlope C width a point) i j * |b - d| := by
  obtain ⟨C, hC, hprofile⟩ := exists_profile_badness_Lipschitz_budget
  refine ⟨C, hC, ?_⟩
  intro retained h states N T width b d hw a point i j
  by_cases he : P0CausalExitEdge retained h (states i) (states j)
  · simp only [p0CausalExitKernel, if_pos he, profileCoefficient, ← mul_sub, abs_mul,
      edgeSlope]
    have hb := mul_le_mul_of_nonneg_left (hprofile width hw N T b d (point i j))
      (abs_nonneg (a i j))
    simpa only [mul_assoc] using hb
  · simp only [p0CausalExitKernel, if_neg he, abs_zero, zero_mul, le_refl]

/-- Full joint finite-horizon stability, derived from primitive residual
records and actual four-gate parameter variation. Constants precede every
source, edge sample, state, depth and physical parameter. -/
theorem exists_joint_response_budget {α : Type*} {n : ℕ} :
    ∃ Cs Ce : ℝ, 1 ≤ Cs ∧ 1 ≤ Ce ∧
      ∀ (retained : Bool → List α → Bool) (h : α → ℝ)
        (states : Fin n → FirstExitDepthState α)
        (N : ℕ) (T width b d R alpha eta : ℝ),
      0 < width → 2 ≤ R → 0 ≤ alpha → 0 ≤ eta →
      ∀ (seed argument : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ)
        (a : Fin n → Fin n → ℝ) (edgePoint : Fin n → Fin n → Fin 2 → ℝ)
        (p : ℕ → List ℚ) (depth L : ℕ),
      (∀ i, (states i).remaining.length < L) → R ≤ (depth : ℝ) + 2 →
      (∀ k < depth, |eval (p k) 2 - 1| ≤ alpha) →
      (∀ k < depth, ∀ t ∈ Icc (2 : ℝ) R,
        |eval (derivative (p k)) t - polynomialStages p k (t - 1)| ≤ eta) →
      (∀ i, argument i ∈ Icc (1 : ℝ) R) →
      ∀ i,
      |p0CausalExitPartialSum retained h states
          (profileCoefficient N T width a edgePoint b) L
          (exactSource N T width b seed argument point) i -
        p0CausalExitPartialSum retained h states
          (profileCoefficient N T width a edgePoint d) L
          (polynomialSource N T width d seed argument point p depth) i| ≤
      p0CausalExitPartialSum retained h states
        (fun j k => |profileCoefficient N T width a edgePoint b j k|) L
        (fun j => localBudget Cs R alpha eta width b d seed argument point p depth j +
          ∑ k, (p0CausalExitKernel retained h states (edgeSlope Ce width a edgePoint) j k *
            |b - d|) * |p0CausalExitPartialSum retained h states
              (profileCoefficient N T width a edgePoint d) L
              (polynomialSource N T width d seed argument point p depth) k|) i := by
  obtain ⟨Cs, hCs, hsource⟩ := exists_source_budget (n := n)
  obtain ⟨Ce, hCe, hedge⟩ := exists_kernel_profile_change_budget (α := α) (n := n)
  refine ⟨Cs, Ce, hCs, hCe, ?_⟩
  intro retained h states N T width b d R alpha eta hw hR halpha heta seed argument
    point a edgePoint p depth L hL hdepth hanchor hresidual harg i
  let cb := profileCoefficient N T width a edgePoint b
  let cd := profileCoefficient N T width a edgePoint d
  let F := exactSource N T width b seed argument point
  let G := polynomialSource N T width d seed argument point p depth
  let V := p0CausalExitPartialSum retained h states cd L G
  let r : Fin n → ℝ := fun j => F j - G j +
    p0CausalExitApply retained h states (fun j k => cb j k - cd j k) V j
  let e : Fin n → ℝ := fun j =>
    localBudget Cs R alpha eta width b d seed argument point p depth j +
      ∑ k, (p0CausalExitKernel retained h states (edgeSlope Ce width a edgePoint) j k *
        |b - d|) * |V k|
  have hs := hsource N T width b d R alpha eta hw hR halpha heta seed argument point
    p depth hdepth hanchor hresidual harg
  have hr (j : Fin n) : |r j| ≤ e j := by
    calc
      _ ≤ |F j - G j| +
          |p0CausalExitApply retained h states (fun j k => cb j k - cd j k) V j| :=
        abs_add_le _ _
      _ ≤ localBudget Cs R alpha eta width b d seed argument point p depth j +
          ∑ k, (p0CausalExitKernel retained h states (edgeSlope Ce width a edgePoint) j k *
            |b - d|) * |V k| := by
        apply add_le_add (hs j)
        unfold p0CausalExitApply
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (hedge retained h states N T width b d hw a edgePoint j k) (abs_nonneg _)
      _ = e j := rfl
  have heq := congrFun
    (response_coefficient_difference retained h states cb cd F G L hL) i
  change |p0CausalExitPartialSum retained h states cb L F i -
    p0CausalExitPartialSum retained h states cd L G i| ≤
      p0CausalExitPartialSum retained h states (fun j k => |cb j k|) L e i
  rw [heq]
  change |p0CausalExitPartialSum retained h states cb L r i| ≤ _
  unfold p0CausalExitPartialSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact (p0CausalExitIterate_abs_le retained h states cb r k i).trans
    (p0CausalExitIterate_absKernel_mono retained h states cb (fun j => |r j|) e hr k i)

end
end ImbalancedChen.P0CausalJointProfileResidualStability
