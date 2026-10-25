import ImbalancedChen.P0CausalExitErrorPropagation
import ImbalancedChen.P4BSmoothPhysicalPairOuterRamp
import ImbalancedChen.P0VariableProfileCutoffVariation
import ImbalancedChen.CurrentNumericalTransfer
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
Parameter differentiation and exact coefficient-error transport for the
literal finite signed-exit recursion. The support is one fixed retained
policy, with the same states and prime weights at every parameter value.
No assertion is made across a change in that Boolean policy.

The manuscript keeps currentK fixed and records a future linear K feedback
slope (current-refinement-slope). Here currentK is retained literally in
the sampled source. The varying badness parameter b enters the actual four
physical gates, rather than an assumed regularity record. Derivatives are
constructed by the finite product rule. A second result controls changes
in BOTH the edge coefficients and the local source by one signed residual
and the actual absolute-coefficient finite resolvent. No contraction,
operator norm, final density estimate, or target error is a premise.

SOURCE ONLY / UNCOMPILED / ZERO ROOT PROOF CREDIT.
Identification of this finite response with the full22 manuscript feedback
operator and all prime distribution licences remain separate obligations.
-/

namespace ImbalancedChen.P0CausalProfileParameterDifferentiation

noncomputable section
open scoped Classical BigOperators ContDiff

section FiniteCausal
variable {α : Type*} {n : ℕ}
variable (retained : Bool → List α → Bool) (h : α → ℝ)
variable (states : Fin n → FirstExitDepthState α)

/-- The genuine product-rule recursion; both the edge and the propagated
source vary. There is no derivative of the Boolean edge predicate. -/
def tangentIterate (c dc : Fin n → Fin n → ℝ) (f df : Fin n → ℝ) :
    ℕ → Fin n → ℝ
  | 0, i => df i
  | k + 1, i => ∑ j,
      p0CausalExitKernel retained h states dc i j *
        p0CausalExitIterate retained h states c f k j +
      p0CausalExitKernel retained h states c i j *
        tangentIterate c dc f df k j

theorem kernel_hasDerivAt
    (c : ℝ → Fin n → Fin n → ℝ) (dc : Fin n → Fin n → ℝ) (b : ℝ)
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (dc i j) b) (i j : Fin n) :
    HasDerivAt (fun t => p0CausalExitKernel retained h states (c t) i j)
      (p0CausalExitKernel retained h states dc i j) b := by
  by_cases he : P0CausalExitEdge retained h (states i) (states j)
  · simpa only [p0CausalExitKernel, if_pos he] using hc i j
  · simpa only [p0CausalExitKernel, if_neg he] using
      (hasDerivAt_const b (0 : ℝ))

/-- Finite-delay differentiation, with an explicitly constructed tangent. -/
theorem iterate_hasDerivAt
    (c : ℝ → Fin n → Fin n → ℝ) (dc : Fin n → Fin n → ℝ)
    (f : ℝ → Fin n → ℝ) (df : Fin n → ℝ) (b : ℝ)
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (dc i j) b)
    (hf : ∀ i, HasDerivAt (fun t => f t i) (df i) b) (k : ℕ) :
    ∀ i, HasDerivAt
      (fun t => p0CausalExitIterate retained h states (c t) (f t) k i)
      (tangentIterate retained h states (c b) dc (f b) df k i) b := by
  induction k with
  | zero => exact hf
  | succ k ih =>
      intro i
      simpa only [p0CausalExitIterate, tangentIterate] using
        (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
          (kernel_hasDerivAt retained h states c dc b hc i j).mul (ih j)))

def tangentSum (c dc : Fin n → Fin n → ℝ) (f df : Fin n → ℝ)
    (L : ℕ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range L, tangentIterate retained h states c dc f df k i

theorem response_hasDerivAt
    (c : ℝ → Fin n → Fin n → ℝ) (dc : Fin n → Fin n → ℝ)
    (f : ℝ → Fin n → ℝ) (df : Fin n → ℝ) (b : ℝ)
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (dc i j) b)
    (hf : ∀ i, HasDerivAt (fun t => f t i) (df i) b) (L : ℕ) (i : Fin n) :
    HasDerivAt
      (fun t => p0CausalExitPartialSum retained h states (c t) L (f t) i)
      (tangentSum retained h states (c b) dc (f b) df L i) b := by
  exact HasDerivAt.fun_sum (fun k _ =>
    iterate_hasDerivAt retained h states c dc f df b hc hf k i)

/-- On a structurally sufficient finite horizon, the computed derivative
satisfies the differentiated exact causal equation, including T' u. -/
theorem tangentSum_equation
    (c : ℝ → Fin n → Fin n → ℝ) (dc : Fin n → Fin n → ℝ)
    (f : ℝ → Fin n → ℝ) (df : Fin n → ℝ) (b : ℝ)
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (dc i j) b)
    (hf : ∀ i, HasDerivAt (fun t => f t i) (df i) b)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) (i : Fin n) :
    tangentSum retained h states (c b) dc (f b) df L i =
      df i + p0CausalExitApply retained h states dc
        (p0CausalExitPartialSum retained h states (c b) L (f b)) i +
      p0CausalExitApply retained h states (c b)
        (tangentSum retained h states (c b) dc (f b) df L) i := by
  let U (t : ℝ) := p0CausalExitPartialSum retained h states (c t) L (f t)
  let V := tangentSum retained h states (c b) dc (f b) df L
  have hU (j : Fin n) : HasDerivAt (fun t => U t j) (V j) b :=
    response_hasDerivAt retained h states c dc f df b hc hf L j
  have hR : HasDerivAt
      (fun t => f t i + p0CausalExitApply retained h states (c t) (U t) i)
      (df i + ∑ j, (p0CausalExitKernel retained h states dc i j * U b j +
        p0CausalExitKernel retained h states (c b) i j * V j)) b :=
    (hf i).add (HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (kernel_hasDerivAt retained h states c dc b hc i j).mul (hU j)))
  have heq : (fun t => U t i) =
      (fun t => f t i + p0CausalExitApply retained h states (c t) (U t) i) := by
    funext t
    exact p0CausalExitPartialSum_solution retained h states (c t) L hL (f t) i
  have hleft := hU i
  rw [heq] at hleft
  have hu := hleft.unique hR
  simpa only [V, U, p0CausalExitApply, Finset.sum_add_distrib, add_assoc] using hu

/-- The derivative is itself the unique exact same-policy causal response
to df + T' u, rather than an assumed sensitivity bound. -/
theorem tangentSum_eq_response
    (c : ℝ → Fin n → Fin n → ℝ) (dc : Fin n → Fin n → ℝ)
    (f : ℝ → Fin n → ℝ) (df : Fin n → ℝ) (b : ℝ)
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (dc i j) b)
    (hf : ∀ i, HasDerivAt (fun t => f t i) (df i) b)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) :
    tangentSum retained h states (c b) dc (f b) df L =
      p0CausalExitPartialSum retained h states (c b) L
        (fun i => df i + p0CausalExitApply retained h states dc
          (p0CausalExitPartialSum retained h states (c b) L (f b)) i) := by
  apply p0CausalExit_solution_unique retained h states (c b) L hL
    (fun i => df i + p0CausalExitApply retained h states dc
      (p0CausalExitPartialSum retained h states (c b) L (f b)) i)
  · exact tangentSum_equation retained h states c dc f df b hc hf L hL
  · exact p0CausalExitPartialSum_solution retained h states (c b) L hL _

/-- A constructed quantitative derivative budget. The full signed local
linearization df + T' u is formed first, so its cancellations are retained. -/
theorem tangentSum_abs_le
    (c : ℝ → Fin n → Fin n → ℝ) (dc : Fin n → Fin n → ℝ)
    (f : ℝ → Fin n → ℝ) (df : Fin n → ℝ) (b : ℝ)
    (hc : ∀ i j, HasDerivAt (fun t => c t i j) (dc i j) b)
    (hf : ∀ i, HasDerivAt (fun t => f t i) (df i) b)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) (i : Fin n) :
    |tangentSum retained h states (c b) dc (f b) df L i| ≤
      p0CausalExitPartialSum retained h states (fun j k => |c b j k|) L
        (fun j => |df j + p0CausalExitApply retained h states dc
          (p0CausalExitPartialSum retained h states (c b) L (f b)) j|) i := by
  have heq := congrFun
    (tangentSum_eq_response retained h states c dc f df b hc hf L hL) i
  rw [heq]
  unfold p0CausalExitPartialSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact p0CausalExitIterate_abs_le retained h states (c b) _ k i

theorem kernel_sub (c d : Fin n → Fin n → ℝ) (i j : Fin n) :
    p0CausalExitKernel retained h states (fun i j => c i j - d i j) i j =
      p0CausalExitKernel retained h states c i j -
        p0CausalExitKernel retained h states d i j := by
  unfold p0CausalExitKernel
  split_ifs <;> simp

theorem apply_sub_source (c : Fin n → Fin n → ℝ) (f g : Fin n → ℝ) (i : Fin n) :
    p0CausalExitApply retained h states c (fun j => f j - g j) i =
      p0CausalExitApply retained h states c f i -
        p0CausalExitApply retained h states c g i := by
  simp only [p0CausalExitApply, mul_sub, Finset.sum_sub_distrib]

theorem apply_sub_coefficient (c d : Fin n → Fin n → ℝ) (g : Fin n → ℝ)
    (i : Fin n) :
    p0CausalExitApply retained h states (fun i j => c i j - d i j) g i =
      p0CausalExitApply retained h states c g i -
        p0CausalExitApply retained h states d g i := by
  simp only [p0CausalExitApply, kernel_sub, sub_mul, Finset.sum_sub_distrib]

/-- Exact two-coefficient resolvent identity. The old solution is charged
once against the actual edge-coefficient difference, with signs intact. -/
theorem response_coefficient_difference
    (c d : Fin n → Fin n → ℝ) (f g : Fin n → ℝ)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) :
    (fun i => p0CausalExitPartialSum retained h states c L f i -
      p0CausalExitPartialSum retained h states d L g i) =
    p0CausalExitPartialSum retained h states c L (fun i => f i - g i +
      p0CausalExitApply retained h states (fun i j => c i j - d i j)
        (p0CausalExitPartialSum retained h states d L g) i) := by
  apply p0CausalExit_solution_unique retained h states c L hL
    (fun i => f i - g i + p0CausalExitApply retained h states
      (fun i j => c i j - d i j) (p0CausalExitPartialSum retained h states d L g) i)
  · intro i
    rw [apply_sub_source, apply_sub_coefficient]
    have hu := p0CausalExitPartialSum_solution retained h states c L hL f i
    have hv := p0CausalExitPartialSum_solution retained h states d L hL g i
    linarith only [hu, hv]
  · exact p0CausalExitPartialSum_solution retained h states c L hL _

/-- Quantitative stability under coefficient AND source variation, with
the signed local residual formed before the absolute finite resolvent. -/
theorem response_coefficient_error_le
    (c d : Fin n → Fin n → ℝ) (f g : Fin n → ℝ)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) (i : Fin n) :
    |p0CausalExitPartialSum retained h states c L f i -
      p0CausalExitPartialSum retained h states d L g i| ≤
      p0CausalExitPartialSum retained h states (fun i j => |c i j|) L
        (fun j => |f j - g j + p0CausalExitApply retained h states
          (fun i j => c i j - d i j)
          (p0CausalExitPartialSum retained h states d L g) j|) i := by
  have heq := congrFun (response_coefficient_difference retained h states c d f g L hL) i
  rw [heq]
  unfold p0CausalExitPartialSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact p0CausalExitIterate_abs_le retained h states c _ k i

end FiniteCausal

section ActualProfile
open P4B

/-- The three gates independent of the moving badness parameter. -/
def badnessFreeProduct (N : ℕ) (T width : ℝ) (v : Fin 2 → ℝ) : ℝ :=
  (smoothGateUpperStep width (v 1 - v 0) *
    smoothGateUpperStep width (v 0 + v 1 - Real.log T / Real.log (N : ℝ))) *
    smoothGateUpperStep width (Real.log (N : ℝ) * (1 - v 0 - v 1))

theorem profile_eq_badnessFree_mul_gate (b : ℝ) (N : ℕ) (T width : ℝ)
    (v : Fin 2 → ℝ) :
    smoothPhysicalProfile b N T width v = badnessFreeProduct N T width v *
      smoothGateUpperStep width (v 0 - b * v 1) := by
  simp [smoothPhysicalProfile, Fin.prod_univ_four, smoothPhysicalProfileMargin,
    physicalProductWallScale, actualPairMargins, badnessFreeProduct] <;> ring

theorem badnessFreeProduct_bounds (N : ℕ) (T width : ℝ) (v : Fin 2 → ℝ) :
    0 ≤ badnessFreeProduct N T width v ∧ badnessFreeProduct N T width v ≤ 1 := by
  have h0 := smoothGateUpperStep_bounds width (v 1 - v 0)
  have h2 := smoothGateUpperStep_bounds width
    (v 0 + v 1 - Real.log T / Real.log (N : ℝ))
  have h3 := smoothGateUpperStep_bounds width
    (Real.log (N : ℝ) * (1 - v 0 - v 1))
  have h02 : smoothGateUpperStep width (v 1 - v 0) *
      smoothGateUpperStep width (v 0 + v 1 - Real.log T / Real.log (N : ℝ)) ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h0.2 h2.2 h2.1 zero_le_one
  constructor
  · exact mul_nonneg (mul_nonneg h0.1 h2.1) h3.1
  · simpa only [badnessFreeProduct, one_mul] using
      mul_le_mul h02 h3.2 h3.1 zero_le_one

/-- A universal badness-parameter budget with exactly one inverse width.
The physical upper gate contributes no log N loss to this derivative. -/
theorem exists_profile_badness_Lipschitz_budget :
    ∃ C1 : ℝ, 1 ≤ C1 ∧ ∀ width : ℝ, 0 < width →
      ∀ (N : ℕ) (T b d : ℝ) (v : Fin 2 → ℝ),
        |smoothPhysicalProfile b N T width v -
          smoothPhysicalProfile d N T width v| ≤
          ((C1 / width) * |v 1|) * |b - d| := by
  obtain ⟨C1, hC1, hstep⟩ :=
    P0VariableProfileCutoffVariation.exists_smoothGateUpperStep_first_Lipschitz_budget
  refine ⟨C1, hC1, ?_⟩
  intro width hw N T b d v
  have hH := badnessFreeProduct_bounds N T width v
  rw [profile_eq_badnessFree_mul_gate, profile_eq_badnessFree_mul_gate,
    ← mul_sub, abs_mul, abs_of_nonneg hH.1]
  calc
    _ ≤ |smoothGateUpperStep width (v 0 - b * v 1) -
        smoothGateUpperStep width (v 0 - d * v 1)| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hH.2
        (abs_nonneg (smoothGateUpperStep width (v 0 - b * v 1) -
          smoothGateUpperStep width (v 0 - d * v 1)))
    _ ≤ (C1 / width) * |(v 0 - b * v 1) - (v 0 - d * v 1)| :=
      hstep width hw _ _
    _ = ((C1 / width) * |v 1|) * |b - d| := by
      have he : (v 0 - b * v 1) - (v 0 - d * v 1) = (d - b) * v 1 := by ring
      rw [he, abs_mul, abs_sub_comm d b]
      ring

/-- Actual badness-parameter smoothness. This is not spatial smoothness
with b frozen: the only moving wall is v0-b*v1. -/
theorem contDiff_profile_badness (N : ℕ) (T width : ℝ) (v : Fin 2 → ℝ)
    {m : ℕ∞} : ContDiff ℝ m (fun b => smoothPhysicalProfile b N T width v) := by
  unfold smoothPhysicalProfile
  apply contDiff_prod
  intro i _
  apply (contDiff_smoothGateUpperStep width).comp
  unfold smoothPhysicalProfileMargin
  apply contDiff_const.mul
  fin_cases i
  · exact contDiff_const
  · change ContDiff ℝ m (fun b : ℝ => v 0 - b * v 1)
    exact contDiff_const.sub (contDiff_id.mul contDiff_const)
  · exact contDiff_const
  · exact contDiff_const

def profileCoefficient {n : ℕ} (N : ℕ) (T width : ℝ)
    (a : Fin n → Fin n → ℝ) (point : Fin n → Fin n → Fin 2 → ℝ)
    (b : ℝ) (i j : Fin n) : ℝ :=
  a i j * smoothPhysicalProfile b N T width (point i j)

/-- The original currentK is kept fixed, exactly as in the manuscript. -/
def currentKProfileSource {n : ℕ} (N : ℕ) (T width : ℝ)
    (seed : Fin n → ℝ) (point : Fin n → Fin 2 → ℝ)
    (b : ℝ) (i : Fin n) : ℝ :=
  currentK * seed i * smoothPhysicalProfile b N T width (point i)

/-- The actual sampled profile gives a differentiable finite same-policy
response at every b, including totalized zero width. Quantitative legal-
width licences and policy-wall changes are not consequences of this. -/
theorem actual_profile_response_hasDerivAt
    {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α)
    (N : ℕ) (T width : ℝ) (a : Fin n → Fin n → ℝ)
    (point : Fin n → Fin n → Fin 2 → ℝ)
    (seed : Fin n → ℝ) (seedPoint : Fin n → Fin 2 → ℝ)
    (L : ℕ) (b : ℝ) (i : Fin n) :
    HasDerivAt
      (fun t => p0CausalExitPartialSum retained h states
        (profileCoefficient N T width a point t) L
        (currentKProfileSource N T width seed seedPoint t) i)
      (tangentSum retained h states
        (profileCoefficient N T width a point b)
        (fun j k => deriv (fun t => profileCoefficient N T width a point t j k) b)
        (currentKProfileSource N T width seed seedPoint b)
        (fun j => deriv (fun t => currentKProfileSource N T width seed seedPoint t j) b)
        L i) b := by
  apply response_hasDerivAt
  · intro j k
    exact (((contDiff_profile_badness N T width (point j k) (m := 1)).differentiable_one b)
      .const_mul (a j k)).hasDerivAt
  · intro j
    exact (((contDiff_profile_badness N T width (seedPoint j) (m := 1)).differentiable_one b)
      .const_mul (currentK * seed j)).hasDerivAt

end ActualProfile
end
end ImbalancedChen.P0CausalProfileParameterDifferentiation
