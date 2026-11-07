import ImbalancedChen.P0CausalExitFiniteResolvent

/-!
Local-error propagation for the same actual finite causal exit kernel.

The signed source difference is formed before the one outer absolute value.
Its majorant uses the absolute value of each actual edge coefficient, with
the identical policy, prime weight, inherited states and truncation length.
No row-norm, density or final-target estimate is assumed.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

theorem p0CausalExitKernel_abs {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    p0CausalExitKernel retained h states (fun i j => |c i j|) i j =
      |p0CausalExitKernel retained h states c i j| := by
  unfold p0CausalExitKernel
  split_ifs <;> simp only [abs_zero]

/-- Iteration retains the exact signed difference of the two local
sources; no error is charged separately to their common part. -/
theorem p0CausalExitIterate_sub {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (f g : Fin n → ℝ) (k : ℕ) :
    ∀ i, p0CausalExitIterate retained h states c f k i -
        p0CausalExitIterate retained h states c g k i =
      p0CausalExitIterate retained h states c (fun j => f j - g j) k i := by
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
      intro i
      change (∑ j, p0CausalExitKernel retained h states c i j *
          p0CausalExitIterate retained h states c f k j) -
        (∑ j, p0CausalExitKernel retained h states c i j *
          p0CausalExitIterate retained h states c g k j) =
        ∑ j, p0CausalExitKernel retained h states c i j *
          p0CausalExitIterate retained h states c (fun j => f j - g j) k j
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_sub, ih j]

/-- Absolute edge coefficients majorize each finite signed iterate. -/
theorem p0CausalExitIterate_abs_le {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (f : Fin n → ℝ) (k : ℕ) :
    ∀ i, |p0CausalExitIterate retained h states c f k i| ≤
      p0CausalExitIterate retained h states (fun i j => |c i j|)
        (fun j => |f j|) k i := by
  induction k with
  | zero => intro i; exact le_refl _
  | succ k ih =>
      intro i
      change |∑ j, p0CausalExitKernel retained h states c i j *
          p0CausalExitIterate retained h states c f k j| ≤
        ∑ j, p0CausalExitKernel retained h states (fun i j => |c i j|) i j *
          p0CausalExitIterate retained h states (fun i j => |c i j|)
            (fun j => |f j|) k j
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, p0CausalExitKernel_abs]
      exact mul_le_mul_of_nonneg_left (ih j) (abs_nonneg _)

/-- Positive majorant iterates preserve pointwise local source budgets. -/
theorem p0CausalExitIterate_absKernel_mono {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (f g : Fin n → ℝ) (hfg : ∀ i, f i ≤ g i) (k : ℕ) :
    ∀ i, p0CausalExitIterate retained h states (fun i j => |c i j|) f k i ≤
      p0CausalExitIterate retained h states (fun i j => |c i j|) g k i := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
      intro i
      change (∑ j, p0CausalExitKernel retained h states (fun i j => |c i j|) i j *
          p0CausalExitIterate retained h states (fun i j => |c i j|) f k j) ≤
        ∑ j, p0CausalExitKernel retained h states (fun i j => |c i j|) i j *
          p0CausalExitIterate retained h states (fun i j => |c i j|) g k j
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left (ih j)
      rw [p0CausalExitKernel_abs]
      exact abs_nonneg _

theorem p0CausalExitPartialSum_sub {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (L : ℕ) (f g : Fin n → ℝ) (i : Fin n) :
    p0CausalExitPartialSum retained h states c L f i -
        p0CausalExitPartialSum retained h states c L g i =
      p0CausalExitPartialSum retained h states c L (fun j => f j - g j) i := by
  unfold p0CausalExitPartialSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact p0CausalExitIterate_sub retained h states c f g k i

/-- Finite causal amplification of the actual local error. The right
side is a constructed positive matrix sum, not an assumed norm bound. -/
theorem p0CausalExitPartialSum_error_le {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (L : ℕ) (f g : Fin n → ℝ) (i : Fin n) :
    |p0CausalExitPartialSum retained h states c L f i -
        p0CausalExitPartialSum retained h states c L g i| ≤
      p0CausalExitPartialSum retained h states (fun i j => |c i j|)
        L (fun j => |f j - g j|) i := by
  rw [p0CausalExitPartialSum_sub]
  unfold p0CausalExitPartialSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact p0CausalExitIterate_abs_le retained h states c (fun j => f j - g j) k i

/-- Separately sized local budgets can be propagated through the same
positive finite resolvent, without bounding the signed sources separately. -/
theorem p0CausalExitPartialSum_error_le_budget {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (L : ℕ) (f g e : Fin n → ℝ) (he : ∀ j, |f j - g j| ≤ e j) (i : Fin n) :
    |p0CausalExitPartialSum retained h states c L f i -
        p0CausalExitPartialSum retained h states c L g i| ≤
      p0CausalExitPartialSum retained h states (fun i j => |c i j|) L e i := by
  apply (p0CausalExitPartialSum_error_le retained h states c L f g i).trans
  unfold p0CausalExitPartialSum
  apply Finset.sum_le_sum
  intro k _
  exact p0CausalExitIterate_absKernel_mono retained h states c _ e he k i

/-- Once the actual remaining-length truncation is chosen, this controls
the unique exact causal solutions, rather than only a finite approximation. -/
theorem p0CausalExit_solutions_error_le {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (c : Fin n → Fin n → ℝ)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L)
    (f g u v : Fin n → ℝ)
    (hu : ∀ i, u i = f i + p0CausalExitApply retained h states c u i)
    (hv : ∀ i, v i = g i + p0CausalExitApply retained h states c v i) (i : Fin n) :
    |u i - v i| ≤ p0CausalExitPartialSum retained h states (fun i j => |c i j|)
      L (fun j => |f j - g j|) i := by
  have heu : u = p0CausalExitPartialSum retained h states c L f :=
    p0CausalExit_solution_unique retained h states c L hL f u _ hu
      (p0CausalExitPartialSum_solution retained h states c L hL f)
  have hev : v = p0CausalExitPartialSum retained h states c L g :=
    p0CausalExit_solution_unique retained h states c L hL g v _ hv
      (p0CausalExitPartialSum_solution retained h states c L hL g)
  rw [heu, hev]
  exact p0CausalExitPartialSum_error_le retained h states c L f g i

/-- The original signed-exit source supplies its own finite truncation.
All transitions retain this same policy and prime weight. -/
theorem p0CausalExit_root_solutions_error_le {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ) (carrier : List α)
    (states : Fin n → FirstExitDepthState α)
    (hstates : ∀ i, states i ∈ p1SignedExitStates retained h [] true 1 carrier)
    (c : Fin n → Fin n → ℝ) (f g u v : Fin n → ℝ)
    (hu : ∀ i, u i = f i + p0CausalExitApply retained h states c u i)
    (hv : ∀ i, v i = g i + p0CausalExitApply retained h states c v i) (i : Fin n) :
    |u i - v i| ≤ p0CausalExitPartialSum retained h states (fun i j => |c i j|)
      carrier.length (fun j => |f j - g j|) i := by
  apply p0CausalExit_solutions_error_le retained h states c carrier.length _ f g u v hu hv i
  intro j
  have hr := p1_mem_exitStates_rank_bound retained h [] carrier true 1 (states j) (hstates j)
  simp only [List.length_nil, Nat.zero_add] at hr
  omega

end

end ImbalancedChen
