import ImbalancedChen.P0CausalExitTriangularOrdering

/-!
Finite causal elimination for the actual signed-exit transition kernel.

The edge kernel, policy, prime weight, state list and signed coefficients
are the same in every iterate. Strict decrease of the inherited remaining
carrier makes the finite sum an exact inverse, without contraction or a
spectral bound. This is finite algebra only, not an analytic density mean.
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators

def p0CausalExitApply {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, p0CausalExitKernel retained h states coefficient i j * f j

/-- The finite causal resolvent, with the identity term included once. -/
def p0CausalExitPartialSum {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (L : ℕ) (f : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k ∈ Finset.range L, p0CausalExitIterate retained h states coefficient f k i

theorem p0CausalExitApply_partialSum {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (L : ℕ) (f : Fin n → ℝ) (i : Fin n) :
    p0CausalExitApply retained h states coefficient
        (p0CausalExitPartialSum retained h states coefficient L f) i =
      ∑ k ∈ Finset.range L,
        p0CausalExitIterate retained h states coefficient f (k + 1) i := by
  simp only [p0CausalExitApply, p0CausalExitPartialSum, Finset.mul_sum,
    p0CausalExitIterate]
  rw [Finset.sum_comm]

/-- Exact finite telescoping leaves only the last iterate as a residual.
No absolute values are introduced, so every signed transition is retained. -/
theorem p0CausalExitPartialSum_telescoping {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (L : ℕ) (f : Fin n → ℝ) (i : Fin n) :
    f i + p0CausalExitApply retained h states coefficient
        (p0CausalExitPartialSum retained h states coefficient L f) i =
      p0CausalExitPartialSum retained h states coefficient L f i +
        p0CausalExitIterate retained h states coefficient f L i := by
  rw [p0CausalExitApply_partialSum]
  change f i + (∑ k ∈ Finset.range L,
      p0CausalExitIterate retained h states coefficient f (k + 1) i) =
    (∑ k ∈ Finset.range L, p0CausalExitIterate retained h states coefficient f k i) +
      p0CausalExitIterate retained h states coefficient f L i
  calc
    _ = (∑ k ∈ Finset.range L,
        p0CausalExitIterate retained h states coefficient f (k + 1) i) +
          p0CausalExitIterate retained h states coefficient f 0 i := add_comm _ _
    _ = ∑ k ∈ Finset.range (L + 1),
        p0CausalExitIterate retained h states coefficient f k i :=
      (Finset.sum_range_succ' _ L).symm
    _ = _ := Finset.sum_range_succ _ L

/-- A structural upper bound on the remaining lengths gives a finite
exact solution of the causal equation `u=f+T u`. -/
theorem p0CausalExitPartialSum_solution {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) (f : Fin n → ℝ) :
    ∀ i, p0CausalExitPartialSum retained h states coefficient L f i =
      f i + p0CausalExitApply retained h states coefficient
        (p0CausalExitPartialSum retained h states coefficient L f) i := by
  intro i
  have ht := p0CausalExitPartialSum_telescoping retained h states coefficient L f i
  have hz := p0CausalExitIterate_zero_of_remaining_lt retained h states coefficient f L i (hL i)
  rw [hz, add_zero] at ht
  exact ht.symm

/-- The same finite triangular support proves uniqueness, including for
signed matrices without any norm bound. -/
theorem p0CausalExit_solution_unique {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L)
    (f u v : Fin n → ℝ)
    (hu : ∀ i, u i = f i + p0CausalExitApply retained h states coefficient u i)
    (hv : ∀ i, v i = f i + p0CausalExitApply retained h states coefficient v i) : u = v := by
  let d : Fin n → ℝ := fun i => u i - v i
  have hd (i : Fin n) :
      d i = ∑ j, p0CausalExitKernel retained h states coefficient i j * d j := by
    dsimp only [d]
    simp only [mul_sub, Finset.sum_sub_distrib]
    have hui := hu i
    have hvi := hv i
    dsimp only [p0CausalExitApply] at hui hvi
    linarith only [hui, hvi]
  have hiter (k : ℕ) : ∀ i,
      d i = p0CausalExitIterate retained h states coefficient d k i := by
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
        intro i
        calc
          d i = ∑ j, p0CausalExitKernel retained h states coefficient i j * d j := hd i
          _ = ∑ j, p0CausalExitKernel retained h states coefficient i j *
              p0CausalExitIterate retained h states coefficient d k j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [ih j]
          _ = _ := rfl
  funext i
  have heq := hiter L i
  rw [p0CausalExitIterate_zero_of_remaining_lt retained h states coefficient d L i (hL i)] at heq
  exact sub_eq_zero.mp heq

/-- Finite same-policy causal elimination has a unique solution. All
inputs are finite matrix data and the actual remaining-length bound. -/
theorem p0CausalExit_existsUnique_solution {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (states : Fin n → FirstExitDepthState α) (coefficient : Fin n → Fin n → ℝ)
    (L : ℕ) (hL : ∀ i, (states i).remaining.length < L) (f : Fin n → ℝ) :
    ∃! u : Fin n → ℝ, ∀ i,
      u i = f i + p0CausalExitApply retained h states coefficient u i := by
  refine ⟨p0CausalExitPartialSum retained h states coefficient L f,
    p0CausalExitPartialSum_solution retained h states coefficient L hL f, ?_⟩
  intro u hu
  exact p0CausalExit_solution_unique retained h states coefficient L hL f u _ hu
    (p0CausalExitPartialSum_solution retained h states coefficient L hL f)

/-- The uniform truncation length is supplied by the original recursion
for a finite family of literal root exits; it is not an additional input. -/
theorem p0CausalExit_root_existsUnique_solution {α : Type*} {n : ℕ}
    (retained : Bool → List α → Bool) (h : α → ℝ) (carrier : List α)
    (states : Fin n → FirstExitDepthState α)
    (hstates : ∀ i, states i ∈ p1SignedExitStates retained h [] true 1 carrier)
    (coefficient : Fin n → Fin n → ℝ) (f : Fin n → ℝ) :
    ∃! u : Fin n → ℝ, ∀ i,
      u i = f i + p0CausalExitApply retained h states coefficient u i := by
  apply p0CausalExit_existsUnique_solution retained h states coefficient carrier.length
  intro i
  have hr := p1_mem_exitStates_rank_bound retained h [] carrier true 1 (states i) (hstates i)
  simp only [List.length_nil, Nat.zero_add] at hr
  omega

end

end ImbalancedChen
