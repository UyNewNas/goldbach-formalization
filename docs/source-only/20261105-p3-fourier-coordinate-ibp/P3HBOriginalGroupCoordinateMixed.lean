import ImbalancedChen.P3HBOriginalGroupDyadicScale
import ImbalancedChen.P3HBCanonicalGeometryDerivative
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
P3.6 manuscript-internal: actual ordered-coordinate mixed derivatives of the
LITERAL original grouped factor psi(c * exp(sum_{j in J} z_j)).
Pinned frozen manuscript 9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §4 (F) lines 153-163; Mathlib
 e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, Lean v4.33.0-rc1.

This pays, for ONE genuine group factor, the exact incidence condition for
an arbitrary ordered list of original positional derivatives, including
repeated axes. Every axis outside the group annihilates the derivative;
otherwise the derivative is the actual scalar iteratedDeriv of the same
positive-scale dyadic profile. The resulting finite-order norm bound is
uniform in c>0 and the six-position group J.

It does NOT establish the product Leibniz rule for all W_T / U5 / trim,
any growing-m(N) uniform whole-weight L1 budget, Fourier tail, arithmetic
PP discrepancy, or the same integer rho assembly.
SOURCE_ONLY / NOT COMPILED / KERNEL NOT VERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupCoordinateMixed
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBOriginalGroupDyadicScale
open ImbalancedChen.P3HBCanonicalGeometryDerivative

/-- Literal sum of original positional logarithmic coordinates in a group. -/
def originalGroupSum (J : Finset (Fin 6)) (u : Fin 6 → ℝ) : ℝ :=
  ∑ j ∈ J, u j

/-- Changing a member of the actual group replaces exactly one summand. -/
theorem originalGroupSum_update_mem (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) (hi : i ∈ J) (t : ℝ) :
    originalGroupSum J (Function.update u i t) =
      t + ∑ j ∈ J.erase i, u j := by
  classical
  calc
    originalGroupSum J (Function.update u i t) =
        (∑ j ∈ J.erase i, Function.update u i t j) +
          Function.update u i t i := by
            unfold originalGroupSum
            exact (Finset.sum_erase_add J
              (fun j : Fin 6 => Function.update u i t j) hi).symm
    _ = (∑ j ∈ J.erase i, u j) + t := by
      simp only [Function.update_same]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      simp [Function.update_noteq (Finset.ne_of_mem_erase hj)]
    _ = t + ∑ j ∈ J.erase i, u j := add_comm _ _

/-- A coordinate absent from J has no influence on its literal group sum. -/
theorem originalGroupSum_update_not_mem (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) (hi : i ∉ J) (t : ℝ) :
    originalGroupSum J (Function.update u i t) = originalGroupSum J u := by
  classical
  unfold originalGroupSum
  apply Finset.sum_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  simp [Function.update_noteq hji]

/-- Basepoint form of the exact original group sum, retaining the slot i. -/
theorem originalGroupSum_eq_self_add (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) (i : Fin 6) (hi : i ∈ J) :
    originalGroupSum J u = u i + ∑ j ∈ J.erase i, u j := by
  classical
  calc
    originalGroupSum J u = (∑ j ∈ J.erase i, u j) + u i := by
      unfold originalGroupSum
      exact (Finset.sum_erase_add J u hi).symm
    _ = u i + ∑ j ∈ J.erase i, u j := add_comm _ _

/-- The canonical actual (not postulated) coordinate derivative of a
scalar function composed with the ORIGINAL group sum. -/
theorem actualAxisDeriv_comp_groupSum (f : ℝ → ℂ)
    (J : Finset (Fin 6)) (u : Fin 6 → ℝ) (i : Fin 6) :
    actualAxisDeriv (fun v => f (originalGroupSum J v)) i u =
      if i ∈ J then deriv f (originalGroupSum J u) else 0 := by
  classical
  by_cases hi : i ∈ J
  · have hs :
        (fun t : ℝ => f (originalGroupSum J (Function.update u i t))) =
          (fun t : ℝ => f (t + ∑ j ∈ J.erase i, u j)) := by
      funext t
      rw [originalGroupSum_update_mem J u i hi t]
    unfold actualAxisDeriv
    rw [hs, deriv_comp_add_const]
    rw [originalGroupSum_eq_self_add J u i hi]
    simp [hi]
  · have hs :
        (fun t : ℝ => f (originalGroupSum J (Function.update u i t))) =
          (fun _ : ℝ => f (originalGroupSum J u)) := by
      funext t
      rw [originalGroupSum_update_not_mem J u i hi t]
    unfold actualAxisDeriv
    rw [hs]
    simp [hi]

/-- Repeated, ordered REAL coordinate derivatives: a repeated slot is
still differentiated repeatedly, rather than replaced by a set member. -/
def originalOrderedAxisDeriv :
    List (Fin 6) → ((Fin 6 → ℝ) → ℂ) → ((Fin 6 → ℝ) → ℂ)
  | [], W => W
  | i :: rest, W => actualAxisDeriv (originalOrderedAxisDeriv rest W) i

/-- Exact positional incidence for ordered derivatives, including repeats. -/
def axesWithinGroup (J : Finset (Fin 6)) : List (Fin 6) → Prop
  | [] => True
  | i :: rest => i ∈ J ∧ axesWithinGroup J rest

/-- The literal 6D original grouped factor is exactly the scalar profile
composed with the true (not surrogate) group sum. -/
theorem originalGroupDyadicFactor_eq_groupSum
    (chi : ℝ → ℂ) (c : ℝ) (J : Finset (Fin 6)) :
    originalGroupDyadicFactor chi c J =
      (fun u => groupDyadicLogProfile chi c (originalGroupSum J u)) := by
  rfl

/-- All ordered repeated coordinate partials of ONE true group are
identified; no differentiability assumption is manufactured and no
mixed partials are commuted. If even one selected slot is outside J,
the derivative is exactly zero. -/
theorem originalGroupOrderedDeriv_exact (chi : ℝ → ℂ) (c : ℝ)
    (J : Finset (Fin 6)) (axes : List (Fin 6)) :
    ∀ u : Fin 6 → ℝ,
      originalOrderedAxisDeriv axes (originalGroupDyadicFactor chi c J) u =
        if axesWithinGroup J axes then
          iteratedDeriv axes.length (groupDyadicLogProfile chi c)
            (originalGroupSum J u)
        else 0 := by
  induction axes with
  | nil =>
      intro u
      simp [originalOrderedAxisDeriv, axesWithinGroup,
        originalGroupDyadicFactor_eq_groupSum, iteratedDeriv_zero]
  | cons i rest ih =>
      intro u
      change actualAxisDeriv
        (originalOrderedAxisDeriv rest (originalGroupDyadicFactor chi c J)) i u = _
      by_cases hr : axesWithinGroup J rest
      · have hrest :
            originalOrderedAxisDeriv rest (originalGroupDyadicFactor chi c J) =
              (fun v => iteratedDeriv rest.length (groupDyadicLogProfile chi c)
                (originalGroupSum J v)) := by
          funext v
          simpa only [if_pos hr] using ih v
        rw [hrest, actualAxisDeriv_comp_groupSum]
        by_cases hi : i ∈ J
        · simp [axesWithinGroup, hi, hr, List.length_cons, iteratedDeriv_succ]
        · simp [axesWithinGroup, hi]
      · have hrest :
            originalOrderedAxisDeriv rest (originalGroupDyadicFactor chi c J) =
              (fun _ => (0 : ℂ)) := by
          funext v
          simpa only [if_neg hr] using ih v
        rw [hrest]
        simp [actualAxisDeriv, axesWithinGroup, hr]

/-- Uniform finite-order quantitative bound for actual ORDERED six-slot
mixed coordinate derivatives of a SINGLE original positive-scale group.
The same C works for all positive c, every group J and all repeated lists
of length at most K. This is not a whole-weight W_T bound. -/
theorem originalGroupOrderedDeriv_uniform_scale
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ c : ℝ, 0 < c → ∀ J : Finset (Fin 6),
        ∀ axes : List (Fin 6), axes.length ≤ K →
          ∀ u : Fin 6 → ℝ,
            ‖originalOrderedAxisDeriv axes
              (originalGroupDyadicFactor chi c J) u‖ ≤ 3 * C := by
  obtain ⟨C, hC, hbound⟩ :=
    groupDyadicLogProfile_uniform_scale_derivatives chi hchi hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro c hc J axes haxes u
  rw [originalGroupOrderedDeriv_exact chi c J axes u]
  by_cases hall : axesWithinGroup J axes
  · simp only [if_pos hall]
    exact hbound c hc axes.length haxes (originalGroupSum J u)
  · simp only [if_neg hall, norm_zero]
    positivity

/-- Genuine support vanishing for every ordered mixed derivative of a
single group, with exactly the same shifted argument s + log(c).
In particular it never assumes a false unshifted support rectangle. -/
theorem originalGroupOrderedDeriv_zero_outside
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : ℝ) (hc : 0 < c) (J : Finset (Fin 6))
    (axes : List (Fin 6)) (u : Fin 6 → ℝ)
    (hout : originalGroupSum J u + Real.log c ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    originalOrderedAxisDeriv axes (originalGroupDyadicFactor chi c J) u = 0 := by
  rw [originalGroupOrderedDeriv_exact chi c J axes u]
  by_cases hall : axesWithinGroup J axes
  · simp only [if_pos hall]
    exact groupDyadicLogProfile_derivative_zero_outside chi hchi hsmall
      hlarge c hc axes.length (originalGroupSum J u) hout
  · simp [hall]

end
end ImbalancedChen.P3HBOriginalGroupCoordinateMixed
