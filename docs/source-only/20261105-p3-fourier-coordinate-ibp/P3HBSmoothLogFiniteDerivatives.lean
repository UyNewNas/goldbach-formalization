import ImbalancedChen.P3HBSmoothLogScaleBudget
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Group.Bounded

/-!
P3.6 — finite-order quantitative bounds for the actual three-way HB
logarithmic coordinate templates, independent of every dyadic label.
SOURCE_ONLY; not Lean/Lake compiled or kernel checked.
Pinned manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 and §4 (F).
Pinned Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

For each finite K and the fixed genuine smooth cutoff chi, compactness of
[-log 2, log 2] bounds the FIRST K derivatives of all three genuine
logChild functions by a common C_K. By the exact earlier scale chart
identity, C_K also bounds all dyadic-labelled children in THEIR NORMALIZED
logarithmic coordinates, with no growth in j. The six-slot product of
individual derivative absolute values has cost C_K^6. No derivative of
an original coupled W_T is identified with this product here.

This is a real quantitative existence theorem for the chosen cutoff, not
a Fourier-L1, full W_T, distributional PP or target-equivalent assumption.
-/

namespace ImbalancedChen.P3HBSmoothLogFiniteDerivatives
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo

private theorem fixed_template_order_bound
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi) (k : ℕ) :
    ∃ C : ℝ, ∀ (a : Fin 3) (u : ℝ),
      u ∈ Set.Icc (-Real.log 2) (Real.log 2) →
      ‖iteratedDeriv k (logChild chi a) u‖ ≤ C := by
  have hcontinuous (a : Fin 3) :
      Continuous (iteratedDeriv k (logChild chi a)) :=
    (logChild_contDiff chi hchi a).continuous_iteratedDeriv k le_top
  have hcompact : IsCompact (Set.Icc (-Real.log 2) (Real.log 2)) :=
    isCompact_Icc
  obtain ⟨B0, hB0⟩ :=
    hcompact.exists_bound_of_continuousOn (hcontinuous 0).continuousOn
  obtain ⟨B1, hB1⟩ :=
    hcompact.exists_bound_of_continuousOn (hcontinuous 1).continuousOn
  obtain ⟨B2, hB2⟩ :=
    hcompact.exists_bound_of_continuousOn (hcontinuous 2).continuousOn
  refine ⟨max B0 (max B1 B2), ?_⟩
  intro a u hu
  fin_cases a
  · exact (hB0 u hu).trans (le_max_left _ _)
  · exact (hB1 u hu).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (hB2 u hu).trans ((le_max_right _ _).trans (le_max_right _ _))

/-- One nonnegative constant simultaneously bounds all three actual
log-templates through every derivative order k ≤ K on their original
compact logarithmic support window. It depends only on the fixed chi,K,
not on the dyadic label, target T, HB length or physical modulus. -/
theorem logChild_uniform_finite_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
        k ≤ K → u ∈ Set.Icc (-Real.log 2) (Real.log 2) →
        ‖iteratedDeriv k (logChild chi a) u‖ ≤ C := by
  have hbase (n : ℕ) :
      ∃ C : ℝ, ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
        k ≤ n → u ∈ Set.Icc (-Real.log 2) (Real.log 2) →
        ‖iteratedDeriv k (logChild chi a) u‖ ≤ C := by
    induction n with
    | zero =>
        obtain ⟨C, hC⟩ := fixed_template_order_bound chi hchi 0
        refine ⟨C, ?_⟩
        intro k a u hk hu
        have hk0 : k = 0 := by omega
        subst k
        exact hC a u hu
    | succ n ih =>
        obtain ⟨C, hC⟩ := ih
        obtain ⟨D, hD⟩ := fixed_template_order_bound chi hchi (n + 1)
        refine ⟨max C D, ?_⟩
        intro k a u hk hu
        by_cases hkn : k ≤ n
        · exact (hC k a u hkn hu).trans (le_max_left _ _)
        · have hkeq : k = n + 1 := by omega
          subst k
          exact (hD a u hu).trans (le_max_right _ _)
  obtain ⟨B, hB⟩ := hbase K
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro k a u hk hu
  exact (hB k a u hk hu).trans (le_max_right _ _)

/-- Equality of genuine k-th derivatives for every dyadic label,
not merely their first derivatives: the two functions are identical
before differentiation, by the earlier exact logarithmic chart lemma. -/
theorem smoothCoord_log_iteratedDeriv_exact
    (chi : ℝ → ℂ) (j k : ℕ) (a : Fin 3) (u : ℝ) :
    iteratedDeriv k
      (fun v : ℝ => smoothCoord chi ((2 : ℝ) ^ j * Real.exp v) j a) u =
        iteratedDeriv k (logChild chi a) u := by
  have hfun :
      (fun v : ℝ => smoothCoord chi ((2 : ℝ) ^ j * Real.exp v) j a) =
        logChild chi a := by
    funext v
    exact smoothCoord_log_exact chi j a v
  rw [hfun]

/-- A common, genuinely derived finite-order constant applies to the
entire original dyadic-label family in normalized logarithmic charts.
This does not assert a uniform physical W_T mixed derivative bound. -/
theorem smoothCoord_log_uniform_finite_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j k : ℕ) (a : Fin 3) (u : ℝ),
        k ≤ K → u ∈ Set.Icc (-Real.log 2) (Real.log 2) →
        ‖iteratedDeriv k
          (fun v : ℝ => smoothCoord chi ((2 : ℝ) ^ j * Real.exp v) j a) u‖ ≤ C := by
  obtain ⟨C, hC, hB⟩ := logChild_uniform_finite_order chi hchi K
  refine ⟨C, hC, ?_⟩
  intro j k a u hk hu
  rw [smoothCoord_log_iteratedDeriv_exact]
  exact hB k a u hk hu

/-- Explicit six-slot fixed-template product envelope: the bound is
C_K^6, with no dyadic-label factor, when each literal positional
coordinate has order at most K and lies in the compact log window.
This bounds the product of one-variable derivative norms only; the
six-dimensional mixed-derivative identity remains to be supplied. -/
theorem six_slot_log_template_product_budget
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (orders : Fin 6 → ℕ) (children : Fin 6 → Fin 3)
        (u : Fin 6 → ℝ),
        (∀ i, orders i ≤ K) →
        (∀ i, u i ∈ Set.Icc (-Real.log 2) (Real.log 2)) →
        (∏ i : Fin 6,
          ‖iteratedDeriv (orders i) (logChild chi (children i)) (u i)‖)
          ≤ C ^ 6 := by
  obtain ⟨C, hC, hB⟩ := logChild_uniform_finite_order chi hchi K
  refine ⟨C, hC, ?_⟩
  intro orders children u horders hu
  calc
    (∏ i : Fin 6,
        ‖iteratedDeriv (orders i) (logChild chi (children i)) (u i)‖)
      ≤ ∏ _i : Fin 6, C := by
        apply Finset.prod_le_prod
        · intro i hi
          exact norm_nonneg _
        · intro i hi
          exact hB (orders i) (children i) (u i) (horders i) (hu i)
    _ = C ^ 6 := by simp

end ImbalancedChen.P3HBSmoothLogFiniteDerivatives
