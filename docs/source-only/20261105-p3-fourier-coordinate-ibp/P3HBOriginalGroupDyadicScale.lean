import ImbalancedChen.P3HBSmoothLogTensorRestoration
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-!
P3.6 manuscript-internal actual ORIGINAL GROUP dyadic factor:
  psi(c * exp(sum_{i in J} z_i)), psi(t)=chi(t)-chi(2*t), c>0.
Pinned manuscript UyNewNas/chen-imbalanced-semiprimes
@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion 20261010 §2 (exact smooth dyadic partition)
and §4 (F), the literal psi(c_i exp(sum_group z_j)).
Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

A POSITIVE physical group scale c changes the log argument only by
log c. The actual iterated derivative of the one-dimensional grouped
profile is therefore a TRANSLATE of the canonical original psi(e^s).
This yields an order-K derivative bound independent of c and exact
translated support, not a postulated uniform geometry class.

No derivative in the full Fin 6 coordinate chart is asserted here;
one still must transfer this scalar derivative via the actual group
sum, compose all original W_T/U5/trim factors, and retain the common
T,m(N) bounds. SOURCE_ONLY, UNCOMPILED, KERNEL UNVERIFIED.
-/

namespace ImbalancedChen.P3HBOriginalGroupDyadicScale
noncomputable section
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo
open ImbalancedChen.P3HBSmoothLogFiniteDerivatives
open ImbalancedChen.P3HBLogDerivativeGlobalSupport
open ImbalancedChen.P3HBSmoothLogTensorRestoration

/-- The EXACT original manuscript's psi(c exp(s)), at positive scale c. -/
def groupDyadicLogProfile (chi : ℝ → ℂ) (c s : ℝ) : ℂ :=
  chi (c * Real.exp s) - chi (2 * (c * Real.exp s))

/-- psi(exp(s)), the literal original dyadic factor in normalized log scale. -/
def baseDyadicLogProfile (chi : ℝ → ℂ) (s : ℝ) : ℂ :=
  chi (Real.exp s) - chi (2 * Real.exp s)

/-- Positive physical scales are genuine translations in the log chart.
No scale-dependent derivative constant or group indicator is introduced. -/
theorem groupDyadicLogProfile_eq_translate
    (chi : ℝ → ℂ) (c : ℝ) (hc : 0 < c) (s : ℝ) :
    groupDyadicLogProfile chi c s =
      baseDyadicLogProfile chi (s + Real.log c) := by
  unfold groupDyadicLogProfile baseDyadicLogProfile
  rw [Real.exp_add, Real.exp_log hc]
  ring

/-- Exact arbitrary-order derivative identity, with the REAL physical
c>0 retained; Mathlib translation invariance pays all derivative orders. -/
theorem groupDyadicLogProfile_iteratedDeriv_translate
    (chi : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (k : ℕ) (s : ℝ) :
    iteratedDeriv k (groupDyadicLogProfile chi c) s =
      iteratedDeriv k (baseDyadicLogProfile chi) (s + Real.log c) := by
  have hfun :
      groupDyadicLogProfile chi c =
        (fun t : ℝ => baseDyadicLogProfile chi (t + Real.log c)) := by
    funext t
    exact groupDyadicLogProfile_eq_translate chi c hc t
  rw [hfun]
  exact congrFun
    (iteratedDeriv_comp_add_const k (baseDyadicLogProfile chi) (Real.log c)) s

/-- The canonical group factor is precisely the original sum of the
three actual smooth children, differentiated at the requested order. -/
theorem baseDyadicLogProfile_iteratedDeriv_children
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (k : ℕ) (s : ℝ) :
    iteratedDeriv k (baseDyadicLogProfile chi) s =
      ∑ a : Fin 3, iteratedDeriv k (logChild chi a) s := by
  simpa only [baseDyadicLogProfile] using
    (logChild_iteratedDeriv_sum chi hchi k s).symm

/-- Real original group factor after the ORIGINAL group log-chart sum.
The group is positional: no HB occurrence, label or multiplicity is merged. -/
def originalGroupDyadicFactor
    (chi : ℝ → ℂ) (c : ℝ) (J : Finset (Fin 6))
    (u : Fin 6 → ℝ) : ℂ :=
  groupDyadicLogProfile chi c (∑ i ∈ J, u i)

/-- The full grouped factor is an exact translation in its sum of
original positional log variables. This is NOT yet a 6D derivative claim. -/
theorem originalGroupDyadicFactor_eq_translate
    (chi : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (J : Finset (Fin 6)) (u : Fin 6 → ℝ) :
    originalGroupDyadicFactor chi c J u =
      baseDyadicLogProfile chi ((∑ i ∈ J, u i) + Real.log c) :=
  groupDyadicLogProfile_eq_translate chi c hc _

/-- All finite scalar log-Euler derivative orders of the ACTUAL smooth
group psi(c exp(s)) have a SINGLE bound INDEPENDENT of the physical c>0.
The factor 3 pays the original three overlapping positional children.
This does not bound the full W_T product or all repeated 2S derivatives. -/
theorem groupDyadicLogProfile_uniform_scale_derivatives
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (c : ℝ), 0 < c →
        ∀ (k : ℕ), k ≤ K → ∀ (s : ℝ),
        ‖iteratedDeriv k (groupDyadicLogProfile chi c) s‖ ≤ 3 * C := by
  obtain ⟨C, hC, hbound⟩ :=
    logChild_uniform_global_finite_order chi hchi hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro c hc k hk s
  rw [groupDyadicLogProfile_iteratedDeriv_translate chi c hc]
  rw [baseDyadicLogProfile_iteratedDeriv_children chi hchi]
  calc
    ‖∑ a : Fin 3, iteratedDeriv k (logChild chi a) (s + Real.log c)‖
      ≤ ∑ a : Fin 3, ‖iteratedDeriv k (logChild chi a) (s + Real.log c)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : Fin 3, C := by
      apply Finset.sum_le_sum
      intro a _
      exact hbound k a (s + Real.log c) hk
    _ = 3 * C := by simp [Fin.sum_univ_succ]; ring

/-- Exact translated zero-support of EVERY scalar log derivative.
Outside the SHIFTED original [-log 2,log 2] interval all three actual
children vanish. No smoothing-stage limit or Fourier tail is assumed. -/
theorem groupDyadicLogProfile_derivative_zero_outside
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (c : ℝ) (hc : 0 < c) (k : ℕ) (s : ℝ)
    (hout : s + Real.log c ∈
      Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    iteratedDeriv k (groupDyadicLogProfile chi c) s = 0 := by
  rw [groupDyadicLogProfile_iteratedDeriv_translate chi c hc]
  rw [baseDyadicLogProfile_iteratedDeriv_children chi hchi]
  apply Finset.sum_eq_zero
  intro a _
  exact logChild_iteratedDeriv_zero_outside chi a k
    hsmall hlarge (s + Real.log c) hout

end
end ImbalancedChen.P3HBOriginalGroupDyadicScale
