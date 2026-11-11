import ImbalancedChen.P3HBSmoothLogFiniteDerivatives
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
P3.6 — compact support of EVERY finite derivative of the actual smooth
three-way HB log template, and a genuinely global fixed-order envelope.

SOURCE_ONLY / UNCOMPILED / KERNEL_UNVERIFIED.
Frozen manuscript: chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 (original smooth psi) and §4 (F).
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

The previous finite-order bound only controlled u in [-log 2, log 2].
The original plateau chi=1 below 1 and chi=0 above 2 makes every
logChild identically zero on the TWO OPEN EXTERIOR intervals.
Locality of iterated derivatives (the pinned Mathlib theorem
iteratedDerivWithin_congr) gives zero for ALL orders on those intervals.
Thus the original compact window controls the WHOLE real line, with no
extra assumptions on rho, physical modulus, T or growing m(N).

This does not pay integrated original W_T mixed derivatives, 6D derivative
identities, Fourier L1/H, arithmetic discrepancy or all PP sources.
-/

namespace ImbalancedChen.P3HBLogDerivativeGlobalSupport
noncomputable section
open scoped Classical
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBSmoothLogFiniteDerivatives

private theorem logChild_eq_zero_on_exterior
    (chi : ℝ → ℂ) (a : Fin 3)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    Set.EqOn (logChild chi a) (fun _ : ℝ => (0 : ℂ))
      (Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) := by
  intro u hu
  rcases Set.mem_union.mp hu with hl | hr
  · change u < -Real.log 2 at hl
    have he : Real.exp u < Real.exp (-Real.log 2) :=
      Real.exp_strictMono hl
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    have hsmall' : 2 * Real.exp u ≤ 1 := by
      norm_num at he
      linarith
    exact logChild_zero_small chi a u hsmall hsmall'
  · change Real.log 2 < u at hr
    have he : Real.exp (Real.log 2) < Real.exp u :=
      Real.exp_strictMono hr
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    exact logChild_zero_large chi a u hlarge (le_of_lt he)

/-- The genuine original smooth HB log child has zero k-th derivative on
both open exterior intervals, for every k, including k=0. This uses
local agreement with zero, NOT an assumption about derivative support. -/
theorem logChild_iteratedDeriv_zero_outside
    (chi : ℝ → ℂ) (a : Fin 3) (k : ℕ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (u : ℝ)
    (hu : u ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)) :
    iteratedDeriv k (logChild chi a) u = 0 := by
  let s : Set ℝ := Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2)
  have hopen : IsOpen s := isOpen_Iio.union isOpen_Ioi
  have hzero : Set.EqOn (logChild chi a) (fun _ : ℝ => (0 : ℂ)) s :=
    logChild_eq_zero_on_exterior chi a hsmall hlarge
  have hwithin :
      iteratedDerivWithin k (logChild chi a) s u =
        iteratedDerivWithin k (fun _ : ℝ => (0 : ℂ)) s u :=
    (iteratedDerivWithin_congr (n := k) hzero) u hu
  have hleft :
      iteratedDerivWithin k (logChild chi a) s u =
        iteratedDeriv k (logChild chi a) u :=
    (iteratedDerivWithin_of_isOpen (n := k) hopen) hu
  have hright :
      iteratedDerivWithin k (fun _ : ℝ => (0 : ℂ)) s u =
        iteratedDeriv k (fun _ : ℝ => (0 : ℂ)) u :=
    (iteratedDerivWithin_of_isOpen (n := k) hopen) hu
  calc
    iteratedDeriv k (logChild chi a) u =
        iteratedDerivWithin k (logChild chi a) s u := hleft.symm
    _ = iteratedDerivWithin k (fun _ : ℝ => (0 : ℂ)) s u := hwithin
    _ = iteratedDeriv k (fun _ : ℝ => (0 : ℂ)) u := hright
    _ = 0 := by simp

private theorem outside_of_not_mem_log_window
    (u : ℝ)
    (hu : u ∉ Set.Icc (-Real.log 2) (Real.log 2)) :
    u ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2) := by
  have hor : u < -Real.log 2 ∨ Real.log 2 < u := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hu
  exact Set.mem_union.mpr hor

/-- Every finite-order derivative is supported in the SAME closed log
window, not merely the original undifferentiated cutoff. -/
theorem logChild_iteratedDeriv_support_subset
    (chi : ℝ → ℂ) (a : Fin 3) (k : ℕ)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) :
    Function.support (iteratedDeriv k (logChild chi a)) ⊆
      Set.Icc (-Real.log 2) (Real.log 2) := by
  intro u hu
  by_contra hn
  change iteratedDeriv k (logChild chi a) u ≠ 0 at hu
  exact hu (logChild_iteratedDeriv_zero_outside chi a k hsmall hlarge u
    (outside_of_not_mem_log_window u hn))

/-- The previous C_K compact-window bound is now global on ALL real
log coordinates, with the same C_K for all 3 children and all k ≤ K.
The plateau hypotheses are about the actual selected smooth cutoff. -/
theorem logChild_uniform_global_finite_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
        k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C := by
  obtain ⟨C, hC, hinside⟩ := logChild_uniform_finite_order chi hchi K
  refine ⟨C, hC, ?_⟩
  intro k a u hk
  by_cases hu : u ∈ Set.Icc (-Real.log 2) (Real.log 2)
  · exact hinside k a u hk hu
  · have hz : iteratedDeriv k (logChild chi a) u = 0 :=
      logChild_iteratedDeriv_zero_outside chi a k hsmall hlarge u
        (outside_of_not_mem_log_window u hu)
    simpa [hz] using hC

/-- The same WHOLE-REAL-LINE envelope applies to every actual dyadic
scale in the normalized coordinate. No j-dependent derivative constant
is introduced. This is not yet the 6D mixed derivative formula. -/
theorem smoothCoord_log_uniform_global_finite_order
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j k : ℕ) (a : Fin 3) (u : ℝ),
        k ≤ K →
        ‖iteratedDeriv k
          (fun v : ℝ => smoothCoord chi ((2 : ℝ) ^ j * Real.exp v) j a) u‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    logChild_uniform_global_finite_order chi hchi hsmall hlarge K
  refine ⟨C, hC, ?_⟩
  intro j k a u hk
  rw [smoothCoord_log_iteratedDeriv_exact]
  exact hbound k a u hk

end ImbalancedChen.P3HBLogDerivativeGlobalSupport
