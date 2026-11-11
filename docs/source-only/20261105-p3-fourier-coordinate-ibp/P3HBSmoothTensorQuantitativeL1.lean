import ImbalancedChen.P3HBSmoothTensorL1
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
P3.6 — quantitative L1 budget for the actual three-way smooth HB log children.
SOURCE_ONLY / NOT COMPILED / KERNEL_UNVERIFIED.
Frozen manuscript @9731290e8f53cffda44129906cde6a965eaa869b,
prime-product completion §2 / §4 (F).
Pinned Lean v4.33.0-rc1, Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

For a fixed genuine C-infinity cutoff chi and derivative order ceiling K, the
previously derived C_K bounds all derivatives globally and all three children.
Their common compact log support has Lebesgue length 2 log 2. Here we pay
that ACTUAL real measure once per original ordered slot; six factors cost
(2 log 2 C_K)^6, and every original labelled 3^6 child costs
(smoothChildren.card) * (2 log 2 C_K)^6.

This is a bound for separated six-slot HB derivatives only. It is NOT the
coupled physical W_T mixed-Frechet derivative, Fourier H-tail or arithmetic PP.
-/
namespace ImbalancedChen.P3HBSmoothTensorQuantitativeL1
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
open ImbalancedChen.P3HBSmoothLogScaleBudget
open ImbalancedChen.P3HBLogDerivativeGlobalSupport
open ImbalancedChen.P3HBSmoothLogTensorRestoration
open ImbalancedChen.P3HBSmoothTensorL1
open ImbalancedChen.P3HBSmoothThreeWayRatioTwo

private theorem exterior_of_not_in_log_window (u : ℝ)
    (hu : u ∉ Set.Icc (-Real.log 2) (Real.log 2)) :
    u ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2) := by
  have hor : u < -Real.log 2 ∨ Real.log 2 < u := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hu
  exact Set.mem_union.mpr hor

/-- Explicit Lebesgue L1 cost for one actual smooth HB child derivative,
using the SAME global C_K already derived from chi and K. -/
theorem logChild_derivative_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C)
    (k : ℕ) (a : Fin 3) (hk : k ≤ K) :
    (∫ u : ℝ, ‖iteratedDeriv k (logChild chi a) u‖) ≤
      (2 * Real.log 2) * C := by
  let s : Set ℝ := Set.Icc (-Real.log 2) (Real.log 2)
  have hs : MeasurableSet s := measurableSet_Icc
  have hfinite : (volume : Measure ℝ) s ≠ ∞ :=
    isCompact_Icc.measure_ne_top
  have htarget : Integrable (fun u : ℝ =>
      ‖iteratedDeriv k (logChild chi a) u‖) :=
    (logChild_derivative_integrable chi hchi hsmall hlarge a k).norm
  have hmajor : Integrable (s.indicator (fun _ : ℝ => C)) :=
    (integrableOn_const hfinite).integrable_indicator hs
  have hpoint (u : ℝ) :
      ‖iteratedDeriv k (logChild chi a) u‖ ≤
        s.indicator (fun _ : ℝ => C) u := by
    by_cases hu : u ∈ s
    · simpa only [Set.indicator_of_mem hu] using hC k a u hk
    · have hout : u ∈ Set.Iio (-Real.log 2) ∪ Set.Ioi (Real.log 2) :=
        exterior_of_not_in_log_window u hu
      have hz : iteratedDeriv k (logChild chi a) u = 0 :=
        logChild_iteratedDeriv_zero_outside chi a k hsmall hlarge u hout
      simp [Set.indicator_of_notMem hu, hz]
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  calc
    (∫ u : ℝ, ‖iteratedDeriv k (logChild chi a) u‖) ≤
        ∫ u : ℝ, s.indicator (fun _ : ℝ => C) u :=
          integral_mono htarget hmajor hpoint
    _ = (volume : Measure ℝ).real s * C := by
      rw [integral_indicator_const C hs]
      rw [smul_eq_mul]
    _ = (2 * Real.log 2) * C := by
      dsimp [s]
      rw [Real.volume_real_Icc]
      have hmax : max (Real.log 2 - -Real.log 2) 0 = 2 * Real.log 2 := by
        rw [max_eq_left]
        · ring
        · linarith
      rw [hmax]

/-- Quantitative bound for each of the original SIX ordered positional
smooth HB derivative tensors. This keeps every original child label. -/
theorem logTensorMixed_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C)
    (orders : Fin 6 → ℕ) (child : Fin 6 → Fin 3)
    (horders : ∀ i : Fin 6, orders i ≤ K) :
    (∫ u : Fin 6 → ℝ, ‖logTensorMixed chi orders child u‖) ≤
      ((2 * Real.log 2) * C) ^ 6 := by
  rw [logTensorMixed_norm_integral_eq_prod chi orders child]
  calc
    (∏ i : Fin 6, ∫ t : ℝ,
      ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) ≤
        ∏ _i : Fin 6, ((2 * Real.log 2) * C) := by
          apply Finset.prod_le_prod
          · intro i _
            exact integral_nonneg (fun _ => norm_nonneg _)
          · intro i _
            exact logChild_derivative_L1_le chi hchi hsmall hlarge
              K C hC (orders i) (child i) (horders i)
    _ = ((2 * Real.log 2) * C) ^ 6 := by simp

/-- Fixed-order logarithmic L1 envelope for ALL original 3^6 positional
children. No claim that the coupled W_T derivative is separated. -/
theorem all_logTensorMixed_children_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C)
    (orders : Fin 6 → ℕ) (horders : ∀ i : Fin 6, orders i ≤ K) :
    (∫ u : Fin 6 → ℝ,
      ∑ child ∈ smoothChildren, ‖logTensorMixed chi orders child u‖) ≤
      (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6 := by
  rw [all_logTensorMixed_children_norm_integral_eq chi hchi hsmall hlarge orders]
  calc
    (∑ child ∈ smoothChildren,
      ∏ i : Fin 6, ∫ t : ℝ,
        ‖iteratedDeriv (orders i) (logChild chi (child i)) t‖) ≤
        ∑ _child ∈ smoothChildren, ((2 * Real.log 2) * C) ^ 6 := by
          apply Finset.sum_le_sum
          intro child _
          rw [← logTensorMixed_norm_integral_eq_prod chi orders child]
          exact logTensorMixed_L1_le chi hchi hsmall hlarge
            K C hC orders child horders
    _ = (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6 := by simp

/-- The same quantitative total applies to every original dyadic index
family through the previously established exact log-chart equality. -/
theorem all_scaledTensorMixed_children_L1_le
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) (C : ℝ)
    (hC : ∀ (k : ℕ) (a : Fin 3) (u : ℝ),
      k ≤ K → ‖iteratedDeriv k (logChild chi a) u‖ ≤ C)
    (label orders : Fin 6 → ℕ)
    (horders : ∀ i : Fin 6, orders i ≤ K) :
    (∫ u : Fin 6 → ℝ,
      ∑ child ∈ smoothChildren, ‖scaledTensorMixed chi label orders child u‖) ≤
      (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6 := by
  rw [all_scaledTensorMixed_children_norm_integral_eq chi hchi hsmall hlarge label orders]
  rw [← all_logTensorMixed_children_norm_integral_eq chi hchi hsmall hlarge orders]
  exact all_logTensorMixed_children_L1_le chi hchi hsmall hlarge
    K C hC orders horders

/-- Existence of one common finite cutoff-dependent C_K for all six-slot
integral bounds, derived from the original plateau and C-infinity only. -/
theorem exists_all_scaledTensorMixed_children_L1_bound
    (chi : ℝ → ℂ) (hchi : ContDiff ℝ ⊤ chi)
    (hsmall : ∀ t : ℝ, t ≤ 1 → chi t = 1)
    (hlarge : ∀ t : ℝ, 2 ≤ t → chi t = 0)
    (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (label orders : Fin 6 → ℕ),
        (∀ i : Fin 6, orders i ≤ K) →
        (∫ u : Fin 6 → ℝ,
          ∑ child ∈ smoothChildren,
            ‖scaledTensorMixed chi label orders child u‖) ≤
            (smoothChildren.card : ℝ) * ((2 * Real.log 2) * C) ^ 6 := by
  obtain ⟨C, hCnonneg, hC⟩ :=
    logChild_uniform_global_finite_order chi hchi hsmall hlarge K
  refine ⟨C, hCnonneg, ?_⟩
  intro label orders horders
  exact all_scaledTensorMixed_children_L1_le chi hchi hsmall hlarge
    K C hC label orders horders

end
end ImbalancedChen.P3HBSmoothTensorQuantitativeL1
