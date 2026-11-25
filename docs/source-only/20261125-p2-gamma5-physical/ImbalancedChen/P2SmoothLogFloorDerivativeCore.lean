import ImbalancedChen.P2SmoothPositiveArgumentCore
import ImbalancedChen.P4BSmoothStepDerivativeBudget
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lean.Elab.Tactic.Omega

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

The existing scalar log-floor bound is extracted from the original
Part5OriginalH430ClassicalSmoothEulerBounds owner. Its original statement
and proof argument are retained, with compiler-directed API repairs to
order coercions, neighborhood elaboration, and floorGate unfolding.
The generic plateau_bound is public so the remaining original
log_upper_bound can reuse this single owner instead of duplicating a
private proof. The initial exact extraction and all subsequent API repairs
are recorded in SCALAR_EULER_EXTRACTION_MANIFEST.json.
-/
namespace ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds
noncomputable section
open Finset Set Filter Real
open P4B
open Part5OriginalH430ClassicalSmoothOuterWeight (floorGate)
open scoped Classical Topology BigOperators ContDiff

def ScalarBound (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ,∃ C : ℝ,0≤C ∧ ∀ x,|iteratedDeriv n f x|≤C

theorem plateau_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ∀x,|f x|≤1)
    {l u v w : ℝ} (hl : ∀x,x≤l → f x=v) (hu : ∀x,u≤x → f x=w) : ScalarBound f := by
  refine ⟨hf,?_⟩
  intro n
  cases n with
  | zero => exact ⟨1,zero_le_one,by simpa only [iteratedDeriv_zero] using hb⟩
  | succ m =>
    have hcont := ContDiff.continuous_iteratedDeriv' (m+1)
      (hf.of_le (show ((m+1 : ℕ) : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc l u)).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max 0 B,le_max_left _ _,?_⟩
    intro x
    by_cases hx : x<l
    · have hlocal : f=ᶠ[𝓝 x](fun _ => v) := by
        filter_upwards [Iio_mem_nhds hx] with p hp
        exact hl p hp.le
      rw [hlocal.iteratedDeriv_eq (m+1),iteratedDeriv_const,if_neg (by omega),abs_zero]
      exact le_max_left _ _
    by_cases hx' : u<x
    · have hlocal : f=ᶠ[𝓝 x](fun _ => w) := by
        filter_upwards [Ioi_mem_nhds hx'] with p hp
        exact hu p hp.le
      rw [hlocal.iteratedDeriv_eq (m+1),iteratedDeriv_const,if_neg (by omega),abs_zero]
      exact le_max_left _ _
    exact (show |iteratedDeriv (m+1) f x|≤B by
      simpa only [Real.norm_eq_abs] using hB x ⟨le_of_not_gt hx,le_of_not_gt hx'⟩).trans (le_max_right _ _)

theorem log_floor_bound : ScalarBound (fun u => floorGate (exp u)) := by
  apply plateau_bound (l:=log (1/2:ℝ)) (u:=0) (v:=0) (w:=1)
  · exact (contDiff_smoothGateUpperStep _).comp (contDiff_exp.sub contDiff_const)
  · intro x
    change |smoothGateUpperStep (1/2) (exp x-1)| ≤ 1
    rw [abs_of_nonneg (smoothGateUpperStep_nonneg _ _)]
    exact smoothGateUpperStep_le_one _ _
  · intro x hx
    apply smoothGateUpperStep_eq_zero (by norm_num)
    have h := exp_le_exp.mpr hx
    rw [exp_log (by norm_num : (0:ℝ)<1/2)] at h
    linarith only [h]
  · intro x hx
    apply smoothGateUpperStep_eq_one (by norm_num)
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hx)

end
end ImbalancedChen.Part5OriginalH430ClassicalSmoothEulerBounds
