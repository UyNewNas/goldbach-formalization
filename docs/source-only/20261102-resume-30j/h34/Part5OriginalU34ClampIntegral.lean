import ImbalancedChen.Part5OriginalU34PhysicalCutoffSource
import ImbalancedChen.P5ZU11ActualH248Ordinary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The actual H430 clamp in the original U3 tail has positive measure.
Its exact integral is computed below from a logarithmic primitive.
The U11 import is used ONLY for the table-independent upperAtom_unique;
no H248 value, history or analytic licence is transferred to H430.
-/

namespace ImbalancedChen.Part5UpperTables.OriginalU34

noncomputable section

open Set MeasureTheory
open Part5OriginalUpsilon5CausalDictionary
open scoped BigOperators

def clampStart : ℝ := 833 / 2500
def clampKnot : Fin 201 := ⟨50, by norm_num⟩

/-- The clamp is entirely in the ideal half-level U3 tail. -/
theorem U3_rootArgument_eq_two_iff {t : ℝ} :
    rootArgument (U3Residual 0) t = 2 ↔ clampStart ≤ t := by
  have ha : 0 < a := by norm_num [a]
  constructor
  · intro h
    have hq : U3Residual 0 t / a ≤ 2 := (le_max_right _ _).trans_eq h
    have hr : U3Residual 0 t ≤ 2 * a := (div_le_iff₀ ha).mp hq
    by_cases hte : t < tailCutoff
    · have hm := mainResidual_gt_two_a hte
      simp only [U3Residual, if_pos hte] at hr
      linarith
    · simp only [U3Residual, if_neg hte, sub_zero] at hr
      dsimp [tailResidual, clampStart, a] at *
      linarith
  · intro ht
    have hte : ¬t < tailCutoff := by dsimp [clampStart, tailCutoff] at *; linarith
    have hq : tailResidual t / a ≤ 2 := by
      apply (div_le_iff₀ ha).mpr
      dsimp [tailResidual, clampStart, a] at *
      linarith
    simp [rootArgument, U3Residual, hte, max_eq_left hq]

theorem U4_rootArgument_gt_two {t : ℝ} (ht : t ∈ Ico a (59 / 250 : ℝ)) :
    2 < rootArgument mainResidual t := by
  have hte : t < tailCutoff := ht.2.trans (by norm_num [tailCutoff])
  have hq : 2 < mainResidual t / a :=
    (lt_div_iff₀ (by norm_num [a] : 0 < a)).mpr (mainResidual_gt_two_a hte)
  exact hq.trans_le (le_max_right _ _)

/-- Pulling back the single scalar knot s=2 gives a whole interval. -/
theorem U3_clamp_atom_exact :
    Ico a (1 / 3 : ℝ) ∩ rootAtom (fun t => U3Residual 0 t / a) (.inr clampKnot) =
      Ico clampStart (1 / 3 : ℝ) := by
  ext t
  constructor
  · rintro ⟨ht, hk⟩
    change (max 2 (U3Residual 0 t / a) ∈ Icc (2 : ℝ) 5 ∧
      max 2 (U3Residual 0 t / a) = floorGrid 50) at hk
    have hg : floorGrid 50 = 2 := by norm_num [floorGrid]
    have hq : rootArgument (U3Residual 0) t = 2 := by
      simpa only [rootArgument, hg] using hk.2
    exact ⟨U3_rootArgument_eq_two_iff.mp hq, ht.2⟩
  · intro ht
    have hq := U3_rootArgument_eq_two_iff.mpr ht.1
    refine ⟨⟨le_trans (by norm_num [a, clampStart]) ht.1, ht.2⟩, ?_⟩
    change (rootArgument (U3Residual 0) t ∈ Icc (2 : ℝ) 5 ∧
      rootArgument (U3Residual 0) t = floorGrid 50)
    rw [hq]
    norm_num [floorGrid]

theorem U3_clamp_volume :
    volume (Ico a (1 / 3 : ℝ) ∩
      rootAtom (fun t => U3Residual 0 t / a) (.inr clampKnot)) =
      ENNReal.ofReal (1 / 7500 : ℝ) := by
  rw [U3_clamp_atom_exact, Real.volume_Ico]
  norm_num [clampStart]

theorem U3_clamp_volume_pos :
    0 < volume (Ico a (1 / 3 : ℝ) ∩
      rootAtom (fun t => U3Residual 0 t / a) (.inr clampKnot)) := by
  rw [U3_clamp_volume]
  positivity

/-- Both adjacent CLOSED cells determine the actual H430 clamp value.
This is a lookup identity only; it does not assert analytic table soundness. -/
theorem H430_two_eq_adjacent_min :
    H430 2 = min (floorValue H430Numerators 49) (floorValue H430Numerators 50) := by
  have hb : (2 : ℝ) ∈ upperAtomSet (.inr clampKnot) := by
    norm_num [upperAtomSet, clampKnot, floorGrid]
  have heq : H430 2 = floorAtomValue H430Numerators (.inr clampKnot) := by
    unfold H430 upperFloor
    calc
      _ = (upperAtomSet (.inr clampKnot)).indicator
          (fun _ => floorAtomValue H430Numerators (.inr clampKnot)) 2 := by
        apply Finset.sum_eq_single (.inr clampKnot)
        · intro b _ hne
          exact indicator_of_notMem
            (fun h => hne (P5Z.U11H248.upperAtom_unique h hb)) _
        · intro h
          exact (h (Finset.mem_univ _)).elim
      _ = _ := indicator_of_mem hb _
  rw [heq]
  norm_num [floorAtomValue, floorKnotValue, clampKnot]

theorem U3_coefficient_on_clamp {t : ℝ} (ht : clampStart ≤ t) :
    U3H430Coefficient t = (upperAmplitude 2 - H430 2) * branchWeight tailResidual t := by
  have hte : tailCutoff ≤ t := (by norm_num [tailCutoff, clampStart] :
    tailCutoff ≤ clampStart).trans ht
  have hq : tailResidual t / a ≤ 2 := by
    apply (div_le_iff₀ (by norm_num [a] : 0 < a)).mpr
    dsimp [tailResidual, clampStart, a] at *
    linarith
  simp [U3H430Coefficient, not_lt.mpr hte, hte, branchCoefficient,
    rootArgument, upperRoot, H430, max_eq_left hq]

private theorem hasDerivAt_tail_primitive {t : ℝ} (ht : 0 < t) (hu : t < 1 / 2) :
    HasDerivAt (fun x : ℝ => 8 * (Real.log x - Real.log (1 / 2 - x)))
      (branchWeight tailResidual t) t := by
  have hg : 0 < (1 / 2 : ℝ) - t := by linarith
  have hlog := ((hasDerivAt_id t).const_sub (1 / 2 : ℝ)).log hg.ne'
  have hd := ((Real.hasDerivAt_log ht.ne').sub hlog).const_mul 8
  apply hd.congr_deriv
  dsimp [branchWeight, tailResidual]
  field_simp [ht.ne', hg.ne'] <;> ring

/-- Exact mass of the original positive-measure tail clamp. No quadrature
or finite-certificate result is used: this is a logarithmic primitive. -/
theorem integral_clamp_tailWeight :
    (∫ t in Ico clampStart (1 / 3 : ℝ), branchWeight tailResidual t) =
      8 * Real.log (834 / 833 : ℝ) := by
  have hab : clampStart ≤ (1 / 3 : ℝ) := by norm_num [clampStart]
  have hc : Icc clampStart (1 / 3 : ℝ) ⊆ coordinateInterval := by
    intro t ht
    exact ⟨le_trans (by norm_num [clampStart, a]) ht.1, ht.2⟩
  have hcont : ContinuousOn (branchWeight tailResidual) (Icc clampStart (1 / 3 : ℝ)) :=
    (continuousOn_branchWeight continuous_tailResidual (fun _ ht => tailResidual_bounds ht)).mono hc
  have hd : ∀ t ∈ uIcc clampStart (1 / 3 : ℝ),
      HasDerivAt (fun x : ℝ => 8 * (Real.log x - Real.log (1 / 2 - x)))
        (branchWeight tailResidual t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    apply hasDerivAt_tail_primitive
    · exact lt_of_lt_of_le (by norm_num [clampStart]) ht.1
    · linarith [ht.2]
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable_of_Icc hab)]
  dsimp only
  rw [← Real.log_div (by norm_num : (1 / 3 : ℝ) ≠ 0)
      (by norm_num : (1 / 2 - 1 / 3 : ℝ) ≠ 0),
    ← Real.log_div (by norm_num [clampStart] : clampStart ≠ 0)
      (by norm_num [clampStart] : (1 / 2 : ℝ) - clampStart ≠ 0)]
  have hu : (1 / 3 : ℝ) / (1 / 2 - 1 / 3) = 2 := by norm_num
  have hl : clampStart / (1 / 2 - clampStart) = (833 / 417 : ℝ) := by
    norm_num [clampStart]
  rw [hu, hl]
  calc
    8 * Real.log 2 - 8 * Real.log (833 / 417 : ℝ) =
        8 * (Real.log 2 - Real.log (833 / 417 : ℝ)) := by ring
    _ = 8 * Real.log ((2 : ℝ) / (833 / 417)) := by
      rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0)
        (by norm_num : (833 / 417 : ℝ) ≠ 0)]
    _ = _ := by norm_num

theorem integral_clamp_tailWeight_pos :
    0 < ∫ t in Ico clampStart (1 / 3 : ℝ), branchWeight tailResidual t := by
  rw [integral_clamp_tailWeight]
  exact mul_pos (by norm_num) (Real.log_pos (by norm_num))

/-- A concrete piece of the original U3 integral endpoint, with the exact
adopted H430 adjacent-cell floor retained. U4 has no such clamp piece. -/
theorem integral_U3H430_clamp_exact :
    (∫ t in Ico clampStart (1 / 3 : ℝ), U3H430Coefficient t) =
      (upperAmplitude 2 -
        min (floorValue H430Numerators 49) (floorValue H430Numerators 50)) *
          (8 * Real.log (834 / 833 : ℝ)) := by
  calc
    _ = ∫ t in Ico clampStart (1 / 3 : ℝ),
        (upperAmplitude 2 - H430 2) * branchWeight tailResidual t := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro t ht
      exact U3_coefficient_on_clamp ht.1
    _ = _ := by
      rw [integral_const_mul, integral_clamp_tailWeight, H430_two_eq_adjacent_min]

def originalU34Integral : ℝ :=
  (∫ t in Ico a (1 / 3 : ℝ), U3H430Coefficient t) +
    ∫ t in Ico a (59 / 250 : ℝ), U4H430Coefficient t

/-- The non-null clamp is paid exactly in the original combined integral.
The remaining two integrals are the actual unclamped U3 prefix and U4;
neither has been replaced by a numerical endpoint hypothesis. -/
theorem originalU34Integral_eq_unclamped_add_exact_clamp :
    originalU34Integral =
      ((∫ t in Ico a clampStart, U3H430Coefficient t) +
        ∫ t in Ico a (59 / 250 : ℝ), U4H430Coefficient t) +
      (upperAmplitude 2 -
        min (floorValue H430Numerators 49) (floorValue H430Numerators 50)) *
          (8 * Real.log (834 / 833 : ℝ)) := by
  have hab : a ≤ clampStart := by norm_num [a, clampStart]
  have hbc : clampStart ≤ (1 / 3 : ℝ) := by norm_num [clampStart]
  have hsplit : Ico a (1 / 3 : ℝ) = Ico a clampStart ∪ Ico clampStart (1 / 3 : ℝ) := by
    ext t
    constructor
    · intro ht
      by_cases h : t < clampStart
      · exact Or.inl ⟨ht.1, h⟩
      · exact Or.inr ⟨le_of_not_gt h, ht.2⟩
    · rintro (ht | ht)
      · exact ⟨ht.1, ht.2.trans_le hbc⟩
      · exact ⟨hab.trans ht.1, ht.2⟩
  have hdis : Disjoint (Ico a clampStart) (Ico clampStart (1 / 3 : ℝ)) := by
    apply disjoint_left.mpr
    intro t ht hu
    exact (not_lt_of_ge hu.1) ht.2
  have hi1 : IntegrableOn U3H430Coefficient (Ico a clampStart) :=
    integrableOn_U3H430Coefficient.mono_set (fun _ ht => ⟨ht.1, ht.2.trans_le hbc⟩)
  have hi2 : IntegrableOn U3H430Coefficient (Ico clampStart (1 / 3 : ℝ)) :=
    integrableOn_U3H430Coefficient.mono_set (fun _ ht => ⟨hab.trans ht.1, ht.2⟩)
  unfold originalU34Integral
  rw [hsplit, setIntegral_union hdis measurableSet_Ico hi1 hi2,
    integral_U3H430_clamp_exact]
  ring

end
end ImbalancedChen.Part5UpperTables.OriginalU34
