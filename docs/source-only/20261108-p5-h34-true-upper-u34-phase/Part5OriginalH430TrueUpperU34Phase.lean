import ImbalancedChen.Part5OriginalU34H430Integrable

/-!
P5.6 / h34 — literal U3/U4 UPPER H430 root phase, not the lower h-start.

This packet works with the genuine original U3/U4 H430 integrable
coefficient and its actual main/tail levels and max(2,L/a) lookup.
It proves the exact three-piece U3 query phase, the U4 nonclamped
main phase, and the strictly positive tail clamp band. It does NOT
claim any original selected-count source, root receiver, Rosser owner,
full/selected/inherited count gate or historical signed payment.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL H34 OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430TrueUpperU34Phase

noncomputable section

open Set
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables
open Part5UpperTables.OriginalU34

/-- The actual upper U3 tail has raw argument (1/2-t)/a.
The precise positive-width clamp threshold is 1/2-2a. -/
def u3TailClampStart : ℝ := 1 / 2 - 2 * a

theorem u3_tail_clamp_start_exact :
    u3TailClampStart = 833 / 2500 := by
  norm_num [u3TailClampStart, a]

/-- The clamp starts strictly after the actual U3 main-to-tail switch. -/
theorem u3_tail_clamp_inside_true_tail :
    tailCutoff < u3TailClampStart ∧ u3TailClampStart < 1 / 3 := by
  norm_num [tailCutoff, u3TailClampStart, a]

/-- This interval has nonzero width; treating the clamp as an endpoint
or as a zero-mass exception would lose a genuine upper-cost region. -/
theorem u3_tail_clamp_width_exact :
    (1 / 3 : ℝ) - u3TailClampStart = 1 / 7500 := by
  norm_num [u3TailClampStart, a]

/-- An explicit interior point of the upper U3 H430 clamp band. -/
theorem u3_tail_clamp_interior_witness :
    (3333 / 10000 : ℝ) ∈ Ico u3TailClampStart (1 / 3) := by
  norm_num [u3TailClampStart, a]

theorem tail_argument_ge_two_before_clamp {t : ℝ}
    (ht : t ≤ u3TailClampStart) :
    2 ≤ tailResidual t / a := by
  have ha : (0 : ℝ) < a := by norm_num [a]
  apply (le_div_iff₀ ha).mpr
  dsimp [tailResidual, u3TailClampStart, a] at *
  linarith

theorem tail_argument_le_two_after_clamp {t : ℝ}
    (ht : u3TailClampStart ≤ t) :
    tailResidual t / a ≤ 2 := by
  have ha : (0 : ℝ) < a := by norm_num [a]
  apply (div_le_iff₀ ha).mpr
  dsimp [tailResidual, u3TailClampStart, a] at *
  linarith

/-- Below the true clamp, max(2,L/a) is the unmodified tail argument. -/
theorem tail_root_unclamped {t : ℝ}
    (ht : t ≤ u3TailClampStart) :
    rootArgument tailResidual t = tailResidual t / a := by
  simp only [rootArgument, max_eq_right (tail_argument_ge_two_before_clamp ht)]

/-- Above the true clamp, the H430 lookup is fixed at exactly 2. -/
theorem tail_root_clamped {t : ℝ}
    (ht : u3TailClampStart ≤ t) :
    rootArgument tailResidual t = 2 := by
  simp only [rootArgument, max_eq_left (tail_argument_le_two_after_clamp ht)]

/-- The literal upper U3 main branch cannot hit the clamp before the
actual switch t=57/224. This is proved from BOTH affine pieces of v,
not from the weak uniform residual bound. -/
theorem main_root_unclamped_before_switch {t : ℝ}
    (ht : t ≤ tailCutoff) :
    rootArgument mainResidual t = mainResidual t / a := by
  have ha : (0 : ℝ) < a := by norm_num [a]
  have hA : t + 2 * a ≤ VariableEnvelope.A t := by
    dsimp [VariableEnvelope.A, a, tailCutoff] at *
    linarith
  have hC : t + 2 * a ≤ VariableEnvelope.C t := by
    dsimp [VariableEnvelope.C, a, tailCutoff] at *
    linarith
  have hmin : t + 2 * a ≤
      min (VariableEnvelope.A t) (VariableEnvelope.C t) :=
    le_min hA hC
  have hres : 2 * a ≤ mainResidual t := by
    unfold mainResidual
    rw [VariableEnvelope.v_eq_min]
    linarith
  have harg : 2 ≤ mainResidual t / a :=
    (le_div_iff₀ ha).mpr (by linarith)
  simp only [rootArgument, max_eq_right harg]

/-- U4 ends at t=59/250, strictly before the U3 switch.
Its entire genuine upper H430 root is therefore un-clamped. -/
theorem u4_root_unclamped {t : ℝ}
    (ht : t ∈ Ico a (59 / 250 : ℝ)) :
    rootArgument mainResidual t = mainResidual t / a := by
  have hbound : t ≤ tailCutoff :=
    ht.2.le.trans (by norm_num [tailCutoff])
  exact main_root_unclamped_before_switch hbound

/-- Actual upper U3, first (variable-envelope) phase. -/
theorem u3_first_phase_true_H430 {t : ℝ}
    (ht : t ∈ Ico a tailCutoff) :
    U3H430Coefficient t =
      (upperAmplitude (mainResidual t / a) -
        upperRoot H430Numerators (mainResidual t / a)) *
          branchWeight mainResidual t := by
  have hnot : ¬ tailCutoff ≤ t := not_le.mpr ht.2
  have harg := main_root_unclamped_before_switch ht.2.le
  simp [U3H430Coefficient, branchCoefficient, ht.2, hnot, harg]

/-- Actual upper U3, second phase, still above raw H430 argument 2. -/
theorem u3_middle_phase_true_H430 {t : ℝ}
    (ht : t ∈ Ico tailCutoff u3TailClampStart) :
    U3H430Coefficient t =
      (upperAmplitude (tailResidual t / a) -
        upperRoot H430Numerators (tailResidual t / a)) *
          branchWeight tailResidual t := by
  have hnot : ¬ t < tailCutoff := not_lt.mpr ht.1
  have harg := tail_root_unclamped ht.2.le
  simp [U3H430Coefficient, branchCoefficient, ht.1, hnot, harg]

/-- Actual upper U3, genuine positive-width third phase. The table
lookup is at H430's knot 2, not H248 and not the ordinary lower h-start. -/
theorem u3_clamped_phase_true_H430 {t : ℝ}
    (ht : t ∈ Ico u3TailClampStart (1 / 3 : ℝ)) :
    U3H430Coefficient t =
      (upperAmplitude 2 - upperRoot H430Numerators 2) *
        branchWeight tailResidual t := by
  have htail : tailCutoff ≤ t :=
    (u3_tail_clamp_inside_true_tail).1.le.trans ht.1
  have hnot : ¬ t < tailCutoff := not_lt.mpr htail
  have harg := tail_root_clamped ht.1
  simp [U3H430Coefficient, branchCoefficient, htail, hnot, harg]

/-- U4's actual upper H430 cost uses the main residual throughout the
whole U4 domain, with NO substitution of an ordinary lower h root. -/
theorem u4_entire_phase_true_H430 {t : ℝ}
    (ht : t ∈ Ico a (59 / 250 : ℝ)) :
    U4H430Coefficient t =
      (upperAmplitude (mainResidual t / a) -
        upperRoot H430Numerators (mainResidual t / a)) *
          branchWeight mainResidual t := by
  simp only [U4H430Coefficient, branchCoefficient,
    u4_root_unclamped ht]

end
end ImbalancedChen.Part5OriginalH430TrueUpperU34Phase
