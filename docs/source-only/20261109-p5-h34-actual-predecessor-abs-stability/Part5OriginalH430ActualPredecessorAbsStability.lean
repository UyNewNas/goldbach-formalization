import ImbalancedChen.Part5OriginalH430ActualSelectedFeedbackOperator

/-!
P5.6 / h34 — automatic genuine predecessor absolute-mass bound and
signed stability of the ACTUAL winning Buchstab/106-bank row.

This is a refinement of the immediately preceding true old-array
consumer, not a new candidate selector, scalar owner, root count, or
replacement sieve estimate. The original winning Fin occurrences and
the separate 12*bankTheta / 5*BuchstabTheta charges are unchanged.

The old-array bound is now obtained from its literal finite RowAtom
entries, not provided as a free external M. A second theorem controls
the change in the selected row under TWO arbitrary signed predecessor
arrays: the missing future feedback-to-integral comparison may use
this bound only after identifying its actual old and ideal vectors.
No theorem below asserts that the resulting absolute mass is <= 1,
or that the original U3/U4 arithmetic count is closed.

SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualPredecessorAbsStability

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedHistory
open Part5OriginalH430ActualRequestNonbankQuantitative
open Part5OriginalH430ActualSelectedRowBudget
open Part5OriginalH430ActualSelectedFeedbackOperator

/-- Explicit finite absolute-mass of the ACTUAL old feedback array.
It is not an arbitrary a priori bound, nor the original q/tag count. -/
def predecessorAbsMass (g : Fin 430) : ℝ :=
  ∑ b : RowAtom,
    |oldAtomValue (precedingH g) (precedingh g) b|

theorem predecessor_abs_mass_nonneg (g : Fin 430) :
    0 ≤ predecessorAbsMass g := by
  unfold predecessorAbsMass
  exact Finset.sum_nonneg (fun b _ => abs_nonneg _)

/-- Every actual preceding atom is bounded by the literal finite
absolute mass of the SAME generation, including signed atoms. -/
theorem predecessor_abs_le_mass (g : Fin 430) (b : RowAtom) :
    |oldAtomValue (precedingH g) (precedingh g) b| ≤
      predecessorAbsMass g := by
  unfold predecessorAbsMass
  exact Finset.single_le_sum
    (fun c _ => abs_nonneg (oldAtomValue (precedingH g) (precedingh g) c))
    (Finset.mem_univ b)

/-- There is no longer an unexplained preceding-array M premise:
the finite original predecessor array supplies a valid M itself.
The 12/5 bounds remain distinct and no bank error is paid twice. -/
theorem actual_selected_old_read_l1_envelope
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) :
    |actualSelectedOldRead N n root tau p g| ≤
      (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) *
          predecessorAbsMass g := by
  exact actual_selected_old_read_le_row_budget
    N n root tau p g (predecessorAbsMass g)
    (predecessor_abs_mass_nonneg g)
    (predecessor_abs_le_mass g) hRow hMass

/-- For any pair of signed arrays, the ACTUAL winning row is Lipschitz
in the finite absolute difference. Only genuinely selected physical
positions contribute; no unselected bank alternative or retention
request is inserted into the coefficient norm. -/
theorem actual_selected_row_difference_l1
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (v w : RowAtom → ℝ)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) :
    |(∑ b : RowAtom, actualSelectedRow N n root tau p g b * v b) -
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b * w b)| ≤
      (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) *
        (∑ b : RowAtom, |v b - w b|) := by
  have hdiffNonneg : 0 ≤ (∑ b : RowAtom, |v b - w b|) := by
    exact Finset.sum_nonneg (fun b _ => abs_nonneg (v b - w b))
  have hentry (b : RowAtom) :
      |v b - w b| ≤ (∑ c : RowAtom, |v c - w c|) := by
    exact Finset.single_le_sum
      (fun c _ => abs_nonneg (v c - w c)) (Finset.mem_univ b)
  have hsplit :
      (∑ b : RowAtom,
        actualSelectedRow N n root tau p g b * (v b - w b)) =
      (∑ b : RowAtom,
        actualSelectedRow N n root tau p g b * v b) -
      (∑ b : RowAtom,
        actualSelectedRow N n root tau p g b * w b) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← hsplit]
  calc
    |∑ b : RowAtom,
        actualSelectedRow N n root tau p g b * (v b - w b)| ≤
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) *
        (∑ c : RowAtom, |v c - w c|) := by
          exact nonnegative_row_old_input_bound
            (actualSelectedRow N n root tau p g)
            (fun b => v b - w b)
            (∑ c : RowAtom, |v c - w c|)
            hRow hentry
    _ ≤ (12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g) *
        (∑ c : RowAtom, |v c - w c|) :=
      mul_le_mul_of_nonneg_right hMass hdiffNonneg

/-- A single N-threshold controls the TRUE predecessor feedback
and arbitrary signed perturbations of the selected row. This removes
the former caller-supplied M for the TRUE array, but does not assert
a uniform numerical bound on its finite absolute mass. -/
theorem uniform_actual_predecessor_abs_stability
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
        0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        actualSelectedError N n root tau p g ≤
          epsilon * actualSelectedTheta N n root tau p g ∧
        actualBankAppliedError N n root tau p g ≤
          epsilon * actualBankTheta N n root tau p g ∧
        |actualSelectedOldRead N n root tau p g| ≤
          (12 * actualBankTheta N n root tau p g +
            5 * actualBuchstabTheta N n root tau p g) *
              predecessorAbsMass g ∧
        (∀ v w : RowAtom → ℝ,
          |(∑ b : RowAtom,
            actualSelectedRow N n root tau p g b * v b) -
            (∑ b : RowAtom,
              actualSelectedRow N n root tau p g b * w b)| ≤
            (12 * actualBankTheta N n root tau p g +
              5 * actualBuchstabTheta N n root tau p g) *
              (∑ b : RowAtom, |v b - w b|)) := by
  obtain ⟨T, hT4, hT⟩ :=
    uniform_actual_selected_error_row_budget he
  refine ⟨T, hT4, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have h := hT N hN n root tau ht ht' hn p hp hband g
  refine ⟨h.2.2.2.1, h.2.1, ?_, ?_⟩
  · exact actual_selected_old_read_l1_envelope
      N n root tau p g h.2.2.2.2.1 h.2.2.2.2.2
  · intro v w
    exact actual_selected_row_difference_l1
      N n root tau p g v w h.2.2.2.2.1 h.2.2.2.2.2

/-- Zero genuine bank AND zero genuine Buchstab Theta force the true
old-array selected operator to vanish, without any normalization by
Theta and without assuming all old atoms vanish. -/
theorem actual_selected_old_read_zero_of_zero_thetas
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430)
    (hRow : ∀ b : RowAtom,
      0 ≤ actualSelectedRow N n root tau p g b)
    (hMass :
      (∑ b : RowAtom, actualSelectedRow N n root tau p g b) ≤
        12 * actualBankTheta N n root tau p g +
        5 * actualBuchstabTheta N n root tau p g)
    (hBank : actualBankTheta N n root tau p g = 0)
    (hBuch : actualBuchstabTheta N n root tau p g = 0) :
    actualSelectedOldRead N n root tau p g = 0 := by
  have h := actual_selected_old_read_l1_envelope
    N n root tau p g hRow hMass
  rw [hBank, hBuch] at h
  have hz : |actualSelectedOldRead N n root tau p g| ≤ 0 := by
    simpa using h
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

end
end ImbalancedChen.Part5OriginalH430ActualPredecessorAbsStability
