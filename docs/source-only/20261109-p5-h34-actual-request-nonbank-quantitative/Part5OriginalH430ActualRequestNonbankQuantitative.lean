import ImbalancedChen.Part5OriginalH430ActualRequestAllActionPartition
import ImbalancedChen.Part5OriginalH430RequestedCandidateLevel
import ImbalancedChen.Part5OriginalH430RequestedNonbankLevel

/-!
P5.6 / h34: bind the REAL one-generation resolver's nonbank Fin
positions to the older, independently supplied quantitative Buchstab
and exact retention consumers.  No second choice is made, and no
old scalar owner replaces the specified cell.

The full generated request READ is also bounded by the original
106 selected-bank previous-array candidates, with the selected
retention/Buchstab reads kept literally, and their genuine
Buchstab row error / 5*Theta bound transferred to the SAME indices.

Manuscript-internal intermediate source; not original U3/U4 arithmetic
count closure, not a new analytic theorem, and not a full CLOSED-CELL
induction. SOURCE ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.
-/

namespace ImbalancedChen.Part5OriginalH430ActualRequestNonbankQuantitative

noncomputable section
open scoped Classical BigOperators
open P5OriginalFeedbackTableKernels
open P5OriginalActionMassBound
open Part5OriginalH430PhysicalRoots
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430RequestedReads
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430RequestedCandidateLevel
open Part5OriginalH430ActualRequestAllActionPartition

/-- The new actual resolver and the older selected-retention supplier
see precisely the same generated Fin LIST positions. -/
theorem actual_retained_eq_selected_retained
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    retainedLevel N n root tau p g =
      selectedRetainedLevel N n root tau p g := by
  ext l
  constructor
  · intro hl
    have hc : actualChoice N n root tau p g l = some .retained :=
      (Finset.mem_filter.mp hl).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (actual_choice_iff_selected N n root tau p g l .retained).1 hc⟩
  · intro hl
    have hs : ∃ i : Fin 200,
        Selected g.val (levelOccurrence l).current i .retained :=
      (Finset.mem_filter.mp hl).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (actual_choice_iff_selected N n root tau p g l .retained).2 hs⟩

/-- The original Buchstab-row supplier is on exactly the actual
resolver's Buchstab winners, including repeated physical products. -/
theorem actual_buchstab_eq_selected_buchstab
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    buchstabLevel N n root tau p g =
      selectedBuchstabLevel N n root tau p g := by
  ext l
  constructor
  · intro hl
    have hc : actualChoice N n root tau p g l = some .buchstab :=
      (Finset.mem_filter.mp hl).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (actual_choice_iff_selected N n root tau p g l .buchstab).1 hc⟩
  · intro hl
    have hs : ∃ i : Fin 200,
        Selected g.val (levelOccurrence l).current i .buchstab :=
      (Finset.mem_filter.mp hl).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,
      (actual_choice_iff_selected N n root tau p g l .buchstab).2 hs⟩

/-- The actually selected retention CHILD value is the original
predecessor-cell read with physical theta and original path mark.
This is a source equality, not an upper bound on arithmetic counts. -/
theorem actual_retention_child_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    retainedLevelValue N n root tau p g =
      ∑ l ∈ retainedLevel N n root tau p g,
        levelMark l * thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          requestValue (iterate (g.val + 1))
            (levelOccurrence l).current := by
  rw [actual_retained_eq_selected_retained]
  exact retained_level_exact N n root tau p g

/-- Actual new-table mass, with no root-count interpretation imposed. -/
def actualRetainedRead
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ retainedLevel N n root tau p g,
    levelMark l * requestValue (iterate (g.val + 1))
      (levelOccurrence l).current

def actualBuchstabRead
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l * requestValue (iterate (g.val + 1))
      (levelOccurrence l).current

def actualBankRead
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ a : Original106Action, markedBankRead N n root tau p g a

/-- One copy per genuine winning action: unresolved requests are zero.
No scalar/specified-cell or original q/tag fibres are identified. -/
theorem actual_new_table_read_exact
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    (∑ l : Index N n root tau p g,
      levelMark l * requestValue (iterate (g.val + 1))
        (levelOccurrence l).current) =
      actualRetainedRead N n root tau p g +
      actualBuchstabRead N n root tau p g +
      actualBankRead N n root tau p g := by
  simpa only [actualRetainedRead, actualBuchstabRead, actualBankRead,
    markedBankRead] using
      (actual_level_request_value_all_actions N n root tau p g)

/-- The full TRUE new-table READ is bounded using the ORIGINAL 106
candidate formula; Buchstab and retention terms are not replaced by
unknown scalar owners or charged as bank alternatives. -/
theorem actual_new_table_read_le_bank_candidates
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    (∑ l : Index N n root tau p g,
      levelMark l * requestValue (iterate (g.val + 1))
        (levelOccurrence l).current) ≤
      actualRetainedRead N n root tau p g +
      actualBuchstabRead N n root tau p g +
      (∑ a : Original106Action,
        markedBankCandidate N n root tau p g a) := by
  rw [actual_new_table_read_exact]
  exact add_le_add_left
    (all_markedBankRead_le_candidate N n root tau p g)
    (actualRetainedRead N n root tau p g +
      actualBuchstabRead N n root tau p g)

/-- An independent definition using the NEW actualChoice Finset,
not a substituted or user-supplied Buchstab selected family. -/
def actualBuchstabTheta
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l * thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old)

def actualBuchstabError
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l * (∑ b : RowAtom,
      |edgeRow (rootQ N n root tau p) (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val
          (levelOccurrence l).current) b -
       thetaAtom N (rootQ N n root tau p)
         (parentProduct (levelOccurrence l).current.old) *
         integralRow (levelOccurrence l).current.node.upper
           (levelOccurrence l).current.node.physical b| *
       |oldAtomValue (precedingH g) (precedingh g) b|)

def actualBuchstabRow
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (b : RowAtom) : ℝ :=
  ∑ l ∈ buchstabLevel N n root tau p g,
    levelMark l * edgeRow (rootQ N n root tau p)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val
        (levelOccurrence l).current) b

theorem actual_buchstab_theta_eq_existing
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualBuchstabTheta N n root tau p g =
      buchstabLevelTheta N n root tau p g := by
  rw [actualBuchstabTheta, buchstabLevelTheta,
    actual_buchstab_eq_selected_buchstab]

theorem actual_buchstab_error_eq_existing
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) :
    actualBuchstabError N n root tau p g =
      buchstabLevelError N n root tau p g := by
  rw [actualBuchstabError, buchstabLevelError,
    actual_buchstab_eq_selected_buchstab]

theorem actual_buchstab_row_eq_existing
    (N n : ℕ) (root : Root) (tau : ℝ) (p : ℕ)
    (g : Fin 430) (b : RowAtom) :
    actualBuchstabRow N n root tau p g b =
      buchstabLevelRow N n root tau p g b := by
  rw [actualBuchstabRow, buchstabLevelRow,
    actual_buchstab_eq_selected_buchstab]

/-- One pre-N threshold: a genuine full selected-request upper step and
the original quantitatively supplied Buchstab error/mass bounds on the
SAME actualChoice Fin positions. Retention remains exact, and the bank
uses its genuine previous-array candidates; no 5+12 mass inflation. -/
theorem uniform_actual_nonbank_quantitative
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 →
      1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
      physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        ((∑ l : Index N n root tau p g,
          levelMark l * requestValue (iterate (g.val + 1))
            (levelOccurrence l).current) ≤
          actualRetainedRead N n root tau p g +
          actualBuchstabRead N n root tau p g +
          (∑ a : Original106Action,
            markedBankCandidate N n root tau p g a)) ∧
        actualBuchstabError N n root tau p g ≤
          epsilon * actualBuchstabTheta N n root tau p g ∧
        (∀ b : RowAtom, 0 ≤ actualBuchstabRow N n root tau p g b) ∧
        (∑ b : RowAtom, actualBuchstabRow N n root tau p g b) ≤
          5 * actualBuchstabTheta N n root tau p g ∧
        (actualBuchstabTheta N n root tau p g = 0 →
          actualBuchstabError N n root tau p g = 0 ∧
          ∀ b : RowAtom, actualBuchstabRow N n root tau p g b = 0) := by
  obtain ⟨T,hTlo,hT⟩ := uniform_level_buchstab_supply he
  refine ⟨T,hTlo,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hOld := hT N hN n root tau ht ht' hn p hp hband g
  refine ⟨actual_new_table_read_le_bank_candidates N n root tau p g, ?_⟩
  simpa only [actual_buchstab_error_eq_existing,
    actual_buchstab_theta_eq_existing,
    actual_buchstab_row_eq_existing] using hOld

end
end ImbalancedChen.Part5OriginalH430ActualRequestNonbankQuantitative
