import ImbalancedChen.Part5OriginalH430RequestedCandidateLevel

/-!
Manuscript-internal SIGNED one-step comparison on the actual generated
request level. SOURCE ONLY / UNCOMPILED / ZERO KERNEL CREDIT.

The requested bank and strict Buchstab winners are compared to their
own ORIGINAL ideal rows, using coefficientwise absolute errors already
supplied upstream. Retention is an exactly copied old cell. There is
no assumption that the generated level is the full original U3/U4
arithmetic prime-count source, and no new base/seed/floor licence.
-/
namespace ImbalancedChen.Part5OriginalH430RequestedSignedStep

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open Part5OriginalBuchstabImmutable430Budget
open Part5OriginalH430PhysicalRoots
open P2EnhancedLowerPrimeChildCarriers P2OriginalChildPhysicalNormalization
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430ImmutableBankProfiles
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLocalBankSupply
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedNonbankSupply
open Part5OriginalH430RequestedNonbankLevel
open Part5OriginalH430RequestedAllChoice
open Part5OriginalH430RequestedAllFeedbackBudget

/-- Elementary finite weighted absolute-error inequality. This uses
the same finite index, so repeated source occurrences are not quotiented
by their prime products or physical catalog labels. -/
private theorem weighted_abs_difference {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w x y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    |(∑ i ∈ s, w i * x i) - (∑ i ∈ s, w i * y i)| ≤
      ∑ i ∈ s, w i * |x i - y i| := by
  have heq :
      (∑ i ∈ s, w i * x i) - (∑ i ∈ s, w i * y i) =
        ∑ i ∈ s, w i * (x i - y i) := by
    calc
      (∑ i ∈ s, w i * x i) - (∑ i ∈ s, w i * y i) =
          ∑ i ∈ s, (w i * x i - w i * y i) :=
            (Finset.sum_sub_distrib).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [heq]
  calc
    |∑ i ∈ s, w i * (x i - y i)| ≤
        ∑ i ∈ s, |w i * (x i - y i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hw i hi)]

/-- Exactly the old-array value of each actually selected bank branch. -/
def bankActual (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a,
    levelMark l *
      edgeValue (rootQ N n root tau p) (iterate g.val)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)

/-- The original bank idealCellProfile at the SAME parent and old array.
It is not a new analytic density or an asserted arithmetic count. -/
def bankIdeal (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action) : ℝ :=
  ∑ l ∈ selectedLevel N n root tau p g a,
    levelMark l *
      (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
        idealCellProfile (precedingH g) (precedingh g) a)

/-- Both strict Buchstab polarities, at the original selected ceiling. -/
def buchstabActual (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ selectedBuchstabLevel N n root tau p g,
    levelMark l *
      edgeValue (rootQ N n root tau p) (iterate g.val)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val (levelOccurrence l).current)

def buchstabIdeal (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ selectedBuchstabLevel N n root tau p g,
    levelMark l *
      (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
        idealProfile (levelOccurrence l).current.node.upper
          (levelOccurrence l).current.node.physical
          (precedingH g) (precedingh g))

/-- Retention carries its exact preceding-cell value into the ideal:
no extra coefficient or artificial epsilon payment. -/
def generatedIdeal (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  (∑ a : Original106Action, bankIdeal N n root tau p g a) +
    buchstabIdeal N n root tau p g +
    retainedLevelValue N n root tau p g

def buchstabAppliedError (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) : ℝ :=
  ∑ l ∈ selectedBuchstabLevel N n root tau p g,
    levelMark l *
      |edgeValue (rootQ N n root tau p) (iterate g.val)
        (levelOccurrence l).current
        (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) -
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          idealProfile (levelOccurrence l).current.node.upper
            (levelOccurrence l).current.node.physical
            (precedingH g) (precedingh g)|

theorem bank_abs_le_applied (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (a : Original106Action) :
    |bankActual N n root tau p g a - bankIdeal N n root tau p g a| ≤
      levelAppliedError N n root tau p g a := by
  unfold bankActual bankIdeal levelAppliedError
  exact weighted_abs_difference
    (selectedLevel N n root tau p g a)
    (fun l => levelMark l)
    (fun l => edgeValue (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current))
    (fun l => thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) *
      idealCellProfile (precedingH g) (precedingh g) a)
    (by intro l _; exact (mark_pos _).le)

theorem buchstab_abs_le_applied (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) :
    |buchstabActual N n root tau p g -
      buchstabIdeal N n root tau p g| ≤
        buchstabAppliedError N n root tau p g := by
  unfold buchstabActual buchstabIdeal buchstabAppliedError
  exact weighted_abs_difference
    (selectedBuchstabLevel N n root tau p g)
    (fun l => levelMark l)
    (fun l => edgeValue (rootQ N n root tau p) (iterate g.val)
      (levelOccurrence l).current
      (children N (rootQ N n root tau p) g.val (levelOccurrence l).current))
    (fun l => thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) *
      idealProfile (levelOccurrence l).current.node.upper
        (levelOccurrence l).current.node.physical
        (precedingH g) (precedingh g))
    (by intro l _; exact (mark_pos _).le)

/-- The actual selected strict-prime branch has the original absolute
arithmetic ROW error as a stronger estimate. Neither scalar ownership
nor a synthetic bound on its signed value is assumed. -/
theorem buchstab_applied_le_rowError (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    buchstabAppliedError N n root tau p g ≤
      buchstabLevelError N n root tau p g := by
  unfold buchstabAppliedError buchstabLevelError
  apply Finset.sum_le_sum
  intro l hl
  have ho := (levelOccurrence_source l).1
  have hc := rootHistory_coherent hN ht ht' hn hp hband ho
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hl).2
  have ha := requested_buchstab_applied_le (g := g) hc hi
  have hrow :
      |edgeValue (rootQ N n root tau p) (iterate g.val)
         (levelOccurrence l).current
         (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) -
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
          idealProfile (levelOccurrence l).current.node.upper
            (levelOccurrence l).current.node.physical
            (precedingH g) (precedingh g)| ≤
      ∑ b : RowAtom,
        |edgeRow (rootQ N n root tau p) (levelOccurrence l).current
            (children N (rootQ N n root tau p) g.val (levelOccurrence l).current) b -
          thetaAtom N (rootQ N n root tau p)
            (parentProduct (levelOccurrence l).current.old) *
            integralRow (levelOccurrence l).current.node.upper
              (levelOccurrence l).current.node.physical b| *
          |oldAtomValue (precedingH g) (precedingh g) b| := by
    simpa only [strictAbsoluteError, ← requested_buchstab_row_eq hc hi] using ha
  exact mul_le_mul_of_nonneg_left hrow (mark_pos _).le

/-- The generated action value uses ONE winner at each old cell. This
does not collapse its tagged occurrences or assert U3/U4 count coverage. -/
theorem generationValue_as_actual (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    generationValue N n root tau p g =
      (∑ a : Original106Action, bankActual N n root tau p g a) +
      buchstabActual N n root tau p g +
      retainedLevelValue N n root tau p g := by
  simpa only [bankActual, buchstabActual] using
    generationValue_partition N n root tau p g

theorem generated_difference (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) :
    generationValue N n root tau p g - generatedIdeal N n root tau p g =
      (∑ a : Original106Action,
        bankActual N n root tau p g a - bankIdeal N n root tau p g a) +
      (buchstabActual N n root tau p g -
        buchstabIdeal N n root tau p g) := by
  calc
    generationValue N n root tau p g - generatedIdeal N n root tau p g =
        (∑ a : Original106Action, bankActual N n root tau p g a) -
        (∑ a : Original106Action, bankIdeal N n root tau p g a) +
        (buchstabActual N n root tau p g -
          buchstabIdeal N n root tau p g) := by
            rw [generationValue_as_actual]
            unfold generatedIdeal
            ring
    _ = _ := by rw [Finset.sum_sub_distrib]

/-- ACTUAL one-step signed feedback comparison, with the same previous
array and both read modes. It remains below the arithmetic count bridge. -/
theorem generated_abs_le_combined (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (hN : 1 < N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root) :
    |generationValue N n root tau p g - generatedIdeal N n root tau p g| ≤
      combinedError N n root tau p g := by
  rw [generated_difference]
  have hb :
      |∑ a : Original106Action,
        bankActual N n root tau p g a - bankIdeal N n root tau p g a| ≤
        ∑ a : Original106Action, levelAppliedError N n root tau p g a := by
    calc
      _ ≤ ∑ a : Original106Action,
        |bankActual N n root tau p g a - bankIdeal N n root tau p g a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun a _ =>
        bank_abs_le_applied N n root tau p g a)
  calc
    |(∑ a : Original106Action,
        bankActual N n root tau p g a - bankIdeal N n root tau p g a) +
        (buchstabActual N n root tau p g -
          buchstabIdeal N n root tau p g)| ≤
      |∑ a : Original106Action,
        bankActual N n root tau p g a - bankIdeal N n root tau p g a| +
      |buchstabActual N n root tau p g -
        buchstabIdeal N n root tau p g| := abs_add_le _ _
    _ ≤ (∑ a : Original106Action, levelAppliedError N n root tau p g a) +
        buchstabLevelError N n root tau p g := add_le_add hb
          ((buchstab_abs_le_applied N n root tau p g).trans
            (buchstab_applied_le_rowError N n root tau p g hN ht ht' hn hp hband))
    _ ≤ combinedError N n root tau p g := by
      unfold combinedError
      exact add_le_add
        (Finset.sum_le_sum (fun a _ => level_applied_error_le N n root tau p g a))
        le_rfl

/-- Uniform TWO-SIDED signed step, plus exact zero-Theta equality. One
threshold is chosen before N, root, precision, original prime and
generation. No extra 5+12 budget or new arithmetic source hypothesis. -/
theorem uniform_generated_signed_step {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ n : ℕ, ∀ root : Root, ∀ tau : ℝ,
      0 ≤ tau → tau ≤ 1/12 → 1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
      physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430,
        (generatedIdeal N n root tau p g -
            epsilon * combinedTheta N n root tau p g ≤
          generationValue N n root tau p g) ∧
        (generationValue N n root tau p g ≤
          generatedIdeal N n root tau p g +
            epsilon * combinedTheta N n root tau p g) ∧
        (combinedTheta N n root tau p g = 0 →
          generationValue N n root tau p g =
            generatedIdeal N n root tau p g) := by
  obtain ⟨T,hT,hbudget⟩ := uniform_combined_feedback he
  refine ⟨T,hT,?_⟩
  intro N hN n root tau ht ht' hn p hp hband g
  have hε := (hbudget N hN n root tau ht ht' hn p hp hband g).1
  have herr := (generated_abs_le_combined N n root tau p g
    (by omega : 1 < N) ht ht' hn hp hband).trans hε
  have hparts := abs_le.mp herr
  refine ⟨?_,?_,?_⟩
  · linarith only [hparts.1]
  · linarith only [hparts.2]
  · intro hz
    have heq :
        |generationValue N n root tau p g -
          generatedIdeal N n root tau p g| = 0 := by
      apply le_antisymm
      · simpa only [hz,mul_zero] using herr
      · exact abs_nonneg _
    exact sub_eq_zero.mp (abs_eq_zero.mp heq)

end
end ImbalancedChen.Part5OriginalH430RequestedSignedStep
