import ImbalancedChen.Part5OriginalH430BuchstabCutoffCancellation
import ImbalancedChen.Part5OriginalH430FixedReadDictionary

/-!
P5.6 / h34. A genuine selected request's FIXED old-cell bank term is
bounded using the original closed-cell predecessor hypothesis. This uses
the actual 70 W1 anchor cells and the 36 W2 4:1 specified-cell mixtures.
It does NOT replace those reads with scalar closed minima, invent a base
or seed inequality, or claim original U3/U4 arithmetic count closure.

The full bank candidate still retains its literal base, per-product
integer-quotient feedback, physical prime-child sum and positive path
mark. Only its FIXED old-cell contribution is discharged, conditionally
on a prior-generation closed-cell bound. The condition is NOT inferred
from the terminal h34 goal. SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ActualFixedClosedCell

noncomputable section
open Set
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2Selected430CausalOccurrenceExporter P2EnhancedLowerPrimeChildCarriers
open Part5OriginalH430PhysicalRoots Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430RequestedReads Part5OriginalH430RequestedBranches
open Part5OriginalH430RequestedHistory Part5OriginalH430RequestedMember
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430AllActionOccurrenceSource
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430BuchstabCutoffCancellation

/-- The ORIGINAL W1 anchor and W2 physical fixed points. The W2 fixed
weights are precisely 4/5 and 1/5; no scalar owner is selected here. -/
def fixedReference (F : ℝ → ℝ) : Original106Action → ℝ
  | .inl (_, j) => F (W1Anchor j)
  | .inr j => (4 * F (originalW2At j).s0 +
      F (originalW2At j).phi1) / 5

/-- Genuine closed-cell input at the previous table. It must ultimately
be obtained from the arithmetic predecessor induction, NOT postulated as
an h34 counting conclusion. Works even for signed old arrays. -/
theorem selected_fixed_reference_upper (g : Fin 430) (F : ℝ → ℝ)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s)
    (a : Original106Action) :
    fixedValue (iterate g.val true) a ≤ fixedReference F a := by
  simpa [fixedReference] using
    fixedValue_le_of_cells (iterate g.val true) F hcells a

/-- Literal actual selected-bank candidate, with ONLY its fixed
read replaced by the same-row closed-cell predecessor upper bound.
Base, original integer feedback and the true strict-prime children
remain untouched. -/
def bankFixedReferenceGap (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (a : Original106Action) (l : Index N n root tau p g) : ℝ :=
  levelMark l *
    (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
       (baseValue a + fixedReference F a +
         feedbackValue (iterate g.val) a) -
     childTerm N n root tau p g l)

/-- The fixed-read part of every real bank candidate is paid
coefficientwise. Theta and the actual history occurrence mark are
nonnegative, so this substitution respects signs and multiplicities. -/
theorem actual_bank_fixed_upper (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430)
    (a : Original106Action) (l : Index N n root tau p g)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    bankCandidateGap N n root tau p g a l ≤
      bankFixedReferenceGap N n root tau p g F a l := by
  have hw := (rootHistory_support (by omega : 1 < N)
    ht ht' hn hp hband (levelOccurrence_source l).1).1
  have htheta : 0 ≤ thetaAtom N (rootQ N n root tau p)
      (parentProduct (levelOccurrence l).current.old) :=
    thetaAtom_nonneg hN hw.2.1 (parentWindow_logs hw).2.1
  have hfixed := selected_fixed_reference_upper g F hcells a
  have hcombo :
      baseValue a + fixedValue (iterate g.val true) a +
        feedbackValue (iterate g.val) a ≤
      baseValue a + fixedReference F a +
        feedbackValue (iterate g.val) a := by
    linarith only [hfixed]
  have hscale := mul_le_mul_of_nonneg_left hcombo htheta
  have hshift := sub_le_sub_right hscale
    (childTerm N n root tau p g l)
  have hmarked := mul_le_mul_of_nonneg_left hshift (mark_pos _).le
  simpa only [bankCandidateGap, bankFixedReferenceGap] using hmarked

/-- Each of the original 106 actual winners pays the fixed channel
ONCE. Repeated LevelIndex occurrences are summed separately. -/
theorem bank_fixed_sum_upper (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        bankCandidateGap N n root tau p g a l) ≤
    (∑ a : Original106Action,
      ∑ l ∈ selectedLevel N n root tau p g a,
        bankFixedReferenceGap N n root tau p g F a l) := by
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro l _
  exact actual_bank_fixed_upper N n root tau p g a l F
    hN ht ht' hn hp hband hcells

/-- Actual one-generation read/selected-child inequality after paying
the old-cell FIXED part via a closed-cell induction hypothesis. This is
not an original arithmetic count licence: base, per-product feedback,
strict physical prime child terms and the external prime-row error are
still present with their original signs and constants. -/
theorem actual_one_generation_fixed_upper (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    levelReadMass N n root tau p g - levelChildMass N n root tau p g ≤
      buchstabLevelError N n root tau p g +
      (∑ a : Original106Action,
        ∑ l ∈ selectedLevel N n root tau p g a,
          bankFixedReferenceGap N n root tau p g F a l) := by
  have hstep := actual_one_generation_without_trim N n
    root tau p g hN ht ht' hn hp hband
  have hfixed := bank_fixed_sum_upper N n
    root tau p g F hN ht ht' hn hp hband hcells
  linarith only [hstep, hfixed]

/-- Uniform threshold is chosen BEFORE the generation, history, action,
old-cell predecessor bound F and root data. No new analytic interface:
only the already fixed-version uniform Buchstab supplier is invoked. -/
theorem uniform_actual_one_generation_fixed_upper
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → ∀ n : ℕ, ∀ root : Root,
      ∀ tau : ℝ, 0 ≤ tau → tau ≤ 1/12 →
        1/((n:ℝ)+1) ≤ 11/384 →
      ∀ p : ℕ, (p.Prime ∧ p.Coprime N) →
        physicalPrime N p ∈ rootBand root →
      ∀ g : Fin 430, ∀ F : ℝ → ℝ,
        (∀ (i : Fin 200) (s : ℝ),
          s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) →
        levelReadMass N n root tau p g -
            levelChildMass N n root tau p g ≤
          epsilon * buchstabLevelTheta N n root tau p g +
          (∑ a : Original106Action,
            ∑ l ∈ selectedLevel N n root tau p g a,
              bankFixedReferenceGap N n root tau p g F a l) := by
  obtain ⟨T, hT, hstep⟩ :=
    uniform_actual_one_generation_without_trim he
  refine ⟨T, hT, ?_⟩
  intro N hN n root tau ht ht' hn p hp hband g F hcells
  have h := hstep N hN n root tau ht ht' hn p hp hband g
  have hf := bank_fixed_sum_upper N n root tau p g F
    (hT.trans hN) ht ht' hn hp hband hcells
  linarith only [h, hf]

end
end ImbalancedChen.Part5OriginalH430ActualFixedClosedCell
