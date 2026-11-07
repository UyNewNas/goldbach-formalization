import ImbalancedChen.Part5OriginalH430ActualFixedClosedCell

/-!
P5.6 / h34. Exact per-PRODUCT integer-division ledger for the ORIGINAL
106-bank feedback numerator. The producer divides every lower/upper
weighted integer product by its original Q80 denominator *before*
summing. It does not divide a combined numerator just once.

This packet retains the actual lower/upper lists, including repeated
terms, the specified-cell FIXED contribution and the outer W1=1 /
W2=5 divisor. The nonnegative remainder is a genuine finite rounding
payment, not an assumed error estimate. It is available even for signed
old table entries. No original U3/U4 selected-count licence, base/seed
inequality, external input or final h34 statement is asserted.

SOURCE ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430ActualFeedbackQuotientRemainders

noncomputable section
open scoped Classical BigOperators
open P5OriginalActionMassBound P5OriginalFeedbackTableKernels
open P2Selected430LiteralActionData (rows)
open Part5OriginalH430BankSlotTargets
open Part5OriginalH430FixedReadDictionary
open Part5OriginalH430ActualReadEdgeDefect
open Part5OriginalH430ActualFixedClosedCell
open Part5OriginalH430RequestedHistory
open Part5OriginalH430RequestedLevelBankSupply
open Part5OriginalH430RequestedMember
open Part5OriginalH430ArithmeticAtomRows
open Part5OriginalH430PhysicalRoots

private abbrev q80 : ℤ := P2Selected430LiteralActionData.q

private theorem q80_pos : (0 : ℤ) < q80 := by
  norm_num [q80, P2Selected430LiteralActionData.q]

/-- An exact LIST of the literal weighted integer products. Repeated
products in the producer remain repeated, and the upper/lower read flags
are not exchanged. -/
def literalFeedbackProducts (old : Table) (a : Original106Action) : List ℤ :=
  ((rows (slotOfAction a)).lowerWeights.map
    (fun w => read old false w.1 * w.2)) ++
  ((rows (slotOfAction a)).upperWeights.map
    (fun w => read old true w.1 * w.2))

/-- Numerator with only the per-product divisions removed. This is NOT
the numerator obtained by dividing a sum and then taking one floor. -/
def unroundedNumerator (old : Table) (a : Original106Action) : ℤ :=
  (literalFeedbackProducts old a).sum

/-- Sum of actual nonnegative Euclidean remainders at the original Q80
division sites. This preserves the number of payment events. -/
def remainderNumerator (old : Table) (a : Original106Action) : ℤ :=
  ((literalFeedbackProducts old a).map (fun z => z % q80)).sum

private theorem literal_quotient_sum (old : Table) (a : Original106Action) :
    ((literalFeedbackProducts old a).map (fun z => z / q80)).sum =
      feedbackNumerator old a := by
  simp [literalFeedbackProducts, feedbackNumerator, q80,
    List.map_append, List.map_map, List.sum_append, Function.comp_def]

/-- Euclidean division, summed over actual list positions. No positivity
premise, and hence no restriction on the sign of an old table entry. -/
private theorem sum_quotient_remainder (xs : List ℤ) (d : ℤ) :
    xs.sum =
      d * (xs.map (fun z => z / d)).sum +
        (xs.map (fun z => z % d)).sum := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
      simp only [List.sum_cons, List.map_cons]
      calc
        z + zs.sum = (z % d + d * (z / d)) + zs.sum := by
          rw [Int.emod_add_ediv]
        _ = d * (z / d + (zs.map (fun w => w / d)).sum) +
              (z % d + (zs.map (fun w => w % d)).sum) := by
          rw [ih]
          ring

/-- Exact finite ledger. Unlike an arbitrary rounding budget, the
right-hand remainder is literally the source producer's per-product
integer remainder, before the unchanged outer W1/W2 divisor. -/
theorem exact_feedback_integer_ledger (old : Table) (a : Original106Action) :
    unroundedNumerator old a =
      q80 * feedbackNumerator old a + remainderNumerator old a := by
  unfold unroundedNumerator remainderNumerator
  rw [← literal_quotient_sum old a]
  exact sum_quotient_remainder (literalFeedbackProducts old a) q80

private theorem list_remainders_nonneg (xs : List ℤ) (d : ℤ) (hd : 0 < d) :
    0 ≤ (xs.map (fun z => z % d)).sum := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (Int.emod_nonneg z hd.ne') ih

private theorem list_remainders_le_length (xs : List ℤ) (d : ℤ)
    (hd : 0 < d) :
    (xs.map (fun z => z % d)).sum ≤ (xs.length : ℤ) * d := by
  induction xs with
  | nil => simp
  | cons z zs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
      calc
        z % d + (zs.map (fun w => w % d)).sum ≤
            d + (zs.length : ℤ) * d :=
          add_le_add (le_of_lt (Int.emod_lt_of_pos z hd)) ih
        _ = ((zs.length : ℤ) + 1) * d := by ring

/-- The actual producer has a NONNEGATIVE exact payment, regardless of
the signs in the old table. -/
theorem remainderNumerator_nonneg (old : Table) (a : Original106Action) :
    0 ≤ remainderNumerator old a := by
  unfold remainderNumerator
  exact list_remainders_nonneg _ _ q80_pos

/-- At most one Q80 integer unit per original weighted product;
the bound uses LIST LENGTH, not cardinality of distinct products. -/
theorem remainderNumerator_le_length (old : Table) (a : Original106Action) :
    remainderNumerator old a ≤
      ((literalFeedbackProducts old a).length : ℤ) * q80 := by
  unfold remainderNumerator
  exact list_remainders_le_length _ _ q80_pos

/-- The exact real linearized sum of the ORIGINAL weighted products.
The integer producer is below this value, with its full W1/W2 divisor. -/
def idealFeedbackValue (old : Table) (a : Original106Action) : ℝ :=
  (unroundedNumerator old a : ℝ) / (q80 : ℝ) /
    ((rows (slotOfAction a)).divisor : ℝ) / (2^80 : ℝ)

/-- Actual feedback rounding cost, still charged after BOTH the
per-product q80 division and the action's one outer divisor. -/
def feedbackRoundingLoss (old : Table) (a : Original106Action) : ℝ :=
  (remainderNumerator old a : ℝ) / (q80 : ℝ) /
    ((rows (slotOfAction a)).divisor : ℝ) / (2^80 : ℝ)

/-- This equation keeps the exact producer feedback on the right,
rather than silently treating integer division as a real equality. -/
theorem ideal_feedback_exact (old : Table) (a : Original106Action) :
    idealFeedbackValue old a =
      feedbackValue old a + feedbackRoundingLoss old a := by
  have heq : (unroundedNumerator old a : ℝ) =
      (q80 : ℝ) * (feedbackNumerator old a : ℝ) +
        (remainderNumerator old a : ℝ) := by
    exact_mod_cast exact_feedback_integer_ledger old a
  have hq : (q80 : ℝ) ≠ 0 := by
    exact_mod_cast q80_pos.ne'
  have hd : (((rows (slotOfAction a)).divisor : ℝ)) ≠ 0 := by
    exact_mod_cast (literal_divisor_pos a).ne'
  unfold idealFeedbackValue feedbackValue feedbackRoundingLoss
  rw [heq]
  field_simp [hq, hd]
  ring

theorem feedbackRoundingLoss_nonneg (old : Table) (a : Original106Action) :
    0 ≤ feedbackRoundingLoss old a := by
  have hq : (0 : ℝ) ≤ (q80 : ℝ) := by
    exact_mod_cast q80_pos.le
  have hd : (0 : ℝ) ≤ ((rows (slotOfAction a)).divisor : ℝ) := by
    exact_mod_cast (literal_divisor_pos a).le
  unfold feedbackRoundingLoss
  exact div_nonneg (div_nonneg
    (div_nonneg (by exact_mod_cast remainderNumerator_nonneg old a) hq) hd)
    (by positivity)

/-- Real numerical payment: at most one decoded Q80 unit for each
literal weighted-product occurrence, including repetitions. -/
theorem feedbackRoundingLoss_le_length (old : Table) (a : Original106Action) :
    feedbackRoundingLoss old a ≤
      ((literalFeedbackProducts old a).length : ℝ) /
        ((rows (slotOfAction a)).divisor : ℝ) / (2^80 : ℝ) := by
  have hr : (remainderNumerator old a : ℝ) ≤
      ((literalFeedbackProducts old a).length : ℝ) * (q80 : ℝ) := by
    exact_mod_cast remainderNumerator_le_length old a
  have hq : (0 : ℝ) < (q80 : ℝ) := by exact_mod_cast q80_pos
  have hd : (0 : ℝ) <
      ((rows (slotOfAction a)).divisor : ℝ) := by
    exact_mod_cast literal_divisor_pos a
  unfold feedbackRoundingLoss
  calc
    _ ≤ (((literalFeedbackProducts old a).length : ℝ) * (q80 : ℝ)) /
          (q80 : ℝ) / ((rows (slotOfAction a)).divisor : ℝ) /
            (2^80 : ℝ) := by
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hr hq.le) hd.le) (by positivity)
    _ = _ := by
      field_simp [hq.ne', hd.ne']
      ring

/-- Idealized real feedback appears with its exact, nonnegative
INTEGER correction at every genuine bank occurrence. This is an
identity, not a new presumed arithmetic-count or integral bound. -/
def bankIdealFeedbackGap (N n : ℕ) (root : Root) (tau : ℝ)
    (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (a : Original106Action) (l : Index N n root tau p g) : ℝ :=
  levelMark l *
    (thetaAtom N (rootQ N n root tau p)
        (parentProduct (levelOccurrence l).current.old) *
       (baseValue a + fixedReference F a +
          idealFeedbackValue (iterate g.val) a) -
     childTerm N n root tau p g l)

theorem bank_ideal_feedback_exact (N n : ℕ) (root : Root)
    (tau : ℝ) (p : ℕ) (g : Fin 430) (F : ℝ → ℝ)
    (a : Original106Action) (l : Index N n root tau p g) :
    bankIdealFeedbackGap N n root tau p g F a l =
      bankFixedReferenceGap N n root tau p g F a l +
      levelMark l *
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
        feedbackRoundingLoss (iterate g.val) a := by
  have h := ideal_feedback_exact (iterate g.val) a
  unfold bankIdealFeedbackGap bankFixedReferenceGap
  rw [h]
  ring

/-- Preserve the original FIXED closed-cell condition while exposing
the precise real-feedback-to-integer correction. This is stronger
bookkeeping than dropping all per-product floor remainders. -/
theorem actual_bank_corrected_feedback_upper (N n : ℕ)
    (root : Root) (tau : ℝ) (p : ℕ) (g : Fin 430)
    (a : Original106Action) (l : Index N n root tau p g)
    (F : ℝ → ℝ)
    (hN : 4 ≤ N) (ht : 0 ≤ tau) (ht' : tau ≤ 1/12)
    (hn : 1/((n:ℝ)+1) ≤ 11/384)
    (hp : p.Prime ∧ p.Coprime N)
    (hband : physicalPrime N p ∈ rootBand root)
    (hcells : ∀ (i : Fin 200) (s : ℝ),
      s ∈ queryCell i → floorValue (iterate g.val true) i ≤ F s) :
    bankCandidateGap N n root tau p g a l ≤
      bankIdealFeedbackGap N n root tau p g F a l -
      levelMark l *
        thetaAtom N (rootQ N n root tau p)
          (parentProduct (levelOccurrence l).current.old) *
        feedbackRoundingLoss (iterate g.val) a := by
  have hf := actual_bank_fixed_upper N n root tau p g a l F
    hN ht ht' hn hp hband hcells
  have he := bank_ideal_feedback_exact N n root tau p g F a l
  linarith only [hf, he]

end
end ImbalancedChen.Part5OriginalH430ActualFeedbackQuotientRemainders
