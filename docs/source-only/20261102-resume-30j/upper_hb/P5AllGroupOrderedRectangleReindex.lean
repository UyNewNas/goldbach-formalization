import ImbalancedChen.P5OrderedFactorTupleRectangleReindex
import ImbalancedChen.P5ActualUpperPairHBLogTransport

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
All original groups of the literal numeratorAtlas are reindexed, in order,
by their individual right-closed HB rectangles. No prime caller, physical
coefficient, reciprocal group logarithm, or source cover is supplied anew.
-/
namespace ImbalancedChen.P5Z.AllGroupOrderedRectangleReindex
noncomputable section
open Classical
open scoped BigOperators
open LiteralHeathBrownOccurrenceWords ActualRoughHeathBrownWords
open HBRightClosedDyadicRoles ActualHBDyadicOccurrenceFamily
open ExactOriginalSmoothDyadicPartition PerGroupIntegerHBAtlasPushforward
open OrderedFactorTupleRectangleReindex ActualHBPostModulusLogCutoff
open ImbalancedChen.P5ActualUpperPairHBLogTransport
open ImbalancedChen.Part3.OriginalProperPowerActualChart

/-- The temporary original-coordinate cap remains visible at every group. -/
def cappedEval (cap : ℕ) (chi : ℝ → ℝ) (z : ℝ) :
    List ℕ → (List Row → ℂ) → ℂ
  | [], F => F []
  | cj :: cjs, F =>
      ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
        ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
          ∑ n ∈ (rectangle (blockVector (2*(j+1)) bs)).filter
              (fun n => completeProduct n ≤ cap),
            roughTupleWeight z (hbCutoff cj) (roles j) (List.ofFn n) *
              (psi chi ((completeProduct n : ℝ)/R cj) *
                cappedEval cap chi z cjs (fun rows =>
                  F ({order := j, blocks := bs, factors := List.ofFn n} :: rows)))

/-- Full individual rectangles, with the original smooth group psi retained.
There is no sharp coupled group-product filter in this recursion. -/
def fullEval (chi : ℝ → ℝ) (z : ℝ) : List ℕ → (List Row → ℂ) → ℂ
  | [], F => F []
  | cj :: cjs, F =>
      ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
        ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
          ∑ n ∈ rectangle (blockVector (2*(j+1)) bs),
            roughTupleWeight z (hbCutoff cj) (roles j) (List.ofFn n) *
              (psi chi ((completeProduct n : ℝ)/R cj) *
                fullEval chi z cjs (fun rows =>
                  F ({order := j, blocks := bs, factors := List.ofFn n} :: rows)))

private theorem sum_numerator_cons (chi : ℝ → ℝ) (z : ℝ)
    (cj p : ℕ) (cjs : List ℕ) (S : Finset (List ℕ)) (F : List Row → ℂ) :
    (∑ ns ∈ S, numeratorAtlas chi z (cj :: cjs) (p :: ns) F) =
      psi chi ((p : ℝ)/R cj) *
        ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            ∑ fs ∈ factorTuples (2*(j+1)) p,
              assignedWeight z (hbCutoff cj) (roles j) bs fs *
                ∑ ns ∈ S, numeratorAtlas chi z cjs ns
                  (fun rows => F ({order := j, blocks := bs, factors := fs} :: rows)) := by
  simp only [numeratorAtlas]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bs hbs
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

/-- Every original rank is reindexed by induction on the ACTUAL group list.
The ordered Row list, signed order scalar, repeated blocks and factor slots
are retained; nothing is sorted or divided by a permutation multiplicity. -/
theorem numerator_source_eq_capped (cap : ℕ) (chi : ℝ → ℝ) (z : ℝ) :
    ∀ (cjs : List ℕ) (F : List Row → ℂ),
      (∑ ps ∈ integerWords cap cjs.length, numeratorAtlas chi z cjs ps F) =
        cappedEval cap chi z cjs F := by
  intro cjs
  induction cjs with
  | nil => intro F; simp [integerWords, words, numeratorAtlas, cappedEval]
  | cons cj cjs ih =>
    intro F
    rw [integerWords, List.length_cons, words_sum_cons]
    have hpwise (p : ℕ) :
        (∑ ns ∈ words (Finset.Icc 1 cap) cjs.length,
          numeratorAtlas chi z (cj :: cjs) (p :: ns) F) =
        ∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            ∑ fs ∈ factorTuples (2*(j+1)) p,
              assignedWeight z (hbCutoff cj) (roles j) bs fs *
                (psi chi ((fs.prod : ℝ)/R cj) *
                  cappedEval cap chi z cjs (fun rows =>
                    F ({order := j, blocks := bs, factors := fs} :: rows))) := by
      rw [sum_numerator_cons]
      change psi chi ((p : ℝ)/R cj) *
        (∑ j ∈ Finset.range 3, SmoothChartHBDyadicPartition.scalar j *
          ∑ bs ∈ blockWords (hbCap cj) (2*(j+1)),
            ∑ fs ∈ factorTuples (2*(j+1)) p,
              assignedWeight z (hbCutoff cj) (roles j) bs fs *
                ∑ ns ∈ integerWords cap cjs.length, numeratorAtlas chi z cjs ns
                  (fun rows => F ({order := j, blocks := bs, factors := fs} :: rows))) = _
      simp_rw [ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro bs hbs
      apply Finset.sum_congr rfl
      intro fs hfs
      rw [(factorTuples_spec (2*(j+1)) p fs hfs).2.1]
      ring
    simp_rw [hpwise]
    rw [Finset.sum_comm]
    simp only [cappedEval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bs hbs
    rw [sum_factorTuples_capped cap z (hbCutoff cj) (roles j) bs
      (blockWords_spec _ _ _ hbs).1]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [List.prod_ofFn, completeProduct]

/-- Zero tests remain zero through every finite original-group rectangle. -/
theorem fullEval_zero (chi : ℝ → ℝ) (z : ℝ) :
    ∀ (cjs : List ℕ) (F : List Row → ℂ),
      (∀ rows, F rows = 0) → fullEval chi z cjs F = 0 := by
  intro cjs
  induction cjs with
  | nil => intro F hF; exact hF []
  | cons cj cjs ih =>
    intro F hF
    simp only [fullEval]
    apply Finset.sum_eq_zero
    intro j hj
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro bs hbs
    apply Finset.sum_eq_zero
    intro n hn
    rw [ih _ (fun rows => hF (_ :: rows)), mul_zero, mul_zero]

/-- This support assertion removes only a temporary enumeration cap.
It is proved for the actual upper test in the concrete consumer module;
it is neither a Family cover nor an arithmetic estimate. -/
def CapSupported (cap : ℕ) (F : List Row → ℂ) : Prop :=
  ∀ rows r, r ∈ rows → cap < r.factors.prod → F rows = 0

theorem cappedEval_eq_fullEval (cap : ℕ) (chi : ℝ → ℝ) (z : ℝ) :
    ∀ (cjs : List ℕ) (F : List Row → ℂ), CapSupported cap F →
      cappedEval cap chi z cjs F = fullEval chi z cjs F := by
  intro cjs
  induction cjs with
  | nil => intro F hF; rfl
  | cons cj cjs ih =>
    intro F hF
    simp only [cappedEval, fullEval]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    apply Finset.sum_congr rfl
    intro bs hbs
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    let row : Row := {order := j, blocks := bs, factors := List.ofFn n}
    have htail : CapSupported cap (fun rows => F (row :: rows)) := by
      intro rows r hr hlarge
      exact hF (row :: rows) r (List.mem_cons_of_mem row hr) hlarge
    by_cases hc : completeProduct n ≤ cap
    · simp only [if_pos hc]
      rw [ih _ htail]
    · have hlarge : cap < row.factors.prod := by
        simpa only [row, List.prod_ofFn, completeProduct] using lt_of_not_ge hc
      have hz : fullEval chi z cjs (fun rows => F (row :: rows)) = 0 :=
        fullEval_zero chi z cjs _ (fun rows => hF _ row (by simp) hlarge)
      change (if completeProduct n ≤ cap then _ else 0) = _
      simp only [if_neg hc]
      change 0 = roughTupleWeight z (hbCutoff cj) (roles j) (List.ofFn n) *
        (psi chi ((completeProduct n : ℝ)/R cj) *
          fullEval chi z cjs (fun rows => F (row :: rows)))
      rw [hz, mul_zero, mul_zero]

/-- Literal all-rank source-to-full-occurrence identity. At the concrete
upper caller CapSupported is DERIVED from its existing smooth support. -/
theorem numerator_source_eq_full_rectangles (cap : ℕ) (chi : ℝ → ℝ) (z : ℝ)
    (cjs : List ℕ) (F : List Row → ℂ) (hF : CapSupported cap F) :
    (∑ ps ∈ integerWords cap cjs.length, numeratorAtlas chi z cjs ps F) =
      fullEval chi z cjs F := by
  rw [numerator_source_eq_capped, cappedEval_eq_fullEval cap chi z cjs F hF]

/-- The raw atlas reaches the same rectangles with exactly the product
of ORIGINAL group logs in its test. Totalized zero/unit logs are included;
no division by an individual HB occurrence log is introduced. -/
theorem atlas_source_eq_full_rectangles (cap : ℕ) (chi : ℝ → ℝ) (z : ℝ)
    (cjs : List ℕ) (F : List Row → ℂ) (hF : CapSupported cap F) :
    (∑ ps ∈ integerWords cap cjs.length, atlasEval chi z cjs ps F) =
      fullEval chi z cjs (fun rows => F rows / (wordLog (originalProducts rows) : ℂ)) := by
  have hnorm : CapSupported cap
      (fun rows => F rows / (wordLog (originalProducts rows) : ℂ)) := by
    intro rows r hr hlarge
    rw [hF rows r hr hlarge, zero_div]
  calc
    _ = ∑ ps ∈ integerWords cap cjs.length, numeratorAtlas chi z cjs ps
        (fun rows => F rows / (wordLog (originalProducts rows) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro ps hps
      rw [actual_atlas_denominators]
      symm
      calc
        _ = numeratorAtlas chi z cjs ps
            (fun rows => F rows / (wordLog ps : ℂ)) := by
          apply numeratorAtlas_congr_on_originalProducts
          intro rows hrows
          rw [hrows]
        _ = _ := numeratorAtlas_div_const chi z cjs ps F (wordLog ps : ℂ)
    _ = _ := numerator_source_eq_full_rectangles cap chi z cjs _ hnorm
end
end ImbalancedChen.P5Z.AllGroupOrderedRectangleReindex