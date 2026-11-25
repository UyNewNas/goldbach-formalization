import ImbalancedChen.Part5OriginalH430TrueUpperU34Phase
import ImbalancedChen.Part5OriginalH430UpperOverlapPhysicalSlot

/-!
P5.6 h34: evaluate the actual H430 upper analytic coefficient on the
original U3/U4 tagged (p,q) arithmetic receivers, preserving each q.
The U4 overlap uses equal true main-envelope H430 lookups; the two
distinct tags consequently contribute twice to a source-indexed lookup.

This is NOT a count-to-integral theorem, full/selected/inherited
owner, signed Euler payment, or proof of the complete h34.
SOURCE_ONLY / UNCOMPILED / UNEVALUATED.
-/

namespace ImbalancedChen.Part5OriginalH430OriginalU34AnalyticLookup
noncomputable section
open Set
open scoped Classical BigOperators
open Part5OriginalUpsilon5CausalDictionary (a)
open Part5UpperTables
open Part5UpperTables.OriginalU34
open Part5OriginalH430TaggedArithmeticReceivers
open Part5OriginalH430OriginalUpperOverlapCount
open Part5OriginalH430UpperOverlapPhysicalSlot
open Part5OriginalH430TrueUpperU34Phase

/-- An ANALYTIC LOOKUP assigned to each original tagged arithmetic
receiver. It is not its original integer count weight. -/
def actualTaggedUpperH430Lookup (N : ℕ) : TaggedReceiver → ℝ :=
  Sum.elim
    (fun x => U3H430Coefficient (primeCoordinate N x.1))
    (fun x => U4H430Coefficient (primeCoordinate N x.1))

/-- The original selected U4 (p,q) gives an ACTUAL prime coordinate
in the strict U4 H430 main band. -/
theorem original_u4_pair_upper_coordinate
    (N : ℕ) (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    primeCoordinate N x.1 ∈ Ico a (59 / 250 : ℝ) := by
  have hp : x.1 ∈ originalBand N .U4 :=
    (Finset.mem_sigma.mp hx).1
  exact primeCoordinate_mem hN
    (by simpa only [originalBand] using hp)

/-- No H248 lookup, lower h-start or tail clamp enters the U4 source:
the two ORIGINAL upper tags have identical H430 lookup. -/
theorem original_u4_pair_true_upper_H430_equal
    (N : ℕ) (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    U3H430Coefficient (primeCoordinate N x.1) =
      U4H430Coefficient (primeCoordinate N x.1) := by
  exact U3_eq_main_on_U4
    (original_u4_pair_upper_coordinate N hN x hx)

/-- The explicit common formula has the literal un-clamped argument
mainResidual/a and the fixed 430 numerators, for real original p. -/
theorem original_u4_pair_both_true_H430_formula
    (N : ℕ) (hN : 2 ≤ N) (x : TaggedPair)
    (hx : x ∈ originalPairs N .U4) :
    let t := primeCoordinate N x.1
    U3H430Coefficient t =
        (upperAmplitude (mainResidual t / a) -
          upperRoot H430Numerators (mainResidual t / a)) *
            branchWeight mainResidual t ∧
    U4H430Coefficient t =
        (upperAmplitude (mainResidual t / a) -
          upperRoot H430Numerators (mainResidual t / a)) *
            branchWeight mainResidual t := by
  dsimp
  have h4 := u4_entire_phase_true_H430
    (original_u4_pair_upper_coordinate N hN x hx)
  exact ⟨(original_u4_pair_true_upper_H430_equal
    N hN x hx).trans h4, h4⟩

/-- A finite sum over EVERY original (p,q,tag), not an integral:
U3-only receipts plus TWO U4 copies with the true analytic H430
value. No unique historical Fin event is counted twice. -/
theorem original_U34_actual_H430_source_lookup_split
    (N : ℕ) (hN : 2 ≤ N) :
    (∑ z ∈ originalTagged N, actualTaggedUpperH430Lookup N z) =
      (∑ x ∈ upperExclusivePairs N,
        U3H430Coefficient (primeCoordinate N x.1)) +
      2 * (∑ x ∈ originalPairs N .U4,
        U4H430Coefficient (primeCoordinate N x.1)) := by
  have hleft :
      (∑ z ∈ originalTagged N, actualTaggedUpperH430Lookup N z) =
        (∑ x ∈ upperExclusivePairs N,
          U3H430Coefficient (primeCoordinate N x.1)) +
        (∑ x ∈ originalPairs N .U4,
          (U3H430Coefficient (primeCoordinate N x.1) +
            U4H430Coefficient (primeCoordinate N x.1))) := by
    simpa only [actualTaggedUpperH430Lookup] using
      (original_tag_dependent_signed_overlap N (by omega)
        (fun x => U3H430Coefficient (primeCoordinate N x.1))
        (fun x => U4H430Coefficient (primeCoordinate N x.1)))
  have hcommon :
      (∑ x ∈ originalPairs N .U4,
        U3H430Coefficient (primeCoordinate N x.1)) =
      (∑ x ∈ originalPairs N .U4,
        U4H430Coefficient (primeCoordinate N x.1)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact original_u4_pair_true_upper_H430_equal N hN x hx
  have hdouble :
      (∑ x ∈ originalPairs N .U4,
        (U3H430Coefficient (primeCoordinate N x.1) +
          U4H430Coefficient (primeCoordinate N x.1))) =
      2 * (∑ x ∈ originalPairs N .U4,
        U4H430Coefficient (primeCoordinate N x.1)) := by
    rw [Finset.sum_add_distrib, hcommon]
    ring
  rw [hleft, hdouble]

/-- Keep the Chen negative 1/4 for BOTH original analytic upper
labels, yielding negative 1/2 on their common U4 source. This
does not equate any discrete receiver count with an H430 integral. -/
theorem original_U34_actual_H430_source_signed_quarter
    (N : ℕ) (hN : 2 ≤ N) :
    -(1 / 4 : ℝ) *
        (∑ z ∈ originalTagged N, actualTaggedUpperH430Lookup N z) =
      -(1 / 4 : ℝ) *
        (∑ x ∈ upperExclusivePairs N,
          U3H430Coefficient (primeCoordinate N x.1)) -
      (1 / 2 : ℝ) *
        (∑ x ∈ originalPairs N .U4,
          U4H430Coefficient (primeCoordinate N x.1)) := by
  rw [original_U34_actual_H430_source_lookup_split N hN]
  ring

end
end ImbalancedChen.Part5OriginalH430OriginalU34AnalyticLookup
