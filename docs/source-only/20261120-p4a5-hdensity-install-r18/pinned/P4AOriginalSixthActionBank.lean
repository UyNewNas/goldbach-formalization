import ImbalancedChen.P4AOriginalSixthQuantizedActionLicense
import ImbalancedChen.P4AOriginalCompleteSixthAffinePrograms
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
SOURCE ONLY / UNCOMPILED / NO KERNEL CREDIT.

One finite tagged bank, retaining the ORIGINAL saved, eleven and nineteen
later actions. `GeometricSource` is a measurable SUPERSET of actual eligible
actions on the below-mu original87 slice. It is used only to choose a common
square-margin stratum; it NEVER replaces an actual producer guard.

No row is accepted merely because its index occurs in the archived bank.
All actual later guards read the unrounded predecessor at their OWN stage.
-/
namespace ImbalancedChen.P4AOriginalSixthActionBank
noncomputable section
open scoped Classical BigOperators
open Set MeasureTheory VariableEnvelope
open P1QuantizedActionLicense P4AOriginalSixthSquareRows
open P1FiniteAffineDecisionProgram
open P4AOriginalFourthFifthAffinePrograms
open P4AOriginalCompleteSixthAffinePrograms
open P4AOriginalSixthQuantizedActionLicense
open P4AOriginalCompleteSixthChronology P5OriginalCommonRefinedConstructor

abbrev Point6 := Fin 6 → ℝ

inductive Action where
  | saved (i : P4AOriginalSavedSixthArchive.Row)
  | eleven (c : Certificates.P2OriginalSixthElevenLogSemantics.Cell)
  | later (c : P4AOriginalSixthLaterLiteral.Cell)
  deriving DecidableEq

/-- The eleven-cell type need not have a separately installed Fintype
instance: its original complete list is the finite supplier. -/
def allActions : Finset Action :=
  (Finset.univ.image Action.saved) ∪
  (Certificates.P2OriginalSixthElevenLogSemantics.allCells.toFinset.image Action.eleven) ∪
  (Finset.univ.image Action.later)

theorem mem_allActions (a : Action) : a ∈ allActions := by
  cases a with
  | saved i => simp [allActions]
  | eleven c =>
      have hc := Certificates.P2OriginalSixthElevenLogSemantics.allCells_complete c
      simp [allActions, hc]
  | later c => simp [allActions]

/-- An explicitly finite index retaining every original action exactly
as a tagged value. No occurrence list is quotiented by this action index. -/
abbrev Entry := {a : Action // a ∈ allActions}

def selected : Action → Finset (Fin 6)
  | .saved i => slots (P4AOriginalSavedSixthArchive.selectedMask i)
  | .eleven c => slots c.selectedMask
  | .later c => slots (P4AOriginalSixthLaterLiteral.mask c)

def endpoint : Action → Point6 → ℝ
  | .saved i => P4AOriginalSavedSixthArchive.endpoint i
  | .eleven c => Certificates.P2OriginalSixthElevenLogSemantics.newCap c
  | .later c => P4AOriginalSixthLaterSemantics.endpoint c

/-- Actual original source geometry. The saved half-floor range is
recorded separately and will be derived from the original87 ancestor. -/
def GeometricSource : Action → Point6 → Prop
  | .saved i, t => P4AOriginalSavedSixthArchive.Source i t ∧ t 2 ≤ mu
  | .eleven c, t => Certificates.P2OriginalSixthElevenLogSemantics.PhysicalCell c t
  | .later c, t => P4AOriginalSixthLaterSemantics.Source c t ∧
      P4AOriginalSixthLaterSemantics.comparison c t <
        P4AOriginalSixthLaterSemantics.endpoint c t

/-- Exact finite comparisons used to establish measurability; no arbitrary
point-dependent predicate is inserted into the comparison language. -/
def geometryTests : Action → List (P1FiniteAffineDecisionProgram.Gate 6)
  | .saved i => savedSourceTests i ++ [LE (atom (X 2)) (atom (K mu))]
  | .eleven c => elevenSourceTests c
  | .later c => laterSourceTests c ++
      [LT (atom (laterComparisonA c)) (atom (laterEndpointA c))]

theorem geometryTests_exact (a : Action) (t : Point6) :
    Passed t (geometryTests a) ↔ GeometricSource a t := by
  cases a with
  | saved i =>
      simp only [geometryTests, passed_append, savedSourceTests_exact,
        passed_cons, passed_nil, holds_LE, Program.eval,
        Affine.eval_coord, Affine.eval_const, and_true, GeometricSource]
  | eleven c => exact elevenSourceTests_exact c t
  | later c =>
      simp only [geometryTests, passed_append, laterSourceTests_exact,
        passed_cons, passed_nil, holds_LT, Program.eval,
        laterComparisonA_exact, laterEndpointA_exact, and_true, GeometricSource]

theorem program_measurable {k : ℕ} (p : Program k) :
    Measurable (fun t : Fin k → ℝ => p.eval t) := by
  induction p with
  | leaf a =>
      have h : Continuous (fun t : Fin k → ℝ => a.eval t) := by
        unfold Affine.eval
        fun_prop
      exact h.measurable
  | sup a b ha hb => exact ha.max hb
  | inf a b ha hb => exact ha.min hb
  | lt a b yes no ha hb hy hn => exact Measurable.ite (measurableSet_lt ha hb) hy hn
  | le a b yes no ha hb hy hn => exact Measurable.ite (measurableSet_le ha hb) hy hn

theorem passed_measurable {k : ℕ} (gs : List (P1FiniteAffineDecisionProgram.Gate k)) :
    MeasurableSet {t : Fin k → ℝ | Passed t gs} := by
  induction gs with
  | nil => simpa only [passed_nil, setOf_true] using MeasurableSet.univ
  | cons g gs ih =>
      have hg : MeasurableSet {t : Fin k → ℝ | g.holds t} := by
        cases h : g.strict with
        | false =>
            simpa only [P1FiniteAffineDecisionProgram.Gate.holds, h,
              Bool.false_eq_true, if_false] using
              measurableSet_le (program_measurable g.lhs) (program_measurable g.rhs)
        | true =>
            simpa only [P1FiniteAffineDecisionProgram.Gate.holds, h, if_true] using
              measurableSet_lt (program_measurable g.lhs) (program_measurable g.rhs)
      simpa only [passed_cons, setOf_and] using hg.inter ih

theorem geometricSource_measurable (a : Action) :
    MeasurableSet {t | GeometricSource a t} := by
  simpa only [geometryTests_exact] using passed_measurable (geometryTests a)

theorem endpoint_continuous (a : Action) : Continuous (endpoint a) := by
  cases a with
  | saved i =>
      change Continuous (P4AOriginalSavedSixthArchive.endpoint i)
      unfold P4AOriginalSavedSixthArchive.endpoint VariableEnvelope.v
        VariableEnvelope.A VariableEnvelope.C
        Certificates.P2OriginalSixthElevenLogSemantics.selectedSum
      fun_prop
  | eleven c =>
      have h : Continuous (fun t : Point6 => (elevenNewA c).eval t) := by
        unfold Affine.eval
        fun_prop
      simpa only [elevenNewA_exact] using h
  | later c =>
      have h : Continuous (fun t : Point6 => (laterEndpointA c).eval t) := by
        unfold Affine.eval
        fun_prop
      simpa only [laterEndpointA_exact] using h

theorem gate_continuous (a : Action) (g : P1QuantizedActionLicense.Gate 6) :
    Continuous (fun t : Point6 => P1QuantizedActionLicense.gate (selected a) t g) := by
  cases g with
  | none => exact continuous_const
  | some bg =>
      rcases bg with ⟨b,j⟩
      cases b with
      | false => exact continuous_prefixSquareExpr j
      | true =>
          by_cases hj : j ∈ selected a
          · simpa only [P1QuantizedActionLicense.gate, if_pos hj] using
              (continuous_const : Continuous (fun _ : Point6 => (1 / 2 : ℝ)))
          · simpa only [P1QuantizedActionLicense.gate, if_neg hj] using
              continuous_selectedSquareExpr (selected a) j

/-- Every gate margin is PROVED positive on this explicit geometric
supercover. It is not an input uniform-margin or saving licence. -/
theorem geometric_lower_license (a : Action) (t : Point6)
    (h : GeometricSource a t) : LowerLicense (selected a) t (endpoint a t) := by
  cases a with
  | saved i => exact saved_lower_license i t h.1 h.2
  | eleven c => exact eleven_lower_license c t h
  | later c =>
      obtain ⟨hf,hs⟩ := later_source_squares c t h.1
      apply (lowerLicense_iff _ _ _).mpr
      exact ⟨(later_comparison_half c t h.1).trans h.2,hf,hs⟩

theorem geometric_upper_license (a : Action) (t : Point6)
    (h : GeometricSource a t) : endpoint a t ≤ v (∑ j ∈ selected a, t j) := by
  cases a with
  | saved i => rw [selected, sum_slots]; exact le_rfl
  | eleven c =>
      rw [selected, sum_slots, v_eq_min]
      exact (lt_min h.selectedAscending (by
        dsimp only [C]
        linarith [h.selectedDescending])).le
  | later c =>
      rw [selected, sum_slots]
      exact (P4AOriginalSixthLaterSemantics.source_endpoint_lt_selected_tent c t h.1).le

/-- This is the actual guard, NOT the geometric supercover. In the later
case the previous stage remains the raw unrounded chronological current. -/
def ActualEligible (e : ℚ) (q : ℕ) (om N : ℝ) (pre : List ℕ) : Action → Prop
  | .saved i => savedEligible e q om N i pre
  | .eleven c => eligibleSixth (data e q om) N c pre
  | .later c => laterEligible (P4AOriginalSixthLaterLiteral.stage c)
      (afterLater e q om N pre (P4AOriginalSixthLaterLiteral.stage c)) N c pre

theorem actualEligible_geometric (e : ℚ) (q : ℕ) (om N : ℝ)
    (pre : List ℕ) (hthird : primeHistoryLogCoordinates N 6 pre 2 ≤ mu)
    (a : Action) (h : ActualEligible e q om N pre a) :
    GeometricSource a (primeHistoryLogCoordinates N 6 pre) := by
  cases a with
  | saved i => exact ⟨h.2.1,hthird⟩
  | eleven c => exact h.2.1
  | later c => exact ⟨h.2.2.1,h.2.2.2.2.2⟩

end
end ImbalancedChen.P4AOriginalSixthActionBank
