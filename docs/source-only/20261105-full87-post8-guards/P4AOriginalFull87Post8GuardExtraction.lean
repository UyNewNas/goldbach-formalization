import ImbalancedChen.P4AOriginalFull87Post8SuffixExit
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import ImbalancedChen.OrdinaryRosserFirstExitPolicy
import MathlibNt.SieveTheory.LiLiuPrereqWFSmallRosser
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNCOMPILED / UNEVALUATED / ZERO FORMAL CREDIT.

P1.4: extract the ACTUAL post-eight upper Rosser decisions, not an
independently chosen square-test predicate. The original history was
admitted at historical levels, so it is not required to satisfy the
whole ordinary full-prefix predicate at the newly frozen level.

The successful odd selections of a literal ordinary continuation DO
pass the complete frozen-level test, including every inherited square.
An odd rejection has a precise disjunction: total-product failure or
some full-prefix odd square failure. That square may belong to the
inherited history, not necessarily to the newly proposed prime.
Consequently the previous post-eight hprior can be addressed from
actual retained decisions, while its hEXIT still needs a separate
last-prime/total-cutoff analysis. No inference from cap monotonicity.
-/

namespace ImbalancedChen.P4AOriginalFull87Post8GuardExtraction
noncomputable section
open scoped Classical BigOperators
open MathlibNt.SieveTheory
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87OwnedEighthSource (frontier frontier_sign_mass states_eq_owner_filter)
open P4AOriginalFull87LicensedSixthRealization (states)

/-- Upper ordinary policy at an odd selected prefix is exactly the
literal full-prefix test; neither the product nor an inherited square
condition is dropped. -/
theorem upper_odd_test_iff (R : ℝ) (pre : List ℕ) :
    ordinaryParityRosserPolicy false R false pre = true ↔
      (pre.prod : ℝ) < R ∧
      LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R pre.toFinset := by
  simp [ordinaryParityRosserPolicy, oddFirstExitPolicy,
    ordinaryRosserPrefixAdmissible]

/-- A rejected odd selection may be caused by the full-product cutoff
rather than by a last-prime square. -/
theorem upper_odd_rejected_iff (R : ℝ) (pre : List ℕ) :
    ordinaryParityRosserPolicy false R false pre = false ↔
      R ≤ (pre.prod : ℝ) ∨
      ¬ LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet R pre.toFinset := by
  simp [ordinaryParityRosserPolicy, oddFirstExitPolicy,
    ordinaryRosserPrefixAdmissible, not_and_or, not_lt]

/-- If the total product is still below the frozen level, a rejected
odd prefix has a genuine failed odd square SOMEWHERE on that full
prefix. This does not assume the failing square is its last prime. -/
theorem upper_odd_rejected_square_witness (R : ℝ) (pre : List ℕ)
    (hproduct : (pre.prod : ℝ) < R)
    (hrejected : ordinaryParityRosserPolicy false R false pre = false) :
    ∃ p ∈ pre.toFinset,
      ¬ Even ((pre.toFinset.filter (fun q => p ≤ q)).card) ∧
      R ≤ (((pre.toFinset.filter (fun q => p ≤ q)).prod id : ℕ) : ℝ) *
        (p : ℝ) ^ 2 := by
  have hcase := (upper_odd_rejected_iff R pre).mp hrejected
  rcases hcase with hfail | hbad
  · exact (not_le_of_gt hproduct hfail).elim
  · unfold LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet at hbad
    push_neg at hbad
    exact hbad

/-- The literal ordered list of post-eight ODD selections. The prefix
is reversed relative to processing order, exactly as in the original
first-exit tree. This list contains no historical admission decisions. -/
def post8OddTrace (history : List ℕ) (positive : Bool) :
    List ℕ → List (List ℕ)
  | [] => []
  | p :: ps =>
      (if positive then [p :: history] else []) ++
        post8OddTrace (p :: history) (!positive) ps

/-- An actual valid continuation certifies every odd selection recorded
in its own trace at ONE frozen level. The proof unfolds the SAME
FirstExitValidSelection used by the physical retained-leaf enumeration;
it does not demand old ranks 1/3/5/7 to be re-admitted at this level. -/
theorem valid_upper_odd_trace (R : ℝ) :
    ∀ (history : List ℕ) (positive : Bool) (chosen : List ℕ),
      FirstExitValidSelection (ordinaryParityRosserPolicy false R)
        history positive chosen →
      ∀ pre ∈ post8OddTrace history positive chosen,
        ordinaryParityRosserPolicy false R false pre = true := by
  intro history positive chosen
  induction chosen generalizing history positive with
  | nil =>
      intro _ pre hmem
      simp [post8OddTrace] at hmem
  | cons p ps ih =>
      intro hvalid pre hmem
      change ordinaryParityRosserPolicy false R (!positive) (p :: history) = true ∧
        FirstExitValidSelection (ordinaryParityRosserPolicy false R)
          (p :: history) (!positive) ps at hvalid
      obtain ⟨hhead, htail⟩ := hvalid
      change pre ∈ (if positive then [p :: history] else []) ++
        post8OddTrace (p :: history) (!positive) ps at hmem
      rcases List.mem_append.mp hmem with hnow | hlater
      · cases positive with
        | false => simp at hnow
        | true =>
            simp only [ite_true, List.mem_singleton] at hnow
            subst pre
            simpa using hhead
      · exact ih (p :: history) (!positive) htail pre hlater

/-- Abbreviation for the TWO ACTUAL levels on an owned original87 state.
The parent is the licensed sixth ancestor; the other level is the
original rounded eighth cap. This is not a caller-selected level. -/
def actualFrozenPost8Level (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ)
    (useParent : Bool) : ℝ :=
  (N : ℝ) ^
    (if useParent then actualParent n e q om (N : ℝ) s.selectedPrefix
     else (finiteCap n c (point8 (N : ℝ) s.selectedPrefix) : ℝ))

/-- On the literal 87-domain occurrence list, an ACTUAL terminal leaf
of either ordinary continuation admits an ordered selected sublist
and complete frozen-level tests for all its post-eight selected odd
prefixes. Signs, remaining carrier, prefix order and occurrence
multiplicity are not altered by the extraction. -/
theorem owned87_terminal_post8_success_guards
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hs : s ∈ states delta n e q om N cap w z (fun _ => 1) c)
    (useParent : Bool) (leaf : FirstExitLeaf ℕ)
    (hleaf : leaf ∈ firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false
        (actualFrozenPost8Level n e q om N c s useParent))
      (fun _ : ℕ => 1) s.selectedPrefix s.positive s.mass s.remaining) :
    ∃ chosen : List ℕ,
      chosen <+ s.remaining ∧
      leaf.selected = chosen.reverse ++ s.selectedPrefix ∧
      ∀ pre ∈ post8OddTrace s.selectedPrefix true chosen,
        (pre.prod : ℝ) < actualFrozenPost8Level n e q om N c s useParent ∧
        LiLiuPrereqWF.SmallRosser.UpperAdmissibleSet
          (actualFrozenPost8Level n e q om N c s useParent) pre.toFinset := by
  let R := actualFrozenPost8Level n e q om N c s useParent
  have hfront : s ∈ frontier n e q om N cap w z := by
    have hsrc := hs
    rw [states_eq_owner_filter] at hsrc
    exact (List.mem_filter.mp hsrc).1
  have hpositive := (frontier_sign_mass n e q om N cap w z s hfront).1
  obtain ⟨chosen, hsub, hvalid, hselected⟩ :=
    exists_validSelection_of_mem_firstExitRetainedLeaves
      (ordinaryParityRosserPolicy false R) (fun _ : ℕ => 1)
      s.selectedPrefix s.remaining s.positive s.mass leaf hleaf
  have hvalidTrue : FirstExitValidSelection (ordinaryParityRosserPolicy false R)
      s.selectedPrefix true chosen := by
    simpa only [hpositive] using hvalid
  have htrace := valid_upper_odd_trace R
    s.selectedPrefix true chosen hvalidTrue
  refine ⟨chosen, hsub, hselected, ?_⟩
  intro pre hmem
  exact (upper_odd_test_iff R pre).mp (htrace pre hmem)

end
end ImbalancedChen.P4AOriginalFull87Post8GuardExtraction
