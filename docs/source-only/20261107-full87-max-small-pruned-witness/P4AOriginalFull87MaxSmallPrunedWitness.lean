import ImbalancedChen.P4AOriginalFull87PrunedTerminalCutoff
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous exact physical-cut decision was applied to EVERY actual small
Rosser support factor.  Since the cutoff is on the NATURAL full modulus
a * terminalProduct, those repeated decisions are equivalent to ONE
decision for the maximum factor in the UNCHANGED actual small support.
This works even for the empty support (its supremum is zero).

A failed maximum-factor test is also transported back to an ACTUAL
small-support factor AND an ORIGINAL retained terminal leaf. This is a
physical high-q witness, not a nonzero signed rho or paid discrepancy.
No rank-eight occurrence, historical policy, terminal enumeration, beta
attachment, or physical cutoff is replaced.
-/

namespace ImbalancedChen.P4AOriginalFull87MaxSmallPrunedWitness
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87RetainedTerminalCeiling
open P4AOriginalFull87PrunedTerminalCutoff
open P4AOriginalFull87OwnedEighthSource (ordinarySaving)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- Maximum of the ORIGINAL actual small Rosser factor support. The
empty support gives zero: no artificial positive factor is inserted. -/
def maxActualSmallFactor (N cap : ℕ) (w : ℝ) : ℕ :=
  (actualSmallRosserSupport N cap w).sup id

/-- Entire finite small-factor inequality reduces to its actual maximum.
The proof retains multiplicity in all subsequent rough terminal sums:
this is merely a decision on a finite support, not a replacement weight. -/
private theorem sup_mul_le_iff_all (S : Finset ℕ) (c X : ℕ) :
    (S.sup id) * c ≤ X ↔ ∀ a ∈ S, a * c ≤ X := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp
  | @insert a S ha ih =>
      have hsup : (insert a S).sup id = max a (S.sup id) := by
        simp [Finset.sup_insert]
      rw [hsup]
      constructor
      · intro h b hb
        rcases Finset.mem_insert.mp hb with rfl | hbS
        · exact (Nat.mul_le_mul_right c
            (le_max_left a (S.sup id))).trans h
        · have hs : (S.sup id) * c ≤ X :=
            (Nat.mul_le_mul_right c
              (le_max_right a (S.sup id))).trans h
          exact (ih.mp hs) b hbS
      · intro h
        have hA : a * c ≤ X := h a (Finset.mem_insert_self a S)
        have hS : ∀ b ∈ S, b * c ≤ X := by
          intro b hb
          exact h b (Finset.mem_insert_of_mem hb)
        rcases le_total a (S.sup id) with hle | hle
        · rw [max_eq_right hle]
          exact ih.mpr hS
        · rw [max_eq_left hle]
          exact hA

/-- A failed maximum support product comes from a genuine member of
the SAME small Rosser support, not an introduced largest divisor. -/
private theorem sup_mul_gt_iff_exists (S : Finset ℕ) (c X : ℕ) :
    X < (S.sup id) * c ↔ ∃ a ∈ S, X < a * c := by
  constructor
  · intro h
    by_contra hn
    have hall : ∀ a ∈ S, a * c ≤ X := by
      intro a ha
      by_contra hnot
      have hgt : X < a * c := by omega
      exact hn ⟨a, ha, hgt⟩
    have hb := (sup_mul_le_iff_all S c X).mpr hall
    omega
  · rintro ⟨a, ha, hgt⟩
    by_contra hn
    have hb : (S.sup id) * c ≤ X := by omega
    have haBound := (sup_mul_le_iff_all S c X).mp hb a ha
    omega

/-- Original two ordinary levels, SAME rank-eight state: the prior
all-a envelope is equivalent to one largest-actual-factor inequality. -/
theorem actualRetainedEnvelope_iff_maxSmallFactor
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) :
    actualRetainedEnvelope n e q om N cap X w c s ↔
      maxActualSmallFactor N cap w *
        actualRetainedTerminalCeiling n e q om N c s ≤ X := by
  unfold actualRetainedEnvelope maxActualSmallFactor
  exact (sup_mul_le_iff_all
    (actualSmallRosserSupport N cap w)
    (actualRetainedTerminalCeiling n e q om N c s) X).symm

private theorem mul_max_le_iff
    (a b c X : ℕ) :
    a * max b c ≤ X ↔ a * b ≤ X ∧ a * c ≤ X := by
  constructor
  · intro h
    exact ⟨
      (Nat.mul_le_mul_left a (le_max_left b c)).trans h,
      (Nat.mul_le_mul_left a (le_max_right b c)).trans h⟩
  · rintro ⟨hb, hc⟩
    rcases le_total b c with hbc | hcb
    · simpa [max_eq_right hbc] using hc
    · simpa [max_eq_left hcb] using hb

/-- Two and only two cutoff-recursion executions per original eighth
occurrence, one on its own-sixth actualParent and one on its finite cap.
The actual Rosser support may be empty; no positivity assumption on a
is needed. The remaining carrier is genuinely positive as before. -/
theorem actualRetainedEnvelope_iff_twoMaxTests
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p) :
    actualRetainedEnvelope n e q om N cap X w c s ↔
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        (maxActualSmallFactor N cap w) X
        s.selectedPrefix s.positive s.remaining = true ∧
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        (maxActualSmallFactor N cap w) X
        s.selectedPrefix s.positive s.remaining = true := by
  rw [actualRetainedEnvelope_iff_maxSmallFactor]
  let A := maxActualSmallFactor N cap w
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  change
    A * max
      (retainedTerminalCeiling oldR s.selectedPrefix s.positive s.remaining)
      (retainedTerminalCeiling newR s.selectedPrefix s.positive s.remaining)
      ≤ X ↔
    withinPhysicalCut oldR A X
      s.selectedPrefix s.positive s.remaining = true ∧
    withinPhysicalCut newR A X
      s.selectedPrefix s.positive s.remaining = true
  rw [mul_max_le_iff]
  constructor
  · rintro ⟨hOld, hNew⟩
    exact ⟨
      (withinPhysicalCut_correct oldR A X
        s.selectedPrefix s.remaining s.positive hpos).mpr hOld,
      (withinPhysicalCut_correct newR A X
        s.selectedPrefix s.remaining s.positive hpos).mpr hNew⟩
  · rintro ⟨hOld, hNew⟩
    exact ⟨
      (withinPhysicalCut_correct oldR A X
        s.selectedPrefix s.remaining s.positive hpos).mp hOld,
      (withinPhysicalCut_correct newR A X
        s.selectedPrefix s.remaining s.positive hpos).mp hNew⟩

/-- A failed maximum-factor cutoff cannot be a phantom factor. It
implies some ORIGINAL small factor actually fails the SAME retained
policy test. It does not claim a nonzero net signed physical sum. -/
theorem maxSmallTest_false_has_original_factor
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w : ℝ)
    (pre remaining : List ℕ) (positive : Bool)
    (hpos : ∀ p ∈ remaining, 0 < p)
    (hfail : withinPhysicalCut R (maxActualSmallFactor N cap w) X
        pre positive remaining = false) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      withinPhysicalCut R a X pre positive remaining = false := by
  let M := retainedTerminalCeiling R pre positive remaining
  have hmax : X < maxActualSmallFactor N cap w * M := by
    by_contra hn
    have hbound : maxActualSmallFactor N cap w * M ≤ X := by omega
    have htrue := (withinPhysicalCut_correct R
      (maxActualSmallFactor N cap w) X pre remaining positive hpos).mpr hbound
    rw [hfail] at htrue
    cases htrue
  obtain ⟨a, ha, hgt⟩ :=
    (sup_mul_gt_iff_exists (actualSmallRosserSupport N cap w) M X).mp hmax
  refine ⟨a, ha, ?_⟩
  cases ht : withinPhysicalCut R a X pre positive remaining with
  | false => rfl
  | true =>
      have hb := (withinPhysicalCut_correct R a X
        pre remaining positive hpos).mp ht
      omega

/-- An actionable failure certificate pairs the ORIGINAL small factor
with an ORIGINAL retained rough terminal, including its history and sign.
A witness is not a count or a certified nonzero signed coefficient. -/
theorem maxSmallTest_false_has_original_high_leaf
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w : ℝ)
    (pre remaining : List ℕ) (positive : Bool)
    (hpos : ∀ p ∈ remaining, 0 < p)
    (hfail : withinPhysicalCut R (maxActualSmallFactor N cap w) X
        pre positive remaining = false) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      ∃ leaf ∈ firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
        pre positive 1 remaining,
        X < a * leaf.selected.prod := by
  obtain ⟨a, ha, hf⟩ :=
    maxSmallTest_false_has_original_factor R N cap X w
      pre remaining positive hpos hfail
  obtain ⟨leaf, hleaf, hgt⟩ :=
    (withinPhysicalCut_false_iff_high_leaf R a X
      pre remaining positive hpos).mp hf
  exact ⟨a, ha, leaf, hleaf, hgt⟩

/-- Exact arithmetical high-q zero of the unchanged old-minus-new
ordinary saving after ONLY TWO actual cutoff decisions. The original
Rosser factors and their signed beta weights are still used in the
saving itself. -/
theorem ordinarySaving_highQ_zero_of_twoMaxTests
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p)
    (htests :
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        (maxActualSmallFactor N cap w) X
        s.selectedPrefix s.positive s.remaining = true ∧
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        (maxActualSmallFactor N cap w) X
        s.selectedPrefix s.positive s.remaining = true) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  apply ordinarySaving_highQ_zero_of_actualRetainedEnvelope
  exact (actualRetainedEnvelope_iff_twoMaxTests
    n e q om N cap X w c s hpos).mpr htests

end
end ImbalancedChen.P4AOriginalFull87MaxSmallPrunedWitness
