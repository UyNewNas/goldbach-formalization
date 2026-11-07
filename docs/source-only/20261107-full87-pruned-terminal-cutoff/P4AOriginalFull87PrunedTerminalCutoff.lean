import ImbalancedChen.P4AOriginalFull87RetainedTerminalCeiling
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

Cutoff-directed exact branch-and-bound on the ORIGINAL retained ordinary
first-exit recursion.  This avoids enumerating all terminal leaves merely
to ask whether a fixed physical small factor a produces any q > X.
The upper exit uses the complete remaining positive carrier; the lower
exit uses the incoming skip-all retained leaf.  Both exits are proved,
not postulated.  An inconclusive node follows only the original policy.

This is a finite exact algorithm, not a polynomial-time claim. The
original full-q Rosser factor, two separately frozen ordinary policies,
strict high-q boundary, old-minus-new saving and actual eighth history
are preserved. No numerical PP level or asymptotic payment is supplied.
-/

namespace ImbalancedChen.P4AOriginalFull87PrunedTerminalCutoff
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87RetainedTerminalCeiling
open P4AOriginalFull87OwnedEighthSource (ordinarySaving)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- A cutoff-directed decision on the same R, same ordered rough carrier,
and same physical multiplier a. It short-circuits a safe whole-carrier
upper bound and the forced oversized skip-all branch. Otherwise it visits
exactly the original permitted take/skip recursion. -/
def withinPhysicalCut (R : Bool → List ℕ → Bool) (a X : ℕ)
    (pre : List ℕ) (positive : Bool) : List ℕ → Bool
  | [] => decide (a * pre.prod ≤ X)
  | p :: ps =>
      if a * (pre.prod * (p :: ps).prod) ≤ X then true
      else if X < a * pre.prod then false
      else if R (!positive) (p :: pre) = true then
        withinPhysicalCut R a X pre positive ps &&
          withinPhysicalCut R a X (p :: pre) (!positive) ps
      else withinPhysicalCut R a X pre positive ps

/-- The skip-all terminal occurs under every original Boolean policy. -/
theorem prefix_product_le_terminal_ceiling
    (R : Bool → List ℕ → Bool)
    (pre remaining : List ℕ) (positive : Bool) :
    pre.prod ≤ retainedTerminalCeiling R pre positive remaining := by
  induction remaining with
  | nil => rfl
  | cons p ps ih =>
      exact ih.trans (ceiling_skip_le R pre positive p ps)

/-- The full physical modulus bound on the exact maximum is equivalent
to bounding both subtrees: Nat multiplication respects this max. -/
private theorem mul_max_le_iff (a b c X : ℕ) :
    a * max b c ≤ X ↔ a * b ≤ X ∧ a * c ≤ X := by
  constructor
  · intro h
    exact ⟨(Nat.mul_le_mul_left a (le_max_left b c)).trans h,
      (Nat.mul_le_mul_left a (le_max_right b c)).trans h⟩
  · rintro ⟨hb, hc⟩
    rcases le_total b c with h | h
    · simpa [max_eq_right h] using hc
    · simpa [max_eq_left h] using hb

/-- Exact pruning correctness, with only the genuine positive-prime
carrier condition. Failure is NOT treated as a negligible mass: it
means that some originally retained terminal has q > X. -/
theorem withinPhysicalCut_correct
    (R : Bool → List ℕ → Bool) (a X : ℕ)
    (pre remaining : List ℕ) (positive : Bool) :
    (∀ p ∈ remaining, 0 < p) →
    (withinPhysicalCut R a X pre positive remaining = true ↔
      a * retainedTerminalCeiling R pre positive remaining ≤ X) := by
  induction remaining generalizing pre positive with
  | nil =>
      intro _
      simp [withinPhysicalCut, retainedTerminalCeiling]
  | cons p ps ih =>
      intro hpos
      have htail : ∀ r ∈ ps, 0 < r := by
        intro r hr
        exact hpos r (by simp [hr])
      by_cases hwhole : a * (pre.prod * (p :: ps).prod) ≤ X
      · have hceil :
            a * retainedTerminalCeiling R pre positive (p :: ps) ≤ X :=
          (Nat.mul_le_mul_left a
            (retained_ceiling_le_full_carrier R pre (p :: ps) positive hpos)).trans
              hwhole
        simp [withinPhysicalCut, hwhole, hceil]
      · by_cases hprefix : X < a * pre.prod
        · have hskip :
              a * pre.prod ≤
                a * retainedTerminalCeiling R pre positive (p :: ps) :=
            Nat.mul_le_mul_left a
              (prefix_product_le_terminal_ceiling R pre (p :: ps) positive)
          have hnot :
              ¬ a * retainedTerminalCeiling R pre positive (p :: ps) ≤ X :=
            not_le.mpr (hprefix.trans_le hskip)
          simp [withinPhysicalCut, hwhole, hprefix, hnot]
        · have hs := ih pre positive htail
          have ht := ih (p :: pre) (!positive) htail
          by_cases htake : R (!positive) (p :: pre) = true
          · simpa [withinPhysicalCut, hwhole, hprefix, htake,
                retainedTerminalCeiling, Bool.and_eq_true, max_le_iff]
              using (show
                (withinPhysicalCut R a X pre positive ps = true ∧
                 withinPhysicalCut R a X (p :: pre) (!positive) ps = true) ↔
                (a * retainedTerminalCeiling R pre positive ps ≤ X ∧
                 a * retainedTerminalCeiling R (p :: pre) (!positive) ps ≤ X)
                from and_congr hs ht)
          · simpa [withinPhysicalCut, hwhole, hprefix, htake,
                retainedTerminalCeiling] using hs

/-- A negative decision exposes an ORIGINAL retained leaf whose attached
physical modulus is genuinely beyond X. It is not a new coefficient or
a claim that a signed coefficient is nonzero after cancellation. -/
theorem withinPhysicalCut_false_iff_high_leaf
    (R : Bool → List ℕ → Bool) (a X : ℕ)
    (pre remaining : List ℕ) (positive : Bool)
    (hpos : ∀ p ∈ remaining, 0 < p) :
    withinPhysicalCut R a X pre positive remaining = false ↔
      ∃ leaf ∈ firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
        pre positive 1 remaining, X < a * leaf.selected.prod := by
  have hc := withinPhysicalCut_correct R a X pre remaining positive hpos
  constructor
  · intro hf
    have hn : ¬ a * retainedTerminalCeiling R pre positive remaining ≤ X := by
      intro hb
      have ht := hc.mpr hb
      simp [hf] at ht
    obtain ⟨leaf, hmem, heq⟩ :=
      retained_ceiling_attained R pre remaining positive (1 : ℝ)
    refine ⟨leaf, hmem, ?_⟩
    have hlt : X < a * retainedTerminalCeiling R pre positive remaining :=
      lt_of_not_ge hn
    simpa [heq] using hlt
  · rintro ⟨leaf, hmem, hlarge⟩
    have hb := retained_leaf_product_le_ceiling
      R pre remaining positive (1 : ℝ) leaf hmem
    have hn : ¬ a * retainedTerminalCeiling R pre positive remaining ≤ X :=
      not_le.mpr (hlarge.trans_le (Nat.mul_le_mul_left a hb))
    cases hbool : withinPhysicalCut R a X pre positive remaining with
    | false => rfl
    | true => exact False.elim (hn (hc.mp hbool))

/-- Apply the exact physical cut to the two ORIGINAL ordinary levels at
the SAME actual eighth state, without relabelling parent or cap. -/
theorem actualRetainedEnvelope_iff_prunedTests
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p) :
    actualRetainedEnvelope n e q om N cap X w c s ↔
      ∀ a ∈ actualSmallRosserSupport N cap w,
        withinPhysicalCut
          (ordinaryParityRosserPolicy false
            ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
          a X s.selectedPrefix s.positive s.remaining = true ∧
        withinPhysicalCut
          (ordinaryParityRosserPolicy false
            ((N : ℝ) ^ (finiteCap n c
              (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
          a X s.selectedPrefix s.positive s.remaining = true := by
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  have hconvert (a : ℕ) :
      a * actualRetainedTerminalCeiling n e q om N c s ≤ X ↔
      a * retainedTerminalCeiling oldR s.selectedPrefix s.positive s.remaining ≤ X ∧
      a * retainedTerminalCeiling newR s.selectedPrefix s.positive s.remaining ≤ X := by
    change a * max
      (retainedTerminalCeiling oldR s.selectedPrefix s.positive s.remaining)
      (retainedTerminalCeiling newR s.selectedPrefix s.positive s.remaining) ≤ X ↔ _
    exact mul_max_le_iff _ _ _ _
  constructor
  · intro h a ha
    have hb := (hconvert a).mp (h a ha)
    exact ⟨(withinPhysicalCut_correct oldR a X
      s.selectedPrefix s.remaining s.positive hpos).mpr hb.1,
      (withinPhysicalCut_correct newR a X
      s.selectedPrefix s.remaining s.positive hpos).mpr hb.2⟩
  · intro h a ha
    have hb := h a ha
    exact (hconvert a).mpr ⟨
      (withinPhysicalCut_correct oldR a X
        s.selectedPrefix s.remaining s.positive hpos).mp hb.1,
      (withinPhysicalCut_correct newR a X
        s.selectedPrefix s.remaining s.positive hpos).mp hb.2⟩

/-- The immediately usable arithmetic consequence is the SAME old-minus-
new ordinary saving, not a surrogate signed upper/lower subtraction.
Actual saved87 gate population and the high-q debit are still open. -/
theorem ordinarySaving_highQ_zero_of_prunedTests
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p)
    (htests : ∀ a ∈ actualSmallRosserSupport N cap w,
        withinPhysicalCut
          (ordinaryParityRosserPolicy false
            ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
          a X s.selectedPrefix s.positive s.remaining = true ∧
        withinPhysicalCut
          (ordinaryParityRosserPolicy false
            ((N : ℝ) ^ (finiteCap n c
              (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
          a X s.selectedPrefix s.positive s.remaining = true) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  apply ordinarySaving_highQ_zero_of_actualRetainedEnvelope
  exact (actualRetainedEnvelope_iff_prunedTests
    n e q om N cap X w c s hpos).mpr htests

end
end ImbalancedChen.P4AOriginalFull87PrunedTerminalCutoff
