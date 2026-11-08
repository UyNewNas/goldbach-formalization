import ImbalancedChen.P4AOriginalFull87NonzeroBetaPhysicalCut
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The active-OR maximum cutoff of the predecessor is a sufficient ZERO
certificate, but its failure can use a beta of the WRONG leaf sign.
This packet proves the converse direction that is actually justified:
a NONZERO original high-q signed contribution necessarily has an
original retained leaf and an original small factor on which the
SIGN-SELECTED Rosser coefficient, full-q strict cutoff, test value,
and leaf value are all nonzero.

This is a causal witness, NOT a claim that a failed active-OR gate
produces a nonzero source.  It preserves the literal first-exit list,
both original continuation policies and all occurrences; no new
physical coefficient or positivity premise is introduced.
-/

namespace ImbalancedChen.P4AOriginalFull87SignMatchedResidualWitness

noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87OwnedEighthSource (ordinarySaving)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)

/-- A genuinely nonzero ORIGINAL signed small-factor terminal sum
has a nonzero contributor with its ACTUAL terminal sign.  The strict
test is on the complete physical modulus, and F may itself vanish. -/
theorem attached_nonzero_has_sign_matched_highQ_factor
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (positive : Bool) (pre : List ℕ)
    (hne : attachedLeafTest N cap 1 w L (highQTest X F)
      positive pre ≠ 0) :
    ∃ a ∈ actualSmallRosserSupport N cap w,
      (if positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
      X < a * pre.prod ∧ F (a * pre.prod) ≠ 0 := by
  classical
  by_contra hno
  have hz : attachedLeafTest N cap 1 w L (highQTest X F)
      positive pre = 0 := by
    unfold attachedLeafTest
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hbeta :
        (if positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) = 0
    · simp [hbeta]
    · by_cases hq : X < a * pre.prod
      · have hF : F (a * pre.prod) = 0 := by
          by_contra hnF
          exact hno ⟨a, ha, hbeta, hq, hnF⟩
        simp [highQTest, hq, hF]
      · simp [highQTest, hq]
  exact hne hz

/-- A nonzero original first-exit high-q test supplies an ACTUAL leaf
occurrence of nonzero signed mass and its sign-matched small factor.
The list is not converted to a set; distinct occurrences remain distinct. -/
theorem signed_nonzero_has_actual_sign_matched_leaf
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (F : ℕ → ℝ) (pre remaining : List ℕ)
    (positive : Bool) (mass : ℝ)
    (hne : signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining ≠ 0) :
    ∃ leaf ∈ firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
        pre positive mass remaining,
      leaf.value ≠ 0 ∧
      ∃ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
        X < a * leaf.selected.prod ∧
        F (a * leaf.selected.prod) ≠ 0 := by
  classical
  by_contra hno
  have hz : signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining = 0 := by
    rw [signedTest_eq_leaves]
    apply List.sum_eq_zero
    intro v hv
    obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.mp hv
    by_cases hvalue : leaf.value = 0
    · simp [hvalue]
    · by_cases hterm : attachedLeafTest N cap 1 w L (highQTest X F)
          leaf.positive leaf.selected = 0
      · simp [hterm]
      · obtain ⟨a, ha, hb, hq, hF⟩ :=
          attached_nonzero_has_sign_matched_highQ_factor
            N cap X w L F leaf.positive leaf.selected hterm
        exact (hno ⟨leaf, hleaf, hvalue, a, ha, hb, hq, hF⟩).elim
  exact hne hz

/-- Necessary causal witness for a NONZERO original own-sixth minus
finite-eighth ordinary high-q saving.  R is one of precisely the TWO
unchanged policies at the SAME actual eighth history; this theorem
does NOT assert that an active-OR gate failure makes the saving nonzero. -/
theorem ordinary_nonzero_has_original_sign_matched_leaf
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hne : ordinarySaving n e q om N cap w L (highQTest X F) c s ≠ 0) :
    ∃ R : Bool → List ℕ → Bool,
      (R = ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix) ∨
       R = ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ))) ∧
      ∃ leaf ∈ firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
          s.selectedPrefix s.positive s.mass s.remaining,
        leaf.value ≠ 0 ∧
        ∃ a ∈ actualSmallRosserSupport N cap w,
          (if leaf.positive then actualSmallRosserPlus N cap w L a
           else actualSmallRosserMinus N cap w L a) ≠ 0 ∧
          X < a * leaf.selected.prod ∧
          F (a * leaf.selected.prod) ≠ 0 := by
  classical
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  let T := attachedLeafTest N cap 1 w L (highQTest X F)
  have hrepr : ordinarySaving n e q om N cap w L (highQTest X F) c s =
      signedTest oldR (fun _ : ℕ => (1 : ℝ)) T
        s.selectedPrefix s.positive s.mass s.remaining -
      signedTest newR (fun _ : ℕ => (1 : ℝ)) T
        s.selectedPrefix s.positive s.mass s.remaining := rfl
  by_cases hold : signedTest oldR (fun _ : ℕ => (1 : ℝ)) T
      s.selectedPrefix s.positive s.mass s.remaining = 0
  · have hnew : signedTest newR (fun _ : ℕ => (1 : ℝ)) T
        s.selectedPrefix s.positive s.mass s.remaining ≠ 0 := by
      intro hz
      apply hne
      rw [hrepr, hold, hz]
      ring
    obtain ⟨leaf, hl, hv, a, ha, hb, hq, hF⟩ :=
      signed_nonzero_has_actual_sign_matched_leaf
        newR N cap X w L F s.selectedPrefix s.remaining
        s.positive s.mass hnew
    exact ⟨newR, Or.inr rfl, leaf, hl, hv, a, ha, hb, hq, hF⟩
  · obtain ⟨leaf, hl, hv, a, ha, hb, hq, hF⟩ :=
      signed_nonzero_has_actual_sign_matched_leaf
        oldR N cap X w L F s.selectedPrefix s.remaining
        s.positive s.mass hold
    exact ⟨oldR, Or.inl rfl, leaf, hl, hv, a, ha, hb, hq, hF⟩

end
end ImbalancedChen.P4AOriginalFull87SignMatchedResidualWitness
