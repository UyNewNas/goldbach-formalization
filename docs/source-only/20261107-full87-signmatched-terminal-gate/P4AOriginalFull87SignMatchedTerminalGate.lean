import ImbalancedChen.P4AOriginalFull87SignMatchedResidualWitness
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

A sign-MATCHED Boolean physical-cut certificate for the ORIGINAL ordinary
first-exit policies. The predecessor showed that a truly nonzero signed
high-q term requires a leaf with a Rosser coefficient nonzero at that
leaf's own parity. The preceding OR-maximum test can fail solely because
the opposite-parity beta is nonzero. Here every terminal cutoff tests only
its own original beta sign; the recursion visits exactly the original
skip/take tree, with no new mask, new parent, or reconstructed coefficient.

This certificate is sufficient for ZERO high-q mass, not a converse:
failure can still cancel between factors, leaves, and old-minus-new.
No PP level, saved87 archive population, or H_N payment is assumed.
-/

namespace ImbalancedChen.P4AOriginalFull87SignMatchedTerminalGate
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87NonzeroBetaPhysicalCut
open P4AOriginalFull87OwnedEighthSource (ordinarySaving)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)

/-- The ORIGINAL small Rosser factors that are nonzero at the ACTUAL
terminal sign. Only the decision support is filtered: attachedLeafTest
continues to sum every original small coefficient. -/
def signMatchedRosserSupport
    (N cap : ℕ) (w L : ℝ) (positive : Bool) : Finset ℕ :=
  (actualSmallRosserSupport N cap w).filter
    (fun a => (if positive then actualSmallRosserPlus N cap w L a
               else actualSmallRosserMinus N cap w L a) ≠ 0)

def maxSignMatchedRosserFactor
    (N cap : ℕ) (w L : ℝ) (positive : Bool) : ℕ :=
  (signMatchedRosserSupport N cap w L positive).sup id

/-- A sign-matched factor is an OR-active factor, but the reverse fails
when only the coefficient of the opposite parity is nonzero. -/
theorem maxSignMatched_le_maxOR
    (N cap : ℕ) (w L : ℝ) (positive : Bool) :
    maxSignMatchedRosserFactor N cap w L positive ≤
      maxNonzeroRosserFactor N cap w L := by
  unfold maxSignMatchedRosserFactor maxNonzeroRosserFactor
  apply Finset.sup_le
  intro a ha
  obtain ⟨hs, hb⟩ := Finset.mem_filter.mp ha
  have hor : actualSmallRosserPlus N cap w L a ≠ 0 ∨
      actualSmallRosserMinus N cap w L a ≠ 0 := by
    cases positive with
    | false => exact Or.inr hb
    | true => exact Or.inl hb
  exact Finset.le_sup
    ((mem_nonzeroRosserSupport_iff N cap a w L).mpr ⟨hs, hor⟩)

private theorem sup_mul_le_iff_all
    (S : Finset ℕ) (m X : ℕ) :
    (S.sup id) * m ≤ X ↔ ∀ a ∈ S, a * m ≤ X := by
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
        · exact (Nat.mul_le_mul_right m
            (le_max_left a (S.sup id))).trans h
        · have hS : (S.sup id) * m ≤ X :=
            (Nat.mul_le_mul_right m
              (le_max_right a (S.sup id))).trans h
          exact (ih.mp hS) b hbS
      · intro h
        have hA : a * m ≤ X := h a (Finset.mem_insert_self a S)
        have hS : ∀ b ∈ S, b * m ≤ X := by
          intro b hb
          exact h b (Finset.mem_insert_of_mem hb)
        rcases le_total a (S.sup id) with hle | hle
        · rw [max_eq_right hle]
          exact ih.mpr hS
        · rw [max_eq_left hle]
          exact hA

/-- The terminal Boolean gate has the exact quantifiers of the original
sign-selected Rosser contribution. It is true even for empty active
support, without pretending that a zero beta carries high-q mass. -/
theorem terminalSignCut_iff
    (N cap X : ℕ) (w L : ℝ) (positive : Bool) (pre : List ℕ) :
    decide (maxSignMatchedRosserFactor N cap w L positive *
        pre.prod ≤ X) = true ↔
      ∀ a ∈ actualSmallRosserSupport N cap w,
        (if positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) ≠ 0 →
          a * pre.prod ≤ X := by
  classical
  rw [decide_eq_true_eq]
  change ((signMatchedRosserSupport N cap w L positive).sup id) *
      pre.prod ≤ X ↔ _
  rw [sup_mul_le_iff_all]
  constructor
  · intro h a ha hb
    exact h a (Finset.mem_filter.mpr ⟨ha, hb⟩)
  · intro h a ha
    obtain ⟨hs, hb⟩ := Finset.mem_filter.mp ha
    exact h a hs hb

/-- The original literal full-q terminal sum is identically zero
under the sign-matched certificate. No source beta is changed. -/
theorem attached_highQ_zero_of_signCut
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (positive : Bool) (pre : List ℕ)
    (hcut : decide (maxSignMatchedRosserFactor N cap w L positive *
        pre.prod ≤ X) = true) :
    attachedLeafTest N cap 1 w L (highQTest X F) positive pre = 0 := by
  have hterminal :=
    (terminalSignCut_iff N cap X w L positive pre).mp hcut
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hb :
      (if positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) = 0
  · simp [hb]
  · have hle := hterminal a ha hb
    have hnot : ¬ X < 1 * (a * pre.prod) := by
      simpa only [one_mul] using (Nat.not_lt.mpr hle)
    simp [highQTest, hnot]

/-- Exact, policy-respecting recursion. Skip retains the incoming sign;
take uses the ACTUAL toggled sign. Unlike the OR-factor envelope, a
wrong-sign factor never forces failure at a retained leaf. -/
def signMatchedPhysicalCut
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (pre : List ℕ) (positive : Bool) : List ℕ → Bool
  | [] => decide (maxSignMatchedRosserFactor N cap w L positive *
      pre.prod ≤ X)
  | p :: ps =>
      if R (!positive) (p :: pre) = true then
        signMatchedPhysicalCut R N cap X w L pre positive ps &&
          signMatchedPhysicalCut R N cap X w L (p :: pre) (!positive) ps
      else signMatchedPhysicalCut R N cap X w L pre positive ps

/-- A true gate kills every genuine original terminal contribution,
including the leaf parity, complete physical modulus and all listed
occurrences. This is proved by recursion, not assumed as a structure
field. No primality, disjointness or cancellation premise is needed. -/
theorem signMatchedCut_true_signedTest_highQ_zero
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (F : ℕ → ℝ) (pre remaining : List ℕ)
    (positive : Bool) (mass : ℝ)
    (hcut : signMatchedPhysicalCut R N cap X w L
      pre positive remaining = true) :
    signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining = 0 := by
  induction remaining generalizing pre positive mass with
  | nil =>
      have ht : decide (maxSignMatchedRosserFactor N cap w L positive *
          pre.prod ≤ X) = true := by
        simpa only [signMatchedPhysicalCut] using hcut
      have hz := attached_highQ_zero_of_signCut
        N cap X w L F positive pre ht
      simp [signedTest, hz]
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · have hp : signMatchedPhysicalCut R N cap X w L
            pre positive ps = true ∧
            signMatchedPhysicalCut R N cap X w L
              (p :: pre) (!positive) ps = true := by
          simpa only [signMatchedPhysicalCut, if_pos hr,
            Bool.and_eq_true] using hcut
        have hs := ih pre positive mass hp.1
        have ht := ih (p :: pre) (!positive) (mass * (1 : ℝ)) hp.2
        simp only [signedTest, if_pos hr, hs, ht, add_zero]
      · have hp : signMatchedPhysicalCut R N cap X w L
            pre positive ps = true := by
          simpa only [signMatchedPhysicalCut, if_neg hr] using hcut
        have hs := ih pre positive mass hp
        simpa only [signedTest, if_neg hr, add_zero] using hs

/-- The two original old/new policies are checked at one and the SAME
actual eighth occurrence. This cannot attach a mask to an inherited
branch or change the owned source list. -/
theorem ordinarySaving_highQ_zero_of_twoSignMatchedCuts
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hold :
      signMatchedPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        N cap X w L s.selectedPrefix s.positive s.remaining = true)
    (hnew :
      signMatchedPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        N cap X w L s.selectedPrefix s.positive s.remaining = true) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  have hzOld := signMatchedCut_true_signedTest_highQ_zero
    oldR N cap X w L F s.selectedPrefix s.remaining s.positive s.mass hold
  have hzNew := signMatchedCut_true_signedTest_highQ_zero
    newR N cap X w L F s.selectedPrefix s.remaining s.positive s.mass hnew
  change signedTest oldR (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest newR (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining = 0
  rw [hzOld, hzNew, sub_self]

end
end ImbalancedChen.P4AOriginalFull87SignMatchedTerminalGate
