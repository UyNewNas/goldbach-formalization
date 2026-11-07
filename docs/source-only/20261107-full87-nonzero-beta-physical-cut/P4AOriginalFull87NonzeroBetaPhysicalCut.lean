import ImbalancedChen.P4AOriginalFull87MaxSmallPrunedWitness
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The former maximum was taken over ALL divisors of the small presieve
product.  That is only a display support: the original Rosser PLUS and
MINUS coefficients can both vanish, notably beyond their strict level L.

This packet removes those demonstrably zero small factors ONLY FROM
THE PHYSICAL CUTOFF DECISION.  The signed source, its full beta sum,
the two ordinary policies, and all retained-leaf occurrences are unchanged.
A failed gate now supplies an actual factor with a nonzero original
Rosser coefficient in AT LEAST ONE sign, plus a permitted terminal leaf.
That sign need not match the leaf, and signed cancellation remains open.

The new gate is sufficient for arithmetic high-q zero; it is NOT a
small high-q remainder estimate, a valid PP cutoff, or a reserve payment.
-/

namespace ImbalancedChen.P4AOriginalFull87NonzeroBetaPhysicalCut
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

/-- Exactly the ORIGINAL displayed small support on which at least one
ORIGINAL Rosser coefficient is nonzero. This only drives a gate; attached
terminal sums still range over actualSmallRosserSupport with every beta. -/
def nonzeroRosserSupport (N cap : ℕ) (w L : ℝ) : Finset ℕ :=
  (actualSmallRosserSupport N cap w).filter
    (fun a => actualSmallRosserPlus N cap w L a ≠ 0 ∨
      actualSmallRosserMinus N cap w L a ≠ 0)

theorem mem_nonzeroRosserSupport_iff (N cap a : ℕ) (w L : ℝ) :
    a ∈ nonzeroRosserSupport N cap w L ↔
      a ∈ actualSmallRosserSupport N cap w ∧
      (actualSmallRosserPlus N cap w L a ≠ 0 ∨
       actualSmallRosserMinus N cap w L a ≠ 0) := by
  simp [nonzeroRosserSupport]

/-- Unlike the old presieve-divisor maximum, every member of this
physical decision support satisfies the EXISTING strict Rosser level. -/
theorem nonzeroRosserSupport_lt_L (N cap a : ℕ) (w L : ℝ)
    (ha : a ∈ nonzeroRosserSupport N cap w L) : (a : ℝ) < L := by
  obtain ⟨_, hpm⟩ := (mem_nonzeroRosserSupport_iff N cap a w L).mp ha
  rcases hpm with hp | hm
  · exact (actualSmallRosserPlus_active hp).2.1
  · exact (actualSmallRosserMinus_active hm).2.1

/-- Auxiliary maximum for the gate, NOT a substitute for any beta. -/
def maxNonzeroRosserFactor (N cap : ℕ) (w L : ℝ) : ℕ :=
  (nonzeroRosserSupport N cap w L).sup id

/-- A genuinely finite physical improvement: the maximum active factor
never exceeds the ceiling of the original strict Rosser level. -/
theorem maxNonzeroRosserFactor_le_ceil (N cap : ℕ) (w L : ℝ) :
    maxNonzeroRosserFactor N cap w L ≤ Nat.ceil L := by
  unfold maxNonzeroRosserFactor
  apply Finset.sup_le
  intro a ha
  have hlt : a < Nat.ceil L :=
    (Nat.lt_ceil).2 (nonzeroRosserSupport_lt_L N cap a w L ha)
  omega

private theorem sup_mul_le_iff_all (S : Finset ℕ) (m X : ℕ) :
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
        · have hs : (S.sup id) * m ≤ X :=
            (Nat.mul_le_mul_right m
              (le_max_right a (S.sup id))).trans h
          exact (ih.mp hs) b hbS
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

/-- This sharper finite gate is about the SAME actual old/new policies. -/
def nonzeroRetainedEnvelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ) : Prop :=
  ∀ a ∈ nonzeroRosserSupport N cap w L,
    a * actualRetainedTerminalCeiling n e q om N c s ≤ X

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

/-- Two pruned decisions on a much smaller, L-licensed active maximum.
The old all-divisor gate is still valid but unnecessarily stringent. -/
theorem nonzeroRetainedEnvelope_iff_twoActiveMaxTests
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p) :
    nonzeroRetainedEnvelope n e q om N cap X w L c s ↔
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        (maxNonzeroRosserFactor N cap w L) X
        s.selectedPrefix s.positive s.remaining = true ∧
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        (maxNonzeroRosserFactor N cap w L) X
        s.selectedPrefix s.positive s.remaining = true := by
  unfold nonzeroRetainedEnvelope
  rw [← sup_mul_le_iff_all
    (nonzeroRosserSupport N cap w L)
    (actualRetainedTerminalCeiling n e q om N c s) X]
  let A := maxNonzeroRosserFactor N cap w L
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  change A * max
      (retainedTerminalCeiling oldR s.selectedPrefix s.positive s.remaining)
      (retainedTerminalCeiling newR s.selectedPrefix s.positive s.remaining) ≤ X ↔
    withinPhysicalCut oldR A X
      s.selectedPrefix s.positive s.remaining = true ∧
    withinPhysicalCut newR A X
      s.selectedPrefix s.positive s.remaining = true
  rw [mul_max_le_iff]
  exact and_congr
    (withinPhysicalCut_correct oldR A X
      s.selectedPrefix s.remaining s.positive hpos).symm
    (withinPhysicalCut_correct newR A X
      s.selectedPrefix s.remaining s.positive hpos).symm

/-- One terminal has zero high-q contribution either because its
physical modulus is within X, OR because BOTH original sign-specific
coefficients vanish. No redefinition of the terminal sum occurs. -/
private theorem attached_highQ_zero_of_nonzero
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (positive : Bool) (pre : List ℕ)
    (hbound : ∀ a ∈ nonzeroRosserSupport N cap w L,
      a * pre.prod ≤ X) :
    attachedLeafTest N cap 1 w L (highQTest X F) positive pre = 0 := by
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hactive : a ∈ nonzeroRosserSupport N cap w L
  · have hnot : ¬ X < 1 * (a * pre.prod) := by
      simpa only [one_mul] using
        (Nat.not_lt.mpr (hbound a hactive))
    simp [highQTest, hnot]
  · have hnot : ¬ (actualSmallRosserPlus N cap w L a ≠ 0 ∨
        actualSmallRosserMinus N cap w L a ≠ 0) := by
      intro hor
      exact hactive ((mem_nonzeroRosserSupport_iff N cap a w L).mpr
        ⟨ha, hor⟩)
    have hp : actualSmallRosserPlus N cap w L a = 0 := by
      by_contra hn
      exact hnot (Or.inl hn)
    have hm : actualSmallRosserMinus N cap w L a = 0 := by
      by_contra hn
      exact hnot (Or.inr hn)
    cases positive <;> simp [hp, hm]

/-- ORIGINAL leaf list, not an invented policy or full-carrier envelope.
Signed cancellation is not used: every retained terminal is exactly zero. -/
theorem signedTest_highQ_zero_of_nonzero_ceiling
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (F : ℕ → ℝ) (pre remaining : List ℕ)
    (positive : Bool) (mass : ℝ)
    (hbound : ∀ a ∈ nonzeroRosserSupport N cap w L,
      a * retainedTerminalCeiling R pre positive remaining ≤ X) :
    signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining = 0 := by
  rw [signedTest_eq_leaves]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨leaf, hleaf, rfl⟩ := List.mem_map.mp hv
  have hleafBound := retained_leaf_product_le_ceiling
    R pre remaining positive mass leaf hleaf
  have hsmall : ∀ a ∈ nonzeroRosserSupport N cap w L,
      a * leaf.selected.prod ≤ X := by
    intro a ha
    exact (Nat.mul_le_mul_left a hleafBound).trans (hbound a ha)
  have hz := attached_highQ_zero_of_nonzero
    N cap X w L F leaf.positive leaf.selected hsmall
  rw [hz]
  ring

/-- Physical high-q ZERO for the unchanged ordinary old-minus-new
saving, with beta chosen afresh at EACH retained terminal sign. -/
theorem ordinarySaving_highQ_zero_of_activeEnvelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hbound : nonzeroRetainedEnvelope n e q om N cap X w L c s) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  have hOld : ∀ a ∈ nonzeroRosserSupport N cap w L,
      a * retainedTerminalCeiling oldR s.selectedPrefix s.positive
        s.remaining ≤ X := by
    intro a ha
    exact (Nat.mul_le_mul_left a (le_max_left
      (retainedTerminalCeiling oldR s.selectedPrefix s.positive s.remaining)
      (retainedTerminalCeiling newR s.selectedPrefix s.positive s.remaining))).trans
      (hbound a ha)
  have hNew : ∀ a ∈ nonzeroRosserSupport N cap w L,
      a * retainedTerminalCeiling newR s.selectedPrefix s.positive
        s.remaining ≤ X := by
    intro a ha
    exact (Nat.mul_le_mul_left a (le_max_right
      (retainedTerminalCeiling oldR s.selectedPrefix s.positive s.remaining)
      (retainedTerminalCeiling newR s.selectedPrefix s.positive s.remaining))).trans
      (hbound a ha)
  have hold := signedTest_highQ_zero_of_nonzero_ceiling
    oldR N cap X w L F s.selectedPrefix s.remaining s.positive s.mass hOld
  have hnew := signedTest_highQ_zero_of_nonzero_ceiling
    newR N cap X w L F s.selectedPrefix s.remaining s.positive s.mass hNew
  change signedTest oldR (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest newR (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining = 0
  rw [hold, hnew, sub_self]

/-- Stronger gate can be checked using exactly the SAME two recursions.
The original source is unchanged; only zero-beta false alarms are excluded. -/
theorem ordinarySaving_highQ_zero_of_twoActiveMaxTests
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p)
    (htests :
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
        (maxNonzeroRosserFactor N cap w L) X
        s.selectedPrefix s.positive s.remaining = true ∧
      withinPhysicalCut
        (ordinaryParityRosserPolicy false
          ((N : ℝ) ^ (finiteCap n c
            (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
        (maxNonzeroRosserFactor N cap w L) X
        s.selectedPrefix s.positive s.remaining = true) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  apply ordinarySaving_highQ_zero_of_activeEnvelope
  exact (nonzeroRetainedEnvelope_iff_twoActiveMaxTests
    n e q om N cap X w L c s hpos).mpr htests

/-- A failed active-maximum decision has a genuine original factor
with at least one NONZERO sign-specific beta, and an ORIGINAL permitted
terminal. This STILL need not yield a nonzero total signed full-q rho. -/
theorem activeMaxTest_false_has_nonzero_beta_factor_and_leaf
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (pre remaining : List ℕ) (positive : Bool)
    (hpos : ∀ p ∈ remaining, 0 < p)
    (hfail : withinPhysicalCut R (maxNonzeroRosserFactor N cap w L) X
      pre positive remaining = false) :
    ∃ a ∈ nonzeroRosserSupport N cap w L,
      (actualSmallRosserPlus N cap w L a ≠ 0 ∨
        actualSmallRosserMinus N cap w L a ≠ 0) ∧
      ∃ leaf ∈ firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
        pre positive 1 remaining, X < a * leaf.selected.prod := by
  let S := nonzeroRosserSupport N cap w L
  let M := retainedTerminalCeiling R pre positive remaining
  have hmax : X < (S.sup id) * M := by
    by_contra hn
    have hb : (S.sup id) * M ≤ X := Nat.le_of_not_gt hn
    have ht := (withinPhysicalCut_correct R
      (maxNonzeroRosserFactor N cap w L) X pre remaining positive hpos).mpr hb
    rw [hfail] at ht
    cases ht
  have hex : ∃ a ∈ S, X < a * M := by
    by_contra hn
    have hall : ∀ a ∈ S, a * M ≤ X := by
      intro a ha
      by_contra hnot
      exact hn ⟨a, ha, Nat.lt_of_not_ge hnot⟩
    have hb := (sup_mul_le_iff_all S M X).mpr hall
    omega
  obtain ⟨a, ha, hgt⟩ := hex
  obtain ⟨leaf, hleaf, heq⟩ :=
    retained_ceiling_attained R pre remaining positive (1 : ℝ)
  have heqM : leaf.selected.prod = M := heq
  have hleafgt : X < a * leaf.selected.prod := by
    simpa only [← heqM] using hgt
  exact ⟨a, ha, (mem_nonzeroRosserSupport_iff N cap a w L).mp ha |>.2,
    leaf, hleaf, hleafgt⟩

end
end ImbalancedChen.P4AOriginalFull87NonzeroBetaPhysicalCut
