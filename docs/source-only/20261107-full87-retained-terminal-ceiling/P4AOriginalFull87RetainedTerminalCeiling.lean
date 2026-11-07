import ImbalancedChen.P4AOriginalFull87HighQCarrierTriage
import ImbalancedChen.FirstExitTree
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The preceding full-carrier zero certificate multiplies EVERY unprocessed
rough prime, even if the original ordinary policy rejects the branch.
This packet instead computes the largest terminal product reachable under
the ACTUAL Boolean retained policy, at the SAME history, sign and carrier.

The recurrence follows only the original skip and licensed select branches.
It is sharp at the level of retained terminal PRODUCTS (not claimed sharp
for signed coefficients, where cancellation or zero beta can occur). Both
the own-sixth parent and the finite eighth cap are evaluated separately,
then their maxima are joined. No policy change, additional mask, fictional
PP threshold, H_N estimate, or reserve payment occurs.
-/

namespace ImbalancedChen.P4AOriginalFull87RetainedTerminalCeiling
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87HighQCarrierTriage (carrierEnvelope)
open P4AOriginalFull87OwnedEighthSource (ordinarySaving)
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87FiniteEighthCap (finiteCap)
open P4AOriginalFull87SourceDispatch (point8)
open P4AOriginalFull87EighthKernelIntegration (actualParent)

/-- An executable-on-finite-data MAXIMUM of reachable retained terminal
rough products. Skipping is always allowed; taking p is considered only
if the ORIGINAL R accepts the new signed history. No artificial support
or proof-valued target witness is introduced. -/
def retainedTerminalCeiling (R : Bool → List ℕ → Bool)
    (pre : List ℕ) (positive : Bool) : List ℕ → ℕ
  | [] => pre.prod
  | p :: ps =>
      max (retainedTerminalCeiling R pre positive ps)
        (if R (!positive) (p :: pre) = true then
          retainedTerminalCeiling R (p :: pre) (!positive) ps
         else 0)

/-- Every skip branch is included, even after an odd selection fails. -/
theorem ceiling_skip_le (R : Bool → List ℕ → Bool)
    (pre : List ℕ) (positive : Bool) (p : ℕ) (ps : List ℕ) :
    retainedTerminalCeiling R pre positive ps ≤
      retainedTerminalCeiling R pre positive (p :: ps) := by
  change retainedTerminalCeiling R pre positive ps ≤
    max (retainedTerminalCeiling R pre positive ps)
      (if R (!positive) (p :: pre) = true then
        retainedTerminalCeiling R (p :: pre) (!positive) ps else 0)
  exact le_max_left _ _

/-- The take branch is counted precisely when the original policy takes it. -/
theorem ceiling_take_le (R : Bool → List ℕ → Bool)
    (pre : List ℕ) (positive : Bool) (p : ℕ) (ps : List ℕ)
    (htake : R (!positive) (p :: pre) = true) :
    retainedTerminalCeiling R (p :: pre) (!positive) ps ≤
      retainedTerminalCeiling R pre positive (p :: ps) := by
  change retainedTerminalCeiling R (p :: pre) (!positive) ps ≤
    max (retainedTerminalCeiling R pre positive ps)
      (if R (!positive) (p :: pre) = true then
        retainedTerminalCeiling R (p :: pre) (!positive) ps else 0)
  rw [if_pos htake]
  exact le_max_right _ _

/-- Every ACTUAL retained terminal leaf lies below the recursive ceiling.
Unlike the full-carrier envelope, rejected selections never enter the max. -/
theorem retained_leaf_product_le_ceiling
    (R : Bool → List ℕ → Bool)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hl : leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
      pre positive mass remaining) :
    leaf.selected.prod ≤ retainedTerminalCeiling R pre positive remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      simp only [firstExitRetainedLeaves, List.mem_singleton] at hl
      subst leaf
      rfl
  | cons p ps ih =>
      by_cases hr : R (!positive) (p :: pre) = true
      · simp only [firstExitRetainedLeaves, if_pos hr, List.mem_append] at hl
        rcases hl with hskip | htake
        · exact (ih pre positive mass hskip).trans
            (ceiling_skip_le R pre positive p ps)
        · exact (ih (p :: pre) (!positive) (mass * 1) htake).trans
            (ceiling_take_le R pre positive p ps hr)
      · simp only [firstExitRetainedLeaves, if_neg hr, List.append_nil] at hl
        exact (ih pre positive mass hl).trans
          (ceiling_skip_le R pre positive p ps)

/-- The bound is attained by an ACTUAL retained leaf: it is the exact
maximum of the finite permitted terminal products, not an assumed cap. -/
theorem retained_ceiling_attained
    (R : Bool → List ℕ → Bool)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ) :
    ∃ leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
        pre positive mass remaining,
      leaf.selected.prod = retainedTerminalCeiling R pre positive remaining := by
  induction remaining generalizing pre positive mass with
  | nil =>
      refine ⟨{ selected := pre, positive := positive, mass := mass }, ?_, ?_⟩
      · simp [firstExitRetainedLeaves]
      · simp [retainedTerminalCeiling]
  | cons p ps ih =>
      obtain ⟨skip, hskip, hskipEq⟩ := ih pre positive mass
      by_cases hr : R (!positive) (p :: pre) = true
      · obtain ⟨take, htake, htakeEq⟩ :=
          ih (p :: pre) (!positive) (mass * 1)
        by_cases hle : retainedTerminalCeiling R pre positive ps ≤
            retainedTerminalCeiling R (p :: pre) (!positive) ps
        · refine ⟨take, ?_, ?_⟩
          · simp only [firstExitRetainedLeaves, if_pos hr, List.mem_append]
            exact Or.inr htake
          · change take.selected.prod =
              max (retainedTerminalCeiling R pre positive ps)
                (retainedTerminalCeiling R (p :: pre) (!positive) ps)
            rw [max_eq_right hle]
            exact htakeEq
        · have hge : retainedTerminalCeiling R (p :: pre) (!positive) ps ≤
              retainedTerminalCeiling R pre positive ps :=
            (lt_of_not_ge hle).le
          refine ⟨skip, ?_, ?_⟩
          · simp only [firstExitRetainedLeaves, if_pos hr, List.mem_append]
            exact Or.inl hskip
          · change skip.selected.prod =
              max (retainedTerminalCeiling R pre positive ps)
                (retainedTerminalCeiling R (p :: pre) (!positive) ps)
            rw [max_eq_left hge]
            exact hskipEq
      · refine ⟨skip, ?_, ?_⟩
        · simp only [firstExitRetainedLeaves, if_neg hr, List.append_nil]
          exact hskip
        · change skip.selected.prod =
            max (retainedTerminalCeiling R pre positive ps) (0 : ℕ)
          simpa [max_eq_left (Nat.zero_le _)] using hskipEq

/-- Characterization of the sharp *permitted-terminal-product* bound.
A signed cancellation may still make the actual arithmetic smaller. -/
theorem retained_ceiling_le_iff_all_leaf_products_le
    (R : Bool → List ℕ → Bool)
    (pre remaining : List ℕ) (positive : Bool) (mass : ℝ) (B : ℕ) :
    retainedTerminalCeiling R pre positive remaining ≤ B ↔
      ∀ leaf ∈ firstExitRetainedLeaves R (fun _ => 1)
        pre positive mass remaining, leaf.selected.prod ≤ B := by
  constructor
  · intro h leaf hl
    exact (retained_leaf_product_le_ceiling R pre remaining positive mass leaf hl).trans h
  · intro h
    obtain ⟨leaf, hl, heq⟩ :=
      retained_ceiling_attained R pre remaining positive mass
    rw [← heq]
    exact h leaf hl

/-- The previous full-carrier bound remains a safe upper bound for the
new sharp retained ceiling, provided the actual rough primes are positive. -/
theorem retained_ceiling_le_full_carrier
    (R : Bool → List ℕ → Bool)
    (pre remaining : List ℕ) (positive : Bool)
    (hpos : ∀ p ∈ remaining, 0 < p) :
    retainedTerminalCeiling R pre positive remaining ≤
      pre.prod * remaining.prod := by
  induction remaining generalizing pre positive with
  | nil => simp [retainedTerminalCeiling]
  | cons p ps ih =>
      have hp : 1 ≤ p := hpos p (by simp)
      have htail : ∀ r ∈ ps, 0 < r := by
        intro r hr
        exact hpos r (by simp [hr])
      have hskip : retainedTerminalCeiling R pre positive ps ≤
          pre.prod * (p * ps.prod) := by
        calc
          _ ≤ pre.prod * ps.prod := ih pre positive htail
          _ ≤ pre.prod * (p * ps.prod) := by
            have hm : ps.prod ≤ p * ps.prod := by
              simpa only [one_mul] using
                (Nat.mul_le_mul_right ps.prod hp)
            exact Nat.mul_le_mul_left _ hm
      have htake : retainedTerminalCeiling R (p :: pre) (!positive) ps ≤
          pre.prod * (p * ps.prod) := by
        calc
          _ ≤ (p :: pre).prod * ps.prod := ih (p :: pre) (!positive) htail
          _ = pre.prod * (p * ps.prod) := by
            simp [List.prod_cons, mul_assoc, mul_comm, mul_left_comm]
      by_cases hr : R (!positive) (p :: pre) = true
      · change max (retainedTerminalCeiling R pre positive ps)
            (retainedTerminalCeiling R (p :: pre) (!positive) ps) ≤
            pre.prod * (p * ps.prod)
        exact max_le hskip htake
      · change max (retainedTerminalCeiling R pre positive ps) 0 ≤
            pre.prod * (p * ps.prod)
        exact max_le hskip (Nat.zero_le _)

/-- The original small-beta terminal has no high-q mass when its FULL
physical modulus is below cutoff; no positivity of beta is required. -/
private theorem attached_highQ_zero_of_ceiling
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool)
    (hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * pre.prod ≤ X) :
    attachedLeafTest N cap 1 w L (highQTest X F) positive pre = 0 := by
  unfold attachedLeafTest
  apply Finset.sum_eq_zero
  intro a ha
  have hnot : ¬ X < a * pre.prod := Nat.not_lt.mpr (hsmall a ha)
  simp [highQTest, hnot]

/-- A genuinely policy-dependent, finite and computable high-q ZERO
certificate, proved by induction on the unchanged signed recursion.
The bound only scans terminals that the ORIGINAL policy can retain. -/
theorem signedTest_highQ_zero_of_retained_ceiling
    (R : Bool → List ℕ → Bool) (N cap X : ℕ) (w L : ℝ)
    (F : ℕ → ℝ) (pre remaining : List ℕ)
    (positive : Bool) (mass : ℝ)
    (hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * retainedTerminalCeiling R pre positive remaining ≤ X) :
    signedTest R (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining = 0 := by
  induction remaining generalizing pre positive mass with
  | nil =>
      have hb : ∀ a ∈ actualSmallRosserSupport N cap w,
          a * pre.prod ≤ X := by
        intro a ha
        simpa only [retainedTerminalCeiling] using hsmall a ha
      simp only [signedTest]
      rw [attached_highQ_zero_of_ceiling N cap X w L F pre positive hb]
      ring
  | cons p ps ih =>
      have hskip : ∀ a ∈ actualSmallRosserSupport N cap w,
          a * retainedTerminalCeiling R pre positive ps ≤ X := by
        intro a ha
        exact (Nat.mul_le_mul_left a
          (ceiling_skip_le R pre positive p ps)).trans (hsmall a ha)
      by_cases hr : R (!positive) (p :: pre) = true
      · have htake : ∀ a ∈ actualSmallRosserSupport N cap w,
            a * retainedTerminalCeiling R (p :: pre) (!positive) ps ≤ X := by
          intro a ha
          exact (Nat.mul_le_mul_left a
            (ceiling_take_le R pre positive p ps hr)).trans (hsmall a ha)
        simp only [signedTest, if_pos hr]
        rw [ih pre positive mass hskip,
          ih (p :: pre) (!positive) (mass * (1 : ℝ)) htake]
        ring
      · simp only [signedTest, if_neg hr, add_zero]
        exact ih pre positive mass hskip

/-- The original own-sixth parent and the actual saved eighth cap are
evaluated separately at the SAME retained eighth history. -/
def actualRetainedTerminalCeiling
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N : ℕ) (c : Cell) (s : FirstExitDepthState ℕ) : ℕ :=
  max
    (retainedTerminalCeiling
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
      s.selectedPrefix s.positive s.remaining)
    (retainedTerminalCeiling
      (ordinaryParityRosserPolicy false
        ((N : ℝ) ^ (finiteCap n c
          (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
      s.selectedPrefix s.positive s.remaining)

/-- This gate is an explicit inequality involving the two actual
ordinary policies and the existing small Rosser support. It is NOT a
field carrying the desired signed-zero theorem. -/
def actualRetainedEnvelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w : ℝ) (c : Cell) (s : FirstExitDepthState ℕ) : Prop :=
  ∀ a ∈ actualSmallRosserSupport N cap w,
    a * actualRetainedTerminalCeiling n e q om N c s ≤ X

/-- The new gate genuinely weakens the preceding full-carrier gate.
It does not pretend that actual saved87 occurrences pass either gate. -/
theorem actualRetainedEnvelope_of_carrierEnvelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w : ℝ) (c : Cell)
    (s : FirstExitDepthState ℕ)
    (hpos : ∀ p ∈ s.remaining, 0 < p)
    (hcarrier : carrierEnvelope N cap X w s) :
    actualRetainedEnvelope n e q om N cap X w c s := by
  intro a ha
  have hOld := retained_ceiling_le_full_carrier
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix))
    s.selectedPrefix s.remaining s.positive hpos
  have hNew := retained_ceiling_le_full_carrier
    (ordinaryParityRosserPolicy false
      ((N : ℝ) ^ (finiteCap n c
        (point8 (N : ℝ) s.selectedPrefix) : ℝ)))
    s.selectedPrefix s.remaining s.positive hpos
  have hmax : actualRetainedTerminalCeiling n e q om N c s ≤
      s.selectedPrefix.prod * s.remaining.prod := by
    unfold actualRetainedTerminalCeiling
    exact max_le hOld hNew
  exact (Nat.mul_le_mul_left a hmax).trans (hcarrier a ha)

/-- Actual same-parent/same-history old-minus-new ordinary continuation
has arithmetic high-q ZERO under the tighter exact retained-terminal gate.
No signed-saving monotonicity, zero measure, or new inherited mask occurs. -/
theorem ordinarySaving_highQ_zero_of_actualRetainedEnvelope
    (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap X : ℕ) (w L : ℝ) (F : ℕ → ℝ)
    (c : Cell) (s : FirstExitDepthState ℕ)
    (hbound : actualRetainedEnvelope n e q om N cap X w c s) :
    ordinarySaving n e q om N cap w L (highQTest X F) c s = 0 := by
  let oldR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ actualParent n e q om (N : ℝ) s.selectedPrefix)
  let newR := ordinaryParityRosserPolicy false
    ((N : ℝ) ^ (finiteCap n c
      (point8 (N : ℝ) s.selectedPrefix) : ℝ))
  have hOldCeil : retainedTerminalCeiling oldR s.selectedPrefix s.positive
      s.remaining ≤ actualRetainedTerminalCeiling n e q om N c s := by
    unfold actualRetainedTerminalCeiling oldR
    exact le_max_left _ _
  have hNewCeil : retainedTerminalCeiling newR s.selectedPrefix s.positive
      s.remaining ≤ actualRetainedTerminalCeiling n e q om N c s := by
    unfold actualRetainedTerminalCeiling newR
    exact le_max_right _ _
  have hOldSmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * retainedTerminalCeiling oldR s.selectedPrefix s.positive
        s.remaining ≤ X := by
    intro a ha
    exact (Nat.mul_le_mul_left a hOldCeil).trans (hbound a ha)
  have hNewSmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * retainedTerminalCeiling newR s.selectedPrefix s.positive
        s.remaining ≤ X := by
    intro a ha
    exact (Nat.mul_le_mul_left a hNewCeil).trans (hbound a ha)
  have hold := signedTest_highQ_zero_of_retained_ceiling
    oldR N cap X w L F s.selectedPrefix s.remaining s.positive s.mass hOldSmall
  have hnew := signedTest_highQ_zero_of_retained_ceiling
    newR N cap X w L F s.selectedPrefix s.remaining s.positive s.mass hNewSmall
  change signedTest oldR (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining -
    signedTest newR (fun _ : ℕ => (1 : ℝ))
      (attachedLeafTest N cap 1 w L (highQTest X F))
      s.selectedPrefix s.positive s.mass s.remaining = 0
  rw [hold, hnew, sub_self]

end
end ImbalancedChen.P4AOriginalFull87RetainedTerminalCeiling
