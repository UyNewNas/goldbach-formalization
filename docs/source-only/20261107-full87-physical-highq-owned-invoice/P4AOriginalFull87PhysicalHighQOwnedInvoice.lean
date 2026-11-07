import ImbalancedChen.P4AOriginalFull87HighQCausalLeaf
import ImbalancedChen.P4AOriginalFull87OwnedEighthSource
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No PP level or reserve payment.

The previous high-q witness is existential. Here the full high-q signed
physical sum is transported to the ACTUAL retained terminal list, still
including every small-beta factor, leaf sign and list occurrence. The
original full87 dynamic eighth owner decomposition is then specialized
to the SAME high-q test. An explicit nonnegative absolute invoice is
recorded; its H_N-relative size is not asserted.
-/

namespace ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice

noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource
open P4AOriginalLicensedSixthSignedLedger (physical)
open P4AOriginalFull87OwnedEighthSource
open P4AOriginalFull87LicensedSixthPolicy
open P4AOriginalFull87SourceDictionary (Cell)
open P4AOriginalFull87LicensedSixthRealization (states)

/-- The strict cutoff is imposed on the COMPLETE physical modulus a*b. -/
def highQTest (X : ℕ) (F : ℕ → ℝ) (d : ℕ) : ℝ :=
  if X < d then F d else 0

/-- The actual signed small-beta term of one retained odd-first-exit
leaf. This is a list term, not a new or aggregated sieve coefficient. -/
def leafHighQTerm (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F : ℕ → ℝ) (leaf : FirstExitLeaf ℕ) : ℝ :=
  leaf.value *
    ∑ a ∈ actualSmallRosserSupport N cap w,
      (if leaf.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) *
        highQTest X F (a * leaf.selected.prod)

/-- Absolute charge retains the same actual leaf occurrence, its beta
choice, and its complete modulus a*prod(selected). -/
def leafHighQCharge (N cap : ℕ) (w L : ℝ) (X : ℕ)
    (F : ℕ → ℝ) (leaf : FirstExitLeaf ℕ) : ℝ :=
  |leaf.value| *
    ∑ a ∈ actualSmallRosserSupport N cap w,
      |if leaf.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a| *
        (if X < a * leaf.selected.prod then
           |F (a * leaf.selected.prod)| else 0)

/-- Not a second generic formal coefficient: the finite physical high-q
sum equals the literal first-exit LEAF sum, with original signs.
The sole structural premise is the actual policy's even retention. -/
theorem high_q_physical_eq_actual_leaf_sum
    (R : Bool → List ℕ → Bool) (heven : ∀ pre, R true pre = true)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical R N cap w z L (highQTest X F) =
      ((firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
          [] true 1 (roughPrimeUniverse N cap w z)).map
        (leafHighQTerm N cap w L X F)).sum := by
  have h := physical_test_eq_signedTest R heven N cap 1 w z L (highQTest X F)
  simp only [one_mul] at h
  rw [signedTest_eq_leaves] at h
  simpa [physical, leafHighQTerm, attachedLeafTest, highQTest] using h

/-- A leaf with no actual small*rough product beyond X contributes
exactly zero; this is an arithmetic statement, not a geometric null set. -/
theorem leaf_high_q_zero_of_no_large_product
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ)
    (hsmall : ∀ a ∈ actualSmallRosserSupport N cap w,
      a * leaf.selected.prod ≤ X) :
    leafHighQTerm N cap w L X F leaf = 0 := by
  unfold leafHighQTerm
  have hzero : (∑ a ∈ actualSmallRosserSupport N cap w,
      (if leaf.positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) *
        highQTest X F (a * leaf.selected.prod)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hnot : ¬ X < a * leaf.selected.prod :=
      Nat.not_lt.mpr (hsmall a ha)
    simp [highQTest, hnot]
  rw [hzero, mul_zero]

private theorem list_abs_sum_le_charge {α : Type*}
    (xs : List α) (f charge : α → ℝ) :
    (∀ a ∈ xs, |f a| ≤ charge a) →
      |(xs.map f).sum| ≤ (xs.map charge).sum := by
  induction xs with
  | nil =>
      intro _
      simp
  | cons x tail ih =>
      intro h
      have hx : |f x| ≤ charge x := h x (by simp)
      have ht : ∀ y ∈ tail, |f y| ≤ charge y := by
        intro y hy
        exact h y (by simp [hy])
      have htail := ih ht
      simp only [List.map_cons, List.sum_cons]
      calc
        |f x + (tail.map f).sum| ≤
            |f x| + |(tail.map f).sum| := abs_add _ _
        _ ≤ charge x + (tail.map charge).sum := add_le_add hx htail

/-- Exact one-leaf absolute invoice, including the signed choice of
the genuine small Rosser beta and the strict FULL-q indicator. -/
theorem abs_leaf_high_q_term_le_charge
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (leaf : FirstExitLeaf ℕ) :
    |leafHighQTerm N cap w L X F leaf| ≤
      leafHighQCharge N cap w L X F leaf := by
  unfold leafHighQTerm leafHighQCharge
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg leaf.value)
  calc
    |∑ a ∈ actualSmallRosserSupport N cap w,
        (if leaf.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) *
          highQTest X F (a * leaf.selected.prod)| ≤
      ∑ a ∈ actualSmallRosserSupport N cap w,
        |(if leaf.positive then actualSmallRosserPlus N cap w L a
          else actualSmallRosserMinus N cap w L a) *
          highQTest X F (a * leaf.selected.prod)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ actualSmallRosserSupport N cap w,
          |if leaf.positive then actualSmallRosserPlus N cap w L a
           else actualSmallRosserMinus N cap w L a| *
            (if X < a * leaf.selected.prod then
               |F (a * leaf.selected.prod)| else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hcut : X < a * leaf.selected.prod
        · simp [highQTest, hcut, abs_mul]
        · simp [highQTest, hcut]

/-- The ACTUAL physical high-q tail is charged once, leaf by leaf.
No rank/cap envelope is used as a substitute for this finite mass. -/
theorem abs_high_q_physical_le_leaf_charge
    (R : Bool → List ℕ → Bool) (heven : ∀ pre, R true pre = true)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |physical R N cap w z L (highQTest X F)| ≤
      ((firstExitRetainedLeaves R (fun _ : ℕ => (1 : ℝ))
          [] true 1 (roughPrimeUniverse N cap w z)).map
        (leafHighQCharge N cap w L X F)).sum := by
  rw [high_q_physical_eq_actual_leaf_sum R heven N cap w z L X F]
  exact list_abs_sum_le_charge _ _ _
    (fun leaf _ => abs_leaf_high_q_term_le_charge N cap w L X F leaf)

/-- The high-q *difference* is supported on the original full87
owned/trimmed eighth frontier. Unowned and inherited ordinary branches
are never equipped with an unrelated changed mask. -/
theorem full87_high_q_gain_eq_owned_sources
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    physical (sixthPolicy n e q om (N : ℝ)) N cap w z L (highQTest X F) -
      physical (policy delta n e q om (N : ℝ)) N cap w z L
        (highQTest X F) =
      ∑ c : Cell, ownedSource delta n e q om N cap w z L
        (highQTest X F) c :=
  physical_saving_eq_owned_sources delta n e q om N cap w z L (highQTest X F)

/-- Absolute value is only taken after the actual signed ordinary
old-minus-new difference at each SAME eighth occurrence is computed. -/
def ownedHighQCharge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (c : Cell) : ℝ :=
  ((states delta n e q om N cap w z (fun _ : ℕ => (1 : ℝ)) c).map
    (fun s => |ordinarySaving n e q om N cap w L
      (highQTest X F) c s|)).sum

/-- The exact actual-owner invoice: no monotonicity of signed saving,
no collapsed occurrence, no disappearing high-q tail. -/
theorem abs_full87_high_q_gain_le_owned_charge
    (delta : ℝ) (n : ℕ) (e : ℚ) (q : ℕ) (om : ℝ)
    (N cap : ℕ) (w z L : ℝ) (X : ℕ) (F : ℕ → ℝ) :
    |physical (sixthPolicy n e q om (N : ℝ)) N cap w z L
        (highQTest X F) -
      physical (policy delta n e q om (N : ℝ)) N cap w z L
        (highQTest X F)| ≤
      ∑ c : Cell, ownedHighQCharge delta n e q om N cap w z L X F c := by
  rw [full87_high_q_gain_eq_owned_sources]
  calc
    |∑ c : Cell, ownedSource delta n e q om N cap w z L
        (highQTest X F) c| ≤
      ∑ c : Cell, |ownedSource delta n e q om N cap w z L
        (highQTest X F) c| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : Cell, ownedHighQCharge delta n e q om N cap w z L X F c := by
        apply Finset.sum_le_sum
        intro c _
        unfold ownedSource ownedHighQCharge
        exact list_abs_sum_le_charge _ _ _
          (fun s _ => le_refl _)

end
end ImbalancedChen.P4AOriginalFull87PhysicalHighQOwnedInvoice
