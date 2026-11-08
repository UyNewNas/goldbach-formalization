import ImbalancedChen.P4AOriginalFull87FirstDisagreementTerminalL1
import Mathlib.Tactic

/-!
SOURCE_ONLY / UNEVALUATED / UNCOMPILED.

The previous true first-disagreement terminal L1 invoice still ranged over
all original stopped terminals. This packet uses the EXISTING active-level
property of the actual small Rosser beta: beta(a) != 0 implies (a : R) < L.
Together with the literal strict physical test X < a * selected.prod, this
proves that only terminals with (X : R) < L * selected.prod can contribute.
Both equalities are signed and preserve the original terminal multiplicity,
producer policy, sign-selected beta and post-candidate carrier. There is no
claim that the resulting high-product population is small versus H_N.
-/

namespace ImbalancedChen.P4AOriginalFull87ActiveLevelHighProduct
noncomputable section
open scoped Classical BigOperators
open P1Pair12RetainedSignedSource (stoppedTest attachedLeafTest)
open P4AOriginalFull87PhysicalHighQOwnedInvoice (highQTest)
open P4AOriginalFull87StoppedTerminalPopulation
  (StoppedTerminal stoppedTerminals stoppedPhysicalTerm
   actual_stopped_eq_physical_terminal_sum)
open P4AOriginalFull87FirstDisagreementTerminalL1
  (terminalFullQCharge abs_stopped_physical_term_le_fullq_charge
   stoppedTerminalL1 abs_stopped_test_le_terminal_l1)

/-- A nonzero ORIGINAL sign-selected beta is supported strictly below
its original Rosser level L; it is not just a divisor of the display set. -/
private theorem active_sign_selected_beta_lt_level
    (N cap a : ℕ) (w L : ℝ) (positive : Bool)
    (hbeta :
      (if positive then actualSmallRosserPlus N cap w L a
       else actualSmallRosserMinus N cap w L a) ≠ 0) :
    (a : ℝ) < L := by
  cases hs : positive with
  | false =>
      have hm : actualSmallRosserMinus N cap w L a ≠ 0 := by
        simpa [hs] using hbeta
      exact (actualSmallRosserMinus_active hm).2.1
  | true =>
      have hp : actualSmallRosserPlus N cap w L a ≠ 0 := by
        simpa [hs] using hbeta
      exact (actualSmallRosserPlus_active hp).2.1

/-- REAL high-product cutoff: if the selected word is too small, then
EVERY actual full-q summand is zero (including each sign separately).
No assumption about the positivity of L or selected.prod is needed. -/
theorem terminal_fullq_charge_zero_of_below_active_level
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (t : StoppedTerminal ℕ)
    (hsmall : L * (t.selected.prod : ℝ) ≤ (X : ℝ)) :
    terminalFullQCharge N cap w L X F t = 0 := by
  unfold terminalFullQCharge
  have hsum :
      (∑ a ∈ actualSmallRosserSupport N cap w,
        |if t.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a| *
          (if X < a * t.selected.prod then
             |F (a * t.selected.prod)| else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_cases hb :
        (if t.positive then actualSmallRosserPlus N cap w L a
         else actualSmallRosserMinus N cap w L a) = 0
    · simp [hb]
    · have hlt : (a : ℝ) < L :=
        active_sign_selected_beta_lt_level N cap a w L t.positive hb
      have hmul :
          ((a * t.selected.prod : ℕ) : ℝ) ≤
            L * (t.selected.prod : ℝ) := by
        rw [Nat.cast_mul]
        exact mul_le_mul_of_nonneg_right (le_of_lt hlt)
          (Nat.cast_nonneg _)
      have hnot : ¬ X < a * t.selected.prod := by
        intro hx
        have hxreal : (X : ℝ) < ((a * t.selected.prod : ℕ) : ℝ) := by
          exact_mod_cast hx
        exact (not_lt_of_ge (hmul.trans hsmall)) hxreal
      simp [hnot]
  simp [hsum]

/-- Not merely the L1 bound: the original SIGNED physical terminal itself
vanishes below the active level, even if the displayed support is huge. -/
theorem stopped_physical_term_zero_of_below_active_level
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (t : StoppedTerminal ℕ)
    (hsmall : L * (t.selected.prod : ℝ) ≤ (X : ℝ)) :
    stoppedPhysicalTerm N cap w L X F t = 0 := by
  have hcharge := terminal_fullq_charge_zero_of_below_active_level
    N cap w L X F t hsmall
  have hle := abs_stopped_physical_term_le_fullq_charge
    N cap w L X F t
  rw [hcharge] at hle
  have habs : |stoppedPhysicalTerm N cap w L X F t| = 0 :=
    le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp habs

/-- Actual stopped terminal occurrences that can contribute to a high-q
physical test. Filter AFTER the original producer creates its complete
terminal population, so no parent or carrier is silently substituted. -/
def highProductStoppedTerminals
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (L : ℝ) (X : ℕ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) : List (StoppedTerminal ℕ) :=
  (stoppedTerminals 8 R h pre positive mass remaining).filter
    (fun t => (X : ℝ) < L * (t.selected.prod : ℝ))

private theorem list_map_sum_eq_map_filter_if_zero {α : Type*}
    (xs : List α) (f : α → ℝ) (Q : α → Prop)
    [DecidablePred Q] (hzero : ∀ x, ¬ Q x → f x = 0) :
    (xs.map f).sum = ((xs.filter Q).map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : Q x
      · simp [hx, ih]
      · simp [hx, hzero x hx, ih]

/-- Exact signed finite identity: ALL terminals with selected-product
below the real active-level threshold are removable without numerical error.
This does not replace one original producer by the other. -/
theorem actual_stopped_eq_high_product_terminal_sum
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) :
    stoppedTest 8 R h
        (attachedLeafTest N cap 1 w L (highQTest X F))
        pre positive mass remaining =
      ((highProductStoppedTerminals R h L X
        pre positive mass remaining).map
        (stoppedPhysicalTerm N cap w L X F)).sum := by
  rw [actual_stopped_eq_physical_terminal_sum]
  unfold highProductStoppedTerminals
  apply list_map_sum_eq_map_filter_if_zero
  intro t ht
  exact stopped_physical_term_zero_of_below_active_level
    N cap w L X F t (le_of_not_gt ht)

/-- The original first-disagreement L1 charge is EXACTLY concentrated
on the high-selected-product original terminal occurrences. No surplus
invoice or second payment is introduced. -/
theorem stopped_terminal_l1_eq_high_product_invoice
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ) :
    stoppedTerminalL1 R h N cap w L X F
      pre positive mass remaining =
      ((highProductStoppedTerminals R h L X
        pre positive mass remaining).map
        (terminalFullQCharge N cap w L X F)).sum := by
  unfold stoppedTerminalL1 highProductStoppedTerminals
  apply list_map_sum_eq_map_filter_if_zero
  intro t ht
  exact terminal_fullq_charge_zero_of_below_active_level
    N cap w L X F t (le_of_not_gt ht)

private theorem list_map_sum_zero_of_each_zero {α : Type*}
    (xs : List α) (f : α → ℝ) :
    (∀ x ∈ xs, f x = 0) → (xs.map f).sum = 0 := by
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
      intro hz
      have hx : f x = 0 := hz x (by simp)
      have htail : (xs.map f).sum = 0 := ih (by
        intro y hy
        exact hz y (by simp [hy]))
      simp [hx, htail]

/-- Every nonzero ORIGINAL signed stopped producer must contain a REAL
high-product occurrence; the existential quantifier ranges over the
producer's own original stopped population, not a synthetic box. -/
theorem nonzero_stopped_has_high_product_terminal
    (R : Bool → List ℕ → Bool) (h : ℕ → ℝ)
    (N cap : ℕ) (w L : ℝ) (X : ℕ) (F : ℕ → ℝ)
    (pre : List ℕ) (positive : Bool) (mass : ℝ)
    (remaining : List ℕ)
    (hnz : stoppedTest 8 R h
      (attachedLeafTest N cap 1 w L (highQTest X F))
      pre positive mass remaining ≠ 0) :
    ∃ t ∈ stoppedTerminals 8 R h pre positive mass remaining,
      (X : ℝ) < L * (t.selected.prod : ℝ) := by
  classical
  by_contra hnone
  have hsmall :
      ∀ t ∈ stoppedTerminals 8 R h pre positive mass remaining,
        L * (t.selected.prod : ℝ) ≤ (X : ℝ) := by
    intro t ht
    by_contra hnot
    apply hnone
    exact ⟨t, ht, lt_of_not_ge hnot⟩
  rw [actual_stopped_eq_physical_terminal_sum] at hnz
  have hz :
      ((stoppedTerminals 8 R h pre positive mass remaining).map
        (stoppedPhysicalTerm N cap w L X F)).sum = 0 := by
    apply list_map_sum_zero_of_each_zero
    intro t ht
    exact stopped_physical_term_zero_of_below_active_level
      N cap w L X F t (hsmall t ht)
  exact hnz hz

end
end ImbalancedChen.P4AOriginalFull87ActiveLevelHighProduct
