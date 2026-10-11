import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Finite odd-first-exit identity

The physical upper weight in the current manuscript begins with a finite
tree.  Every even-rank prefix is retained, while an odd-rank prefix may be
the first rejected prefix.  Divisors below a first exit remain unrestricted;
their alternating sum is the residual Euler product.

This file proves that algebra for an arbitrary finite ordered universe and an
arbitrary odd-rank retention policy.  It does not identify the policy with
the manuscript's causal boxes, estimate its density, or attach the
small-prime fundamental-lemma weights.

The Boolean `positive` records the sign of the coefficient of the already
selected prefix: `true` is even rank and `false` is odd rank.  The remaining
list is processed from larger to smaller labels.  Thus when a new odd prefix
is rejected, the unprocessed list is exactly the set of smaller labels in
the residual Euler product.
-/

namespace ImbalancedChen

noncomputable section

/-- A nonnegative mass with the alternating sign of the selected prefix. -/
def signedTreeCoefficient (positive : Bool) (mass : ℝ) : ℝ :=
  if positive then mass else -mass

@[simp] theorem signedTreeCoefficient_true (mass : ℝ) :
    signedTreeCoefficient true mass = mass := rfl

@[simp] theorem signedTreeCoefficient_false (mass : ℝ) :
    signedTreeCoefficient false mass = -mass := rfl

/-- Selecting one more label flips the Möbius sign and multiplies the mass
by that label's local weight. -/
theorem signedTreeCoefficient_not_mul
    (positive : Bool) (mass weight : ℝ) :
    signedTreeCoefficient (!positive) (mass * weight) =
      -signedTreeCoefficient positive mass * weight := by
  cases positive <;> simp [signedTreeCoefficient] <;> ring

/-- Sum of all retained extensions of one already-retained prefix.

`retained newSign newPrefix = true` means that the selected branch remains
inside the tree.  If it is false, that branch contributes no retained
coefficient and becomes a first exit. -/
def firstExitRetainedPolynomial {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => signedTreeCoefficient positive mass
  | p :: ps =>
      firstExitRetainedPolynomial retained h prefix positive mass ps +
        if retained (!positive) (p :: prefix) = true then
          firstExitRetainedPolynomial retained h (p :: prefix) (!positive)
            (mass * h p) ps
        else 0

/-- The signed correction contributed by all first exits below a retained
prefix.  At an exit, all later smaller labels are free, hence the product of
`1 - h` over the unprocessed tail. -/
def firstExitCorrection {α : Type*}
    (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix : List α) (positive : Bool) (mass : ℝ) : List α → ℝ
  | [] => 0
  | p :: ps =>
      firstExitCorrection retained h prefix positive mass ps +
        if retained (!positive) (p :: prefix) = true then
          firstExitCorrection retained h (p :: prefix) (!positive)
            (mass * h p) ps
        else
          -signedTreeCoefficient (!positive) (mass * h p) *
            (ps.map fun q => 1 - h q).prod

/-- Exact finite product-plus-first-exit identity, before imposing that first
exits have odd rank. -/
theorem firstExitRetainedPolynomial_eq_product_add_correction
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ) :
    firstExitRetainedPolynomial retained h prefix positive mass remaining =
      signedTreeCoefficient positive mass *
          (remaining.map fun p => 1 - h p).prod +
        firstExitCorrection retained h prefix positive mass remaining := by
  induction remaining generalizing prefix positive mass with
  | nil => simp [firstExitRetainedPolynomial, firstExitCorrection]
  | cons p ps ih =>
      simp only [firstExitRetainedPolynomial, firstExitCorrection,
        List.map_cons, List.prod_cons]
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [if_pos hr, ih, ih, signedTreeCoefficient_not_mul]
        ring
      · rw [if_neg hr, ih, signedTreeCoefficient_not_mul]
        ring

/-- A retention policy with no even-rank exit.  At odd rank `retainOdd`
decides whether the branch continues; at even rank it always continues. -/
def oddFirstExitPolicy {α : Type*}
    (retainOdd : List α → Bool) (positive : Bool) (prefix : List α) : Bool :=
  positive || retainOdd prefix

@[simp] theorem oddFirstExitPolicy_even {α : Type*}
    (retainOdd : List α → Bool) (prefix : List α) :
    oddFirstExitPolicy retainOdd true prefix = true := by
  simp [oddFirstExitPolicy]

/-- The retained polynomial of an odd-first-exit tree, starting at its root. -/
def oddFirstExitRetainedPolynomial {α : Type*}
    (retainOdd : List α → Bool) (h : α → ℝ) (universe : List α) : ℝ :=
  firstExitRetainedPolynomial (oddFirstExitPolicy retainOdd) h [] true 1 universe

/-- The sum of the residual Euler products at all odd first exits. -/
def oddFirstExitCorrection {α : Type*}
    (retainOdd : List α → Bool) (h : α → ℝ) (universe : List α) : ℝ :=
  firstExitCorrection (oddFirstExitPolicy retainOdd) h [] true 1 universe

/-- The manuscript's finite identity in its root form: retained Möbius
polynomial equals the complete Euler product plus the odd-first-exit sum. -/
theorem oddFirstExitRetainedPolynomial_eq_product_add_exits
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α) :
    oddFirstExitRetainedPolynomial retainOdd h universe =
      (universe.map fun p => 1 - h p).prod +
        oddFirstExitCorrection retainOdd h universe := by
  simpa [oddFirstExitRetainedPolynomial, oddFirstExitCorrection] using
    firstExitRetainedPolynomial_eq_product_add_correction
      (oddFirstExitPolicy retainOdd) h [] universe true 1

/-- A product of nonnegative factors indexed by a list is nonnegative. -/
theorem list_prod_nonneg_of_mem {α : Type*} (f : α → ℝ) (xs : List α)
    (hf : ∀ x ∈ xs, 0 ≤ f x) : 0 ≤ (xs.map f).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_nonneg (hf x (by simp))
        (ih fun y hy => hf y (by simp [hy]))

/-- Every first-exit correction is nonnegative when local weights lie in
`[0,1]` and even-rank prefixes are retained. -/
theorem firstExitCorrection_nonneg_of_even_retained
    {α : Type*} (retained : Bool → List α → Bool) (h : α → ℝ)
    (prefix remaining : List α) (positive : Bool) (mass : ℝ)
    (heven : ∀ pre, retained true pre = true)
    (hmass : 0 ≤ mass)
    (hh : ∀ p ∈ remaining, 0 ≤ h p ∧ h p ≤ 1) :
    0 ≤ firstExitCorrection retained h prefix positive mass remaining := by
  induction remaining generalizing prefix positive mass with
  | nil => simp [firstExitCorrection]
  | cons p ps ih =>
      have hp : 0 ≤ h p ∧ h p ≤ 1 := hh p (by simp)
      have hps : ∀ q ∈ ps, 0 ≤ h q ∧ h q ≤ 1 := by
        intro q hq
        exact hh q (by simp [hq])
      have hleft :
          0 ≤ firstExitCorrection retained h prefix positive mass ps :=
        ih prefix positive mass hmass hps
      have hright :
          0 ≤ firstExitCorrection retained h (p :: prefix) (!positive)
            (mass * h p) ps :=
        ih (p :: prefix) (!positive) (mass * h p)
          (mul_nonneg hmass hp.1) hps
      have hprod : 0 ≤ (ps.map fun q => 1 - h q).prod :=
        list_prod_nonneg_of_mem (fun q => 1 - h q) ps
          (fun q hq => sub_nonneg.mpr (hps q hq).2)
      simp only [firstExitCorrection]
      by_cases hr : retained (!positive) (p :: prefix) = true
      · rw [if_pos hr]
        exact add_nonneg hleft hright
      · rw [if_neg hr]
        cases positive with
        | false =>
            exact False.elim (hr (heven (p :: prefix)))
        | true =>
            simpa [signedTreeCoefficient] using
              add_nonneg hleft (mul_nonneg (mul_nonneg hmass hp.1) hprod)

/-- Odd first exits give a nonnegative residual sum. -/
theorem oddFirstExitCorrection_nonneg
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α)
    (hh : ∀ p ∈ universe, 0 ≤ h p ∧ h p ≤ 1) :
    0 ≤ oddFirstExitCorrection retainOdd h universe := by
  unfold oddFirstExitCorrection
  exact firstExitCorrection_nonneg_of_even_retained
    (oddFirstExitPolicy retainOdd) h [] universe true 1
    (fun pre => oddFirstExitPolicy_even retainOdd pre) zero_le_one hh

/-- Consequently the retained tree polynomial majorizes the complete Euler
product for every choice of local weights in `[0,1]`. -/
theorem product_le_oddFirstExitRetainedPolynomial
    {α : Type*} (retainOdd : List α → Bool) (h : α → ℝ)
    (universe : List α)
    (hh : ∀ p ∈ universe, 0 ≤ h p ∧ h p ≤ 1) :
    (universe.map fun p => 1 - h p).prod ≤
      oddFirstExitRetainedPolynomial retainOdd h universe := by
  rw [oddFirstExitRetainedPolynomial_eq_product_add_exits]
  exact le_add_of_nonneg_right
    (oddFirstExitCorrection_nonneg retainOdd h universe hh)

/-- Literal divisibility indicator on every integer, including zero and
negative integers. -/
def integerDivisorIndicator (n : ℤ) (p : ℕ) : ℝ :=
  if (p : ℤ) ∣ n then 1 else 0

/-- The complete finite roughness indicator written as an Euler product. -/
def finiteIntegerRoughIndicator (universe : List ℕ) (n : ℤ) : ℝ :=
  (universe.map fun p => 1 - integerDivisorIndicator n p).prod

/-- The Euler product is literally the `0`/`1` indicator that no member of
the finite universe divides `n`.  No positivity hypothesis on `n` is used. -/
theorem finiteIntegerRoughIndicator_eq_indicator
    (universe : List ℕ) (n : ℤ) :
    finiteIntegerRoughIndicator universe n =
      if ∀ p ∈ universe, ¬(p : ℤ) ∣ n then 1 else 0 := by
  induction universe with
  | nil => simp [finiteIntegerRoughIndicator]
  | cons p ps ih =>
      rw [finiteIntegerRoughIndicator, List.map_cons, List.prod_cons]
      change (1 - integerDivisorIndicator n p) *
          finiteIntegerRoughIndicator ps n = _
      rw [ih]
      by_cases hp : (p : ℤ) ∣ n <;>
        simp [integerDivisorIndicator, hp]

/-- Equivalent proposition-level characterization of the finite roughness
indicator. -/
theorem finiteIntegerRoughIndicator_eq_one_iff
    (universe : List ℕ) (n : ℤ) :
    finiteIntegerRoughIndicator universe n = 1 ↔
      ∀ p ∈ universe, ¬(p : ℤ) ∣ n := by
  rw [finiteIntegerRoughIndicator_eq_indicator]
  by_cases hrough : ∀ p ∈ universe, ¬(p : ℤ) ∣ n <;> simp [hrough]

/-- Taking `h(p)=1_{p∣n}` gives the manuscript's pointwise rough-indicator
majorant for every integer `n`, without excluding `0` or negative inputs. -/
theorem finiteIntegerRoughIndicator_le_oddFirstExitRetainedPolynomial
    (retainOdd : List ℕ → Bool) (universe : List ℕ) (n : ℤ) :
    finiteIntegerRoughIndicator universe n ≤
      oddFirstExitRetainedPolynomial retainOdd
        (integerDivisorIndicator n) universe := by
  apply product_le_oddFirstExitRetainedPolynomial
  intro p hp
  by_cases hpn : (p : ℤ) ∣ n <;>
    simp [integerDivisorIndicator, hpn]

/-- The pointwise majorant with the roughness indicator displayed explicitly,
matching the manuscript's statement for every integer. -/
theorem integerRoughIndicator_le_oddFirstExitRetainedPolynomial
    (retainOdd : List ℕ → Bool) (universe : List ℕ) (n : ℤ) :
    (if ∀ p ∈ universe, ¬(p : ℤ) ∣ n then 1 else 0 : ℝ) ≤
      oddFirstExitRetainedPolynomial retainOdd
        (integerDivisorIndicator n) universe := by
  rw [← finiteIntegerRoughIndicator_eq_indicator]
  exact finiteIntegerRoughIndicator_le_oddFirstExitRetainedPolynomial
    retainOdd universe n

end

end ImbalancedChen
