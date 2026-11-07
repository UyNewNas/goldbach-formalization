import ImbalancedChen.RenewalFiniteErrorPropagationP5
import ImbalancedChen.P2TableActionSoundness

/-! Source-only, uncompiled. Exact adapter for the per-product floor used
by the actual P2 draft, and common-generation error transport including its
explicit quantization cost. P2TableActionSoundness is a sibling P2 draft
source-root dependency, not an already installed public module. -/

namespace ImbalancedChen.P5RenewalRoundedAction

noncomputable section

open Classical
open scoped BigOperators
open P5RenewalFiniteError

variable {State Act Atom : Type*}

def roundAtom (Q : ℕ) (x : ℝ) : ℝ := (⌊(Q : ℝ) * x⌋ : ℝ) / (Q : ℝ)

/-- Exactly the existing P2 product-floor operation after normalization. -/
theorem roundAtom_eq_actualP2Product (Q : ℕ) (hQ : 0 < Q) (v w : ℤ) :
    roundAtom Q (((v : ℝ) / Q) * ((w : ℝ) / Q)) =
      P2TableActionSourceOnly.roundedProduct Q v w := by
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have harg : (Q : ℝ) * (((v : ℝ) / Q) * ((w : ℝ) / Q)) =
      (v : ℝ) * (w : ℝ) / Q := by field_simp [hQr]; ring
  simp only [roundAtom, P2TableActionSourceOnly.roundedProduct, harg]

/-- No sign assumption is needed for the exact Euclidean floor remainder. -/
theorem roundAtom_error (Q : ℕ) (hQ : 0 < Q) (x : ℝ) :
    0 ≤ x - roundAtom Q x ∧ x - roundAtom Q x ≤ 1 / (Q : ℝ) := by
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hfloor := Int.floor_le ((Q : ℝ) * x)
  have hceil := (Int.lt_floor_add_one ((Q : ℝ) * x)).le
  have hlo := div_le_div_of_nonneg_right hfloor hQr.le
  have hhi := div_le_div_of_nonneg_right hceil hQr.le
  have hcancel : (Q : ℝ) * x / (Q : ℝ) = x := by field_simp [hQr.ne']
  rw [hcancel] at hlo hhi
  rw [add_div] at hhi
  unfold roundAtom
  constructor <;> linarith only [hlo, hhi]

def roundedActionValue (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (Q : ℕ) (X : State → ℝ) (a : Act) : ℝ :=
  base a + ∑ i ∈ atoms a, roundAtom Q (weight a i * X (child a i))

/-- Downward product floors do not create a positive oriented defect error. -/
theorem roundedActionValue_le (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (X : State → ℝ) (a : Act) :
    roundedActionValue atoms child base weight Q X a ≤ actionValue atoms child base weight X a := by
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  have h := (roundAtom_error Q hQ (weight a i * X (child a i))).1
  linarith only [h]

/-- Per-product rounding contributes at most one Q-unit per actual atom. -/
theorem roundedActionValue_error (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (base : Act → ℝ) (weight : Act → Atom → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (X : State → ℝ) (a : Act) :
    |roundedActionValue atoms child base weight Q X a - actionValue atoms child base weight X a| ≤
      ((atoms a).card : ℝ) / (Q : ℝ) := by
  have heq : roundedActionValue atoms child base weight Q X a - actionValue atoms child base weight X a =
      ∑ i ∈ atoms a, (roundAtom Q (weight a i * X (child a i)) - weight a i * X (child a i)) := by
    simp only [roundedActionValue, actionValue, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i ∈ atoms a, |roundAtom Q (weight a i * X (child a i)) - weight a i * X (child a i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ atoms a, 1 / (Q : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := roundAtom_error Q hQ (weight a i * X (child a i))
      apply abs_le.mpr
      constructor <;> linarith only [h.1, h.2]
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- Both the coefficient quadrature error and actual product floors occur
in the explicit local budget. Alternatives still cost only one maximum. -/
theorem rounded_step_error (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (target : Act → State) (bank : List Act)
    (baseA baseB : Act → ℝ) (weightA weightB : Act → Atom → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (X Y : State → ℝ) (E delta : ℝ)
    (hE : 0 ≤ E) (hdelta : 0 ≤ delta)
    (hw : ∀ a ∈ bank, ∀ i ∈ atoms a, 0 ≤ weightA a i)
    (hmass : ∀ a ∈ bank, (∑ i ∈ atoms a, weightA a i) ≤ 12)
    (hXY : ∀ s, |X s - Y s| ≤ E)
    (hlocal : ∀ a ∈ bank,
      localBudget atoms child baseA baseB weightA weightB Y a + ((atoms a).card : ℝ) / Q ≤ delta) :
    ∀ s, |maxActions target X (roundedActionValue atoms child baseA weightA Q X) bank s -
      maxActions target Y (actionValue atoms child baseB weightB Y) bank s| ≤ 12 * E + delta := by
  apply maxActions_lipschitz
  · intro s
    exact (hXY s).trans (by nlinarith only [hE, hdelta])
  · intro a ha
    have hround := roundedActionValue_error atoms child baseA weightA Q hQ X a
    have hsum := actionValue_total_error atoms child baseA baseB weightA weightB X Y a E
      (localBudget atoms child baseA baseB weightA weightB Y a) hE
      (hw a ha) (hmass a ha) hXY le_rfl
    have htri :
        |roundedActionValue atoms child baseA weightA Q X a - actionValue atoms child baseB weightB Y a| ≤
          |roundedActionValue atoms child baseA weightA Q X a - actionValue atoms child baseA weightA X a| +
          |actionValue atoms child baseA weightA X a - actionValue atoms child baseB weightB Y a| := by
      have heq : roundedActionValue atoms child baseA weightA Q X a - actionValue atoms child baseB weightB Y a =
          (roundedActionValue atoms child baseA weightA Q X a - actionValue atoms child baseA weightA X a) +
          (actionValue atoms child baseA weightA X a - actionValue atoms child baseB weightB Y a) := by ring
      rw [heq]
      exact abs_add_le _ _
    linarith only [hround, hsum, htri, hlocal a ha]

/-- For directed lower enclosures of BOTH H and h defects, a product floor
only improves the enclosure. No cardinality/Q term is charged here. -/
theorem rounded_step_oriented
    (atoms : Act → Finset Atom) (child : Act → Atom → State)
    (target : Act → State) (bank : List Act)
    (baseA baseB : Act → ℝ) (weightA weightB : Act → Atom → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (X Y : State → ℝ) (E delta : ℝ)
    (hE : 0 ≤ E) (hdelta : 0 ≤ delta)
    (hw : ∀ a ∈ bank, ∀ i ∈ atoms a, 0 ≤ weightA a i)
    (hmass : ∀ a ∈ bank, (∑ i ∈ atoms a, weightA a i) ≤ 12)
    (hXY : ∀ s, X s ≤ Y s + E)
    (hlocal : ∀ a ∈ bank, localBudget atoms child baseA baseB weightA weightB Y a ≤ delta) :
    ∀ s, maxActions target X (roundedActionValue atoms child baseA weightA Q X) bank s ≤
      maxActions target Y (actionValue atoms child baseB weightB Y) bank s + (12 * E + delta) := by
  apply maxActions_oriented
  · intro s
    exact (hXY s).trans (by nlinarith only [hE, hdelta])
  · intro a ha
    have hround := roundedActionValue_le atoms child baseA weightA Q hQ X a
    have hprop := actionValue_oriented atoms child baseA weightA X Y a E hE (hw a ha) (hmass a ha) hXY
    have hcoef := (abs_le.mp ((actionValue_coefficient_error atoms child baseA baseB
      weightA weightB Y a).trans (hlocal a ha))).2
    linarith only [hround, hprop, hcoef]

def roundedIterate (atoms : ℕ → Act → Finset Atom) (child : ℕ → Act → Atom → State)
    (target : ℕ → Act → State) (bank : ℕ → List Act)
    (base : ℕ → Act → ℝ) (weight : ℕ → Act → Atom → ℝ)
    (Q : ℕ) (seed : State → ℝ) : ℕ → State → ℝ
  | 0 => seed
  | n + 1 => maxActions (target n) (roundedIterate atoms child target bank base weight Q seed n)
      (roundedActionValue (atoms n) (child n) (base n) (weight n) Q
        (roundedIterate atoms child target bank base weight Q seed n)) (bank n)

/-- The actual floor-approximated iteration has the same exact geometric
amplification when its finite floor cost is included locally. -/
theorem roundedIterate_error
    (atoms : ℕ → Act → Finset Atom) (child : ℕ → Act → Atom → State)
    (target : ℕ → Act → State) (bank : ℕ → List Act)
    (baseA baseB : ℕ → Act → ℝ) (weightA weightB : ℕ → Act → Atom → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (seed : State → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hw : ∀ n a, a ∈ bank n → ∀ i ∈ atoms n a, 0 ≤ weightA n a i)
    (hmass : ∀ n a, a ∈ bank n → (∑ i ∈ atoms n a, weightA n a i) ≤ 12)
    (hlocal : ∀ n a, a ∈ bank n →
      localBudget (atoms n) (child n) (baseA n) (baseB n) (weightA n) (weightB n)
        (iterate atoms child target bank baseB weightB seed n) a + ((atoms n a).card : ℝ) / Q ≤ delta)
    (n : ℕ) : ∀ s,
      |roundedIterate atoms child target bank baseA weightA Q seed n s -
        iterate atoms child target bank baseB weightB seed n s| ≤ delta * amplification n := by
  induction n with
  | zero => intro s; simp only [roundedIterate, iterate, sub_self, abs_zero, amplification, mul_zero, le_refl]
  | succ n ih =>
    have hE : 0 ≤ delta * amplification n := mul_nonneg hdelta (amplification_nonneg n)
    have hs := rounded_step_error (atoms n) (child n) (target n) (bank n)
      (baseA n) (baseB n) (weightA n) (weightB n) Q hQ
      (roundedIterate atoms child target bank baseA weightA Q seed n)
      (iterate atoms child target bank baseB weightB seed n)
      (delta * amplification n) delta hE hdelta (hw n) (hmass n) ih (hlocal n)
    intro s
    simpa only [roundedIterate, iterate, amplification, mul_add, mul_one, mul_assoc,
      add_comm, mul_left_comm, mul_comm] using hs s

/-- Fixed finite Q is admissible for oriented lower-defect propagation:
its downward floors need no fictitious arbitrary-precision limit. -/
theorem roundedIterate_oriented_error
    (atoms : ℕ → Act → Finset Atom) (child : ℕ → Act → Atom → State)
    (target : ℕ → Act → State) (bank : ℕ → List Act)
    (baseA baseB : ℕ → Act → ℝ) (weightA weightB : ℕ → Act → Atom → ℝ)
    (Q : ℕ) (hQ : 0 < Q) (seed : State → ℝ) (delta : ℝ) (hdelta : 0 ≤ delta)
    (hw : ∀ n a, a ∈ bank n → ∀ i ∈ atoms n a, 0 ≤ weightA n a i)
    (hmass : ∀ n a, a ∈ bank n → (∑ i ∈ atoms n a, weightA n a i) ≤ 12)
    (hlocal : ∀ n a, a ∈ bank n →
      localBudget (atoms n) (child n) (baseA n) (baseB n) (weightA n) (weightB n)
        (iterate atoms child target bank baseB weightB seed n) a ≤ delta)
    (n : ℕ) : ∀ s,
      roundedIterate atoms child target bank baseA weightA Q seed n s ≤
        iterate atoms child target bank baseB weightB seed n s + delta * amplification n := by
  induction n with
  | zero => intro s; simp only [roundedIterate, iterate, amplification, mul_zero, add_zero, le_refl]
  | succ n ih =>
    have hE : 0 ≤ delta * amplification n := mul_nonneg hdelta (amplification_nonneg n)
    have hs := rounded_step_oriented (atoms n) (child n) (target n) (bank n)
      (baseA n) (baseB n) (weightA n) (weightB n) Q hQ
      (roundedIterate atoms child target bank baseA weightA Q seed n)
      (iterate atoms child target bank baseB weightB seed n)
      (delta * amplification n) delta hE hdelta (hw n) (hmass n) ih (hlocal n)
    intro s
    simpa only [roundedIterate, iterate, amplification, mul_add, mul_one, mul_assoc,
      add_comm, mul_left_comm, mul_comm] using hs s

end

end ImbalancedChen.P5RenewalRoundedAction
