import ImbalancedChen.P5ZU1011OriginalSixteenPolicyBank
import ImbalancedChen.P2OriginalFourthCapProducerInterface

/-!
# Whole-box rational certificates for the original sixteen-policy bank

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

This is the ORIGINAL typed bank: mask IDs 1,...,15 and the distinct W
policy ID16. Rational affine endpoint evaluation is reused from the
existing P2 fourth-cap producer interface. Only the original sixteen
circuits and their strict eligibility tests are new here.

For a mask cap min(A(s),C(s)), BOTH affine branches are enclosed before
taking min. Thus the increasing A branch takes lower/upper selected-mass
endpoints and the decreasing C branch takes the opposite endpoints.
The W circuit uses v2 with coefficient -3/8 and retains BOTH extra gates.
Every certificate is a finite rational test; no cell interval, eligibility
conclusion, analytic kernel bound, or saved endpoint is a hypothesis.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.BoxCertificates

noncomputable section

open Set
open scoped BigOperators
open U11Integral
open P2OriginalFourthCapProducerInterface

abbrev RationalPoint := Fin 4 → ℚ

structure Box where
  lo : RationalPoint
  hi : RationalPoint

def Box.Valid (B : Box) : Prop := ∀ i, B.lo i ≤ B.hi i

def Box.region (B : Box) : Set LogFour :=
  {v | (∀ i, (B.lo i : ℝ) ≤ v i) ∧ ∀ i, v i ≤ (B.hi i : ℝ)}

/-- The two actual cap branches. W deliberately has the same circuit
for either side, matching the original dictionary's single owner. -/
def capPiece (p : Policy) (left : Bool) : Affine :=
  if p.val < 15 then
    if left then ⟨1 / 2, fun i => if Selected p i then 1 / 2 else 0⟩
    else ⟨57 / 64, fun i => if Selected p i then -3 / 2 else 0⟩
  else ⟨153 / 256, fun i => if i = 2 then -3 / 8 else 0⟩

def fullSquarePiece (j : Fin 4) : Affine :=
  ⟨0, fun i => (if i.val < j.val then 1 else 0) + (if i = j then 2 else 0)⟩

def selectedSquarePiece (p : Policy) (j : Fin 4) : Affine :=
  ⟨0, fun i => (if Selected p i then 1 else 0) +
    (if i.val < j.val ∧ ¬Selected p i then 1 else 0) + (if i = j then 2 else 0)⟩

def prefixPiece : Affine := ⟨0, fun _ => 1⟩

def wExtraPiece : Affine := ⟨1 / 2, fun i => if i = 0 then 1 / 2 else 0⟩

private theorem selected_scaled_sum (p : Policy) (c : ℚ) (v : LogFour) :
    (∑ i : Fin 4, ((if Selected p i then c else 0 : ℚ) : ℝ) * v i) =
      (c : ℝ) * selectedMass p v := by
  rw [selectedMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : Selected p i <;> simp [hs]

theorem capPiece_eval (p : Policy) (left : Bool) (v : LogFour) :
    (capPiece p left).eval v =
      if p.val < 15 then
        if left then (1 + selectedMass p v) / 2
        else 57 / 64 - (3 / 2 : ℝ) * selectedMass p v
      else 153 / 256 - (3 / 8 : ℝ) * v 2 := by
  by_cases hp : p.val < 15
  · cases left <;>
      simp only [capPiece, hp, if_true, Bool.false_eq_true, if_false,
        Affine.eval, selected_scaled_sum, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_neg, Rat.cast_one]
    <;> ring
  · simp [capPiece, hp, Affine.eval, ite_mul]
    <;> ring

theorem cap_eq_piece_min (p : Policy) (v : LogFour) :
    cap p v = if p.val < 15 then
      min ((capPiece p true).eval v) ((capPiece p false).eval v)
      else (capPiece p true).eval v := by
  by_cases hp : p.val < 15 <;> simp [cap, capPiece_eval, hp]

theorem fullSquarePiece_eval (j : Fin 4) (v : LogFour) :
    (fullSquarePiece j).eval v = fullSquare j v := by
  simp only [fullSquarePiece, Affine.eval, Rat.cast_zero, zero_add,
    Rat.cast_add, add_mul, Finset.sum_add_distrib, fullSquare]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : i.val < j.val <;> simp [hij]
  · simp [ite_mul]

theorem selectedSquarePiece_eval (p : Policy) (j : Fin 4) (v : LogFour) :
    (selectedSquarePiece p j).eval v = selectedSquare p j v := by
  simp only [selectedSquarePiece, Affine.eval, Rat.cast_zero, zero_add,
    Rat.cast_add, add_mul, Finset.sum_add_distrib, selectedSquare, selectedMass]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hs : Selected p i <;> simp [hs]
    · apply Finset.sum_congr rfl
      intro i hi
      by_cases hs : i.val < j.val ∧ ¬Selected p i <;> simp [hs]
  · simp [ite_mul]

theorem prefixPiece_eval (v : LogFour) :
    prefixPiece.eval v = U11SelectedLargest.prefixSum v := by
  simp [prefixPiece, Affine.eval, Fin.sum_univ_succ, U11SelectedLargest.prefixSum]
  <;> ring

theorem wExtraPiece_eval (v : LogFour) :
    wExtraPiece.eval v = (1 + v 0) / 2 := by
  simp [wExtraPiece, Affine.eval, ite_mul]
  <;> ring

def selectedMassQ (p : Policy) (q : RationalPoint) : ℚ :=
  ∑ i : Fin 4, if Selected p i then q i else 0

theorem selectedMassQ_cast (p : Policy) (q : RationalPoint) :
    (selectedMassQ p q : ℝ) = selectedMass p (fun i => (q i : ℝ)) := by
  simp only [selectedMassQ, selectedMass, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hs : Selected p i <;> simp [hs]

theorem selectedMass_mono (p : Policy) {v w : LogFour}
    (h : ∀ i, v i ≤ w i) : selectedMass p v ≤ selectedMass p w := by
  unfold selectedMass
  apply Finset.sum_le_sum
  intro i hi
  by_cases hs : Selected p i
  · simpa only [if_pos hs] using h i
  · simp only [if_neg hs, le_refl]

theorem selectedMass_bounds (p : Policy) (B : Box) {v : LogFour} (hv : v ∈ B.region) :
    (selectedMassQ p B.lo : ℝ) ≤ selectedMass p v ∧
      selectedMass p v ≤ (selectedMassQ p B.hi : ℝ) := by
  rw [selectedMassQ_cast, selectedMassQ_cast]
  exact ⟨selectedMass_mono p hv.1, selectedMass_mono p hv.2⟩

/-- The min endpoints remain crossed on a box meeting the cap ridge. -/
def capLower (p : Policy) (B : Box) : ℚ :=
  if p.val < 15 then min ((1 + selectedMassQ p B.lo) / 2)
    (57 / 64 - (3 / 2 : ℚ) * selectedMassQ p B.hi)
  else 153 / 256 - (3 / 8 : ℚ) * B.hi 2

def capUpper (p : Policy) (B : Box) : ℚ :=
  if p.val < 15 then min ((1 + selectedMassQ p B.hi) / 2)
    (57 / 64 - (3 / 2 : ℚ) * selectedMassQ p B.lo)
  else 153 / 256 - (3 / 8 : ℚ) * B.lo 2

def residualLower (p : Policy) (B : Box) : ℚ :=
  capLower p B - prefixPiece.upper B.lo B.hi

def residualUpper (p : Policy) (B : Box) : ℚ :=
  capUpper p B - prefixPiece.lower B.lo B.hi

/-- The increasing A branch and decreasing C branch use opposite corners.
Both min branches remain present on a box crossing their common ridge. -/
theorem cap_bounds (p : Policy) (B : Box) {v : LogFour} (hv : v ∈ B.region) :
    (capLower p B : ℝ) ≤ cap p v ∧ cap p v ≤ (capUpper p B : ℝ) := by
  have hs := selectedMass_bounds p B hv
  by_cases hp : p.val < 15
  · simp only [capLower, capUpper, cap, if_pos hp, Rat.cast_min,
      Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    constructor
    · exact min_le_min (by linarith only [hs.1]) (by linarith only [hs.2])
    · exact min_le_min (by linarith only [hs.2]) (by linarith only [hs.1])
  · simp only [capLower, capUpper, cap, if_neg hp,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
    constructor <;> linarith only [hv.1 2, hv.2 2]

theorem residual_bounds (p : Policy) (B : Box) {v : LogFour} (hv : v ∈ B.region) :
    (residualLower p B : ℝ) ≤ typedResidual p v ∧
      typedResidual p v ≤ (residualUpper p B : ℝ) := by
  have hc := cap_bounds p B hv
  have hL := prefixPiece.lower_le_eval B.lo B.hi v hv.1 hv.2
  have hU := prefixPiece.eval_le_upper B.lo B.hi v hv.1 hv.2
  rw [prefixPiece_eval] at hL hU
  simp only [residualLower, residualUpper, Rat.cast_sub, typedResidual]
  exact ⟨sub_le_sub hc.1 hU, sub_le_sub hc.2 hL⟩

/-- All strict tests use upper left-hand sides against the lower cap.
W retains both its original extra-A gate and x<25/128 gate. -/
def WholeBoxEligible (p : Policy) (B : Box) : Prop :=
  (1 / 2 : ℚ) < capLower p B ∧
    (∀ j : Fin 4, (fullSquarePiece j).upper B.lo B.hi < capLower p B) ∧
    (if p.val < 15 then ∀ j : Fin 4, ¬Selected p j →
      (selectedSquarePiece p j).upper B.lo B.hi < capLower p B
    else wExtraPiece.upper B.lo B.hi < capLower p B ∧ B.hi 0 < (25 / 128 : ℚ))

instance (p : Policy) (B : Box) : Decidable (WholeBoxEligible p B) := by
  unfold WholeBoxEligible Selected sourceId
  infer_instance

def wholeBoxEligibleTest (p : Policy) (B : Box) : Bool := decide (WholeBoxEligible p B)

theorem wholeBoxEligibleTest_sound (p : Policy) (B : Box)
    (htest : wholeBoxEligibleTest p B = true) :
    ∀ v ∈ B.region, TypedEligible p v := by
  have ht : WholeBoxEligible p B := of_decide_eq_true htest
  unfold WholeBoxEligible at ht
  intro v hv
  have hc := (cap_bounds p B hv).1
  have hhalf : (1 / 2 : ℝ) < (capLower p B : ℝ) := by exact_mod_cast ht.1
  refine ⟨hhalf.trans_le hc, ?_, ?_⟩
  · intro j
    have hj := (fullSquarePiece j).eval_le_upper B.lo B.hi v hv.1 hv.2
    rw [fullSquarePiece_eval] at hj
    have htj : ((fullSquarePiece j).upper B.lo B.hi : ℝ) < (capLower p B : ℝ) := by
      exact_mod_cast ht.2.1 j
    exact hj.trans_lt (htj.trans_le hc)
  · by_cases hp : p.val < 15
    · simp only [if_pos hp] at ht ⊢
      intro j hj
      have hs := (selectedSquarePiece p j).eval_le_upper B.lo B.hi v hv.1 hv.2
      rw [selectedSquarePiece_eval] at hs
      have htj : ((selectedSquarePiece p j).upper B.lo B.hi : ℝ) < (capLower p B : ℝ) := by
        exact_mod_cast ht.2.2 j hj
      exact hs.trans_lt (htj.trans_le hc)
    · simp only [if_neg hp] at ht ⊢
      have hs := wExtraPiece.eval_le_upper B.lo B.hi v hv.1 hv.2
      rw [wExtraPiece_eval] at hs
      have htA : (wExtraPiece.upper B.lo B.hi : ℝ) < (capLower p B : ℝ) := by
        exact_mod_cast ht.2.2.1
      have htX : (B.hi 0 : ℝ) < (25 / 128 : ℝ) := by exact_mod_cast ht.2.2.2
      exact ⟨hs.trans_lt (htA.trans_le hc), (hv.2 0).trans_lt htX⟩

/-- Non-strict reverse comparisons reject a strict original gate on the
whole CLOSED box. Equality is therefore correctly owned by rejection. -/
def WholeBoxIneligible (p : Policy) (B : Box) : Prop :=
  capUpper p B ≤ (1 / 2 : ℚ) ∨
    (∃ j : Fin 4, capUpper p B ≤ (fullSquarePiece j).lower B.lo B.hi) ∨
    (if p.val < 15 then ∃ j : Fin 4, ¬Selected p j ∧
      capUpper p B ≤ (selectedSquarePiece p j).lower B.lo B.hi
    else capUpper p B ≤ wExtraPiece.lower B.lo B.hi ∨ (25 / 128 : ℚ) ≤ B.lo 0)

instance (p : Policy) (B : Box) : Decidable (WholeBoxIneligible p B) := by
  unfold WholeBoxIneligible Selected sourceId
  infer_instance

def wholeBoxIneligibleTest (p : Policy) (B : Box) : Bool := decide (WholeBoxIneligible p B)

theorem wholeBoxIneligibleTest_sound (p : Policy) (B : Box)
    (htest : wholeBoxIneligibleTest p B = true) :
    ∀ v ∈ B.region, ¬TypedEligible p v := by
  have ht : WholeBoxIneligible p B := of_decide_eq_true htest
  unfold WholeBoxIneligible at ht
  intro v hv he
  have hc := (cap_bounds p B hv).2
  rcases ht with hhalf | hfull | hextra
  · have hhalfR : (capUpper p B : ℝ) ≤ (1 / 2 : ℝ) := by exact_mod_cast hhalf
    exact (not_lt_of_ge (hc.trans hhalfR)) he.1
  · obtain ⟨j, hj⟩ := hfull
    have hsq := (fullSquarePiece j).lower_le_eval B.lo B.hi v hv.1 hv.2
    rw [fullSquarePiece_eval] at hsq
    have hjR : (capUpper p B : ℝ) ≤ ((fullSquarePiece j).lower B.lo B.hi : ℝ) := by
      exact_mod_cast hj
    exact (not_lt_of_ge ((hc.trans hjR).trans hsq)) (he.2.1 j)
  · by_cases hp : p.val < 15
    · simp only [if_pos hp] at hextra
      obtain ⟨j, hnj, hj⟩ := hextra
      have hsq := (selectedSquarePiece p j).lower_le_eval B.lo B.hi v hv.1 hv.2
      rw [selectedSquarePiece_eval] at hsq
      have hjR : (capUpper p B : ℝ) ≤ ((selectedSquarePiece p j).lower B.lo B.hi : ℝ) := by
        exact_mod_cast hj
      have heextra : ∀ j : Fin 4, ¬Selected p j → selectedSquare p j v < cap p v := by
        simpa only [TypedEligible, if_pos hp] using he.2.2
      exact (not_lt_of_ge ((hc.trans hjR).trans hsq)) (heextra j hnj)
    · simp only [if_neg hp] at hextra
      have heextra : (1 + v 0) / 2 < cap p v ∧ v 0 < (25 / 128 : ℝ) := by
        simpa only [if_neg hp] using he.2.2
      rcases hextra with hA | hX
      · have hs := wExtraPiece.lower_le_eval B.lo B.hi v hv.1 hv.2
        rw [wExtraPiece_eval] at hs
        have hAR : (capUpper p B : ℝ) ≤ (wExtraPiece.lower B.lo B.hi : ℝ) := by
          exact_mod_cast hA
        exact (not_lt_of_ge ((hc.trans hAR).trans hs)) heextra.1
      · have hXR : (25 / 128 : ℝ) ≤ (B.lo 0 : ℝ) := by exact_mod_cast hX
        exact (not_lt_of_ge (hXR.trans (hv.1 0))) heextra.2

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.BoxCertificates
