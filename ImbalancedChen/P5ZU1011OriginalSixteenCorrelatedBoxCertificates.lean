import ImbalancedChen.P5ZU1011OriginalSixteenBoxCertificates

/-!
# Correlated eligibility certificates for the actual sixteen-policy bank

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Every cap-minus-gate difference is evaluated as ONE signed affine form
on the rational box. This preserves coordinate cancellation. The cap is
still the min of both actual mask branches; W has one actual cap circuit
with two equal Boolean flags. All strict original gates are retained.

Positive lower differences certify eligibility throughout a closed box.
A nonpositive upper difference certifies a failed strict gate throughout
that box, with equality correctly rejected. Both W extra gates are used.
The existing generic signed affine endpoint evaluator is reused verbatim.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityGridCertificates

noncomputable section

open Set U11Integral
open BoxCertificates P2OriginalFourthCapProducerInterface

def halfPiece : Affine := ⟨1 / 2, fun _ => 0⟩

def wXSlack : Affine := ⟨25 / 128, fun i => if i = 0 then -1 else 0⟩

theorem halfPiece_eval (v : LogFour) : halfPiece.eval v = (1 / 2 : ℝ) := by
  simp [halfPiece, Affine.eval]

theorem wXSlack_eval (v : LogFour) : wXSlack.eval v = (25 / 128 : ℝ) - v 0 := by
  simp [wXSlack, Affine.eval, ite_mul]
  <;> ring

theorem cap_le_piece (p : Policy) (left : Bool) (v : LogFour) :
    cap p v ≤ (capPiece p left).eval v := by
  rw [cap_eq_piece_min]
  by_cases hp : p.val < 15
  · simp only [if_pos hp]
    cases left
    · exact min_le_right _ _
    · exact min_le_left _ _
  · simp only [if_neg hp]
    simp only [capPiece_eval, if_neg hp, le_refl]

theorem lt_cap_of_lt_all_pieces (p : Policy) (v : LogFour) (x : ℝ)
    (h : ∀ left : Bool, x < (capPiece p left).eval v) : x < cap p v := by
  rw [cap_eq_piece_min]
  by_cases hp : p.val < 15
  · simp only [if_pos hp]
    exact lt_min (h true) (h false)
  · simpa only [if_neg hp] using h true

def PositiveMargins (p : Policy) (B : Box) (lhs : Affine) : Prop :=
  ∀ left : Bool, 0 < ((capPiece p left).sub lhs).lower B.lo B.hi

def NonpositiveMargin (p : Policy) (B : Box) (lhs : Affine) : Prop :=
  ∃ left : Bool, ((capPiece p left).sub lhs).upper B.lo B.hi ≤ 0

/-- This helper specializes the existing generic evaluator to the actual
min-cap circuit; its input is a finite rational margin test. -/
theorem positiveMargins_sound (p : Policy) (B : Box) (lhs : Affine)
    (ht : PositiveMargins p B lhs) {v : LogFour} (hv : v ∈ B.region) :
    lhs.eval v < cap p v := by
  apply lt_cap_of_lt_all_pieces
  intro left
  have hL := ((capPiece p left).sub lhs).lower_le_eval B.lo B.hi v hv.1 hv.2
  rw [Affine.eval_sub] at hL
  have hpos : (0 : ℝ) < (((capPiece p left).sub lhs).lower B.lo B.hi : ℝ) := by
    exact_mod_cast ht left
  linarith only [hL, hpos]

theorem nonpositiveMargin_sound (p : Policy) (B : Box) (lhs : Affine)
    (ht : NonpositiveMargin p B lhs) {v : LogFour} (hv : v ∈ B.region) :
    cap p v ≤ lhs.eval v := by
  obtain ⟨left, hleft⟩ := ht
  have hU := ((capPiece p left).sub lhs).eval_le_upper B.lo B.hi v hv.1 hv.2
  rw [Affine.eval_sub] at hU
  have hnonpos : (((capPiece p left).sub lhs).upper B.lo B.hi : ℝ) ≤ 0 := by
    exact_mod_cast hleft
  have hc := cap_le_piece p left v
  linarith only [hU, hnonpos, hc]

def CorrelatedEligible (p : Policy) (B : Box) : Prop :=
  PositiveMargins p B halfPiece ∧
    (∀ j : Fin 4, PositiveMargins p B (fullSquarePiece j)) ∧
    (if p.val < 15 then ∀ j : Fin 4, ¬Selected p j →
      PositiveMargins p B (selectedSquarePiece p j)
    else PositiveMargins p B wExtraPiece ∧ 0 < wXSlack.lower B.lo B.hi)

instance (p : Policy) (B : Box) : Decidable (CorrelatedEligible p B) := by
  unfold CorrelatedEligible PositiveMargins Selected sourceId
  infer_instance

def correlatedEligibleTest (p : Policy) (B : Box) : Bool := decide (CorrelatedEligible p B)

theorem correlatedEligibleTest_sound (p : Policy) (B : Box)
    (htest : correlatedEligibleTest p B = true) : ∀ v ∈ B.region, TypedEligible p v := by
  have ht : CorrelatedEligible p B := of_decide_eq_true htest
  unfold CorrelatedEligible at ht
  intro v hv
  have hhalf := positiveMargins_sound p B halfPiece ht.1 hv
  rw [halfPiece_eval] at hhalf
  refine ⟨hhalf, ?_, ?_⟩
  · intro j
    have hj := positiveMargins_sound p B (fullSquarePiece j) (ht.2.1 j) hv
    simpa only [fullSquarePiece_eval] using hj
  · by_cases hp : p.val < 15
    · simp only [if_pos hp] at ht ⊢
      intro j hnj
      have hj := positiveMargins_sound p B (selectedSquarePiece p j) (ht.2.2 j hnj) hv
      simpa only [selectedSquarePiece_eval] using hj
    · simp only [if_neg hp] at ht ⊢
      have hA := positiveMargins_sound p B wExtraPiece ht.2.2.1 hv
      rw [wExtraPiece_eval] at hA
      have hX := wXSlack.lower_le_eval B.lo B.hi v hv.1 hv.2
      rw [wXSlack_eval] at hX
      have hXL : (0 : ℝ) < (wXSlack.lower B.lo B.hi : ℝ) := by exact_mod_cast ht.2.2.2
      refine ⟨hA, ?_⟩
      linarith only [hX, hXL]

def CorrelatedIneligible (p : Policy) (B : Box) : Prop :=
  NonpositiveMargin p B halfPiece ∨
    (∃ j : Fin 4, NonpositiveMargin p B (fullSquarePiece j)) ∨
    (if p.val < 15 then ∃ j : Fin 4, ¬Selected p j ∧
      NonpositiveMargin p B (selectedSquarePiece p j)
    else NonpositiveMargin p B wExtraPiece ∨ wXSlack.upper B.lo B.hi ≤ 0)

instance (p : Policy) (B : Box) : Decidable (CorrelatedIneligible p B) := by
  unfold CorrelatedIneligible NonpositiveMargin Selected sourceId
  infer_instance

def correlatedIneligibleTest (p : Policy) (B : Box) : Bool := decide (CorrelatedIneligible p B)

theorem correlatedIneligibleTest_sound (p : Policy) (B : Box)
    (htest : correlatedIneligibleTest p B = true) : ∀ v ∈ B.region, ¬TypedEligible p v := by
  have ht : CorrelatedIneligible p B := of_decide_eq_true htest
  unfold CorrelatedIneligible at ht
  intro v hv he
  rcases ht with hhalf | hfull | hextra
  · have h := nonpositiveMargin_sound p B halfPiece hhalf hv
    rw [halfPiece_eval] at h
    exact (not_lt_of_ge h) he.1
  · obtain ⟨j, hj⟩ := hfull
    have h := nonpositiveMargin_sound p B (fullSquarePiece j) hj hv
    rw [fullSquarePiece_eval] at h
    exact (not_lt_of_ge h) (he.2.1 j)
  · by_cases hp : p.val < 15
    · simp only [if_pos hp] at hextra
      obtain ⟨j, hnj, hj⟩ := hextra
      have h := nonpositiveMargin_sound p B (selectedSquarePiece p j) hj hv
      rw [selectedSquarePiece_eval] at h
      have hrequired : selectedSquare p j v < cap p v := by
        have hh := he.2.2
        simp only [if_pos hp] at hh
        exact hh j hnj
      exact (not_lt_of_ge h) hrequired
    · simp only [if_neg hp] at hextra
      have hrequired : (1 + v 0) / 2 < cap p v ∧ v 0 < (25 / 128 : ℝ) := by
        simpa only [if_neg hp] using he.2.2
      rcases hextra with hA | hX
      · have h := nonpositiveMargin_sound p B wExtraPiece hA hv
        rw [wExtraPiece_eval] at h
        exact (not_lt_of_ge h) hrequired.1
      · have h := wXSlack.eval_le_upper B.lo B.hi v hv.1 hv.2
        rw [wXSlack_eval] at h
        have hXU : (wXSlack.upper B.lo B.hi : ℝ) ≤ 0 := by exact_mod_cast hX
        linarith only [h, hXU, hrequired.2]

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
