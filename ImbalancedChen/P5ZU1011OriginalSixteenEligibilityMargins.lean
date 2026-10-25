import ImbalancedChen.P5ZU1011OriginalSixteenCorrelatedBoxCertificates
import ImbalancedChen.P5ZU1011OriginalSixteenWalls

/-!
# Actual finite eligibility margins and proper-wall dictionary

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The gate family below is the literal sixteen-policy eligibility circuit.
It includes both min-cap sides and both W conditions. Positive lower and
nonpositive upper rational tests are characterized by this SAME finite
family. Every required margin has an actual proper affine wall, proved by
the existing original-wall source; no form-properness premise is supplied.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityGridCertificates

noncomputable section

open Set U11Integral BoxCertificates
open P2OriginalFourthCapProducerInterface
open U1011OriginalSixteenWalls

inductive Gate where
  | half
  | full (j : Fin 4)
  | selected (j : Fin 4)
  | wExtra
  | wX
  deriving DecidableEq, Fintype

def Required (p : Policy) : Gate → Prop
  | .half => True
  | .full _ => True
  | .selected j => p.val < 15 ∧ ¬Selected p j
  | .wExtra => ¬p.val < 15
  | .wX => ¬p.val < 15

instance (p : Policy) (g : Gate) : Decidable (Required p g) := by
  cases g <;> unfold Required Selected sourceId <;> infer_instance

def margin (p : Policy) (left : Bool) : Gate → Affine
  | .half => (capPiece p left).sub halfPiece
  | .full j => (capPiece p left).sub (fullSquarePiece j)
  | .selected j => (capPiece p left).sub (selectedSquarePiece p j)
  | .wExtra => (capPiece p left).sub wExtraPiece
  | .wX => wXSlack

theorem correlatedEligible_iff_margins (p : Policy) (B : Box) :
    CorrelatedEligible p B ↔ ∀ g : Gate, Required p g →
      ∀ left : Bool, 0 < (margin p left g).lower B.lo B.hi := by
  constructor
  · intro ht g hg
    unfold CorrelatedEligible at ht
    cases g with
    | half => exact ht.1
    | full j => exact ht.2.1 j
    | selected j =>
      have hp := hg.1
      simp only [if_pos hp] at ht
      exact ht.2.2 j hg.2
    | wExtra =>
      simp only [if_neg hg] at ht
      exact ht.2.2.1
    | wX =>
      simp only [if_neg hg] at ht
      exact fun _ => ht.2.2.2
  · intro ht
    refine ⟨ht .half trivial, fun j => ht (.full j) trivial, ?_⟩
    by_cases hp : p.val < 15
    · simp only [if_pos hp]
      exact fun j hj => ht (.selected j) ⟨hp, hj⟩
    · simp only [if_neg hp]
      exact ⟨ht .wExtra hp, ht .wX hp true⟩

theorem correlatedIneligible_iff_margin (p : Policy) (B : Box) :
    CorrelatedIneligible p B ↔ ∃ g : Gate, Required p g ∧
      ∃ left : Bool, (margin p left g).upper B.lo B.hi ≤ 0 := by
  constructor
  · intro ht
    unfold CorrelatedIneligible at ht
    rcases ht with hh | hf | he
    · exact ⟨.half, trivial, hh⟩
    · obtain ⟨j, hj⟩ := hf
      exact ⟨.full j, trivial, hj⟩
    · by_cases hp : p.val < 15
      · simp only [if_pos hp] at he
        obtain ⟨j, hnj, hj⟩ := he
        exact ⟨.selected j, ⟨hp, hnj⟩, hj⟩
      · simp only [if_neg hp] at he
        rcases he with hA | hX
        · exact ⟨.wExtra, hp, hA⟩
        · exact ⟨.wX, hp, true, hX⟩
  · rintro ⟨g, hg, left, hleft⟩
    unfold CorrelatedIneligible
    cases g with
    | half => exact Or.inl ⟨left, hleft⟩
    | full j => exact Or.inr (Or.inl ⟨j, left, hleft⟩)
    | selected j =>
      refine Or.inr (Or.inr ?_)
      simp only [if_pos hg.1]
      exact ⟨j, hg.2, left, hleft⟩
    | wExtra =>
      refine Or.inr (Or.inr ?_)
      simp only [if_neg hg]
      exact Or.inl ⟨left, hleft⟩
    | wX =>
      refine Or.inr (Or.inr ?_)
      simp only [if_neg hg]
      exact Or.inr hleft

/-- This is an exact pointwise dictionary for the true original circuit,
not a premise asserting which box tests should pass. -/
theorem typedEligible_iff_positive_margins (p : Policy) (v : LogFour) :
    TypedEligible p v ↔ ∀ g : Gate, Required p g →
      ∀ left : Bool, 0 < (margin p left g).eval v := by
  constructor
  · intro he g hg left
    have hc := cap_le_piece p left v
    cases g with
    | half =>
      simp only [margin, Affine.eval_sub, halfPiece_eval]
      linarith only [he.1, hc]
    | full j =>
      simp only [margin, Affine.eval_sub, fullSquarePiece_eval]
      linarith only [he.2.1 j, hc]
    | selected j =>
      have hreq := he.2.2
      simp only [if_pos hg.1] at hreq
      simp only [margin, Affine.eval_sub, selectedSquarePiece_eval]
      linarith only [hreq j hg.2, hc]
    | wExtra =>
      have hreq := he.2.2
      simp only [if_neg hg] at hreq
      simp only [margin, Affine.eval_sub, wExtraPiece_eval]
      linarith only [hreq.1, hc]
    | wX =>
      have hreq := he.2.2
      simp only [if_neg hg] at hreq
      simp only [margin, wXSlack_eval]
      linarith only [hreq.2]
  · intro ht
    have hh : (1 / 2 : ℝ) < cap p v := by
      apply lt_cap_of_lt_all_pieces
      intro left
      have h := ht .half trivial left
      simp only [margin, Affine.eval_sub, halfPiece_eval] at h
      linarith only [h]
    refine ⟨hh, ?_, ?_⟩
    · intro j
      apply lt_cap_of_lt_all_pieces
      intro left
      have h := ht (.full j) trivial left
      simp only [margin, Affine.eval_sub, fullSquarePiece_eval] at h
      linarith only [h]
    · by_cases hp : p.val < 15
      · simp only [if_pos hp]
        intro j hj
        apply lt_cap_of_lt_all_pieces
        intro left
        have h := ht (.selected j) ⟨hp, hj⟩ left
        simp only [margin, Affine.eval_sub, selectedSquarePiece_eval] at h
        linarith only [h]
      · simp only [if_neg hp]
        constructor
        · apply lt_cap_of_lt_all_pieces
          intro left
          have h := ht .wExtra hp left
          simp only [margin, Affine.eval_sub, wExtraPiece_eval] at h
          linarith only [h]
        · have h := ht .wX hp true
          simp only [margin, wXSlack_eval] at h
          linarith only [h]

theorem capPiece_eq_actualAffine (p : Policy) (left : Bool) (v : LogFour) :
    (capPiece p left).eval v = affineCap p left v := by
  by_cases hp : p.val < 15 <;> cases left <;>
    simp [capPiece_eval, affineCap, capLinear, capOffset, hp,
      selectedLinear_apply, smul_eq_mul]
  <;> ring

private theorem eq_wPolicy_of_not_mask (p : Policy) (hp : ¬p.val < 15) : p = wPolicy := by
  apply Fin.ext
  have hcap := p.isLt
  simp only [wPolicy]
  omega

/-- These are exactly the already proved proper original wall forms. -/
def wall (p : Policy) (left : Bool) : Gate → (LogFour →L[ℝ] ℝ)
  | .half => halfGate p left
  | .full j => fullGate p left j
  | .selected j => selectedGate p left j
  | .wExtra => wExtraGate left
  | .wX => ContinuousLinearMap.proj 0

def wallOffset (p : Policy) (left : Bool) : Gate → ℝ
  | .half => capOffset p left - 1 / 2
  | .full _ => capOffset p left
  | .selected _ => capOffset p left
  | .wExtra => capOffset wPolicy left - 1 / 2
  | .wX => 25 / 128

/-- The thin strips below are centered on the actual proper eligibility
walls, with the source's offsets and strict endpoint conventions. -/
theorem margin_eq_actual_wall (p : Policy) (left : Bool) (g : Gate)
    (hg : Required p g) (v : LogFour) :
    (margin p left g).eval v = wallOffset p left g - wall p left g v := by
  cases g with
  | half =>
    simp only [margin, Affine.eval_sub, halfPiece_eval, capPiece_eq_actualAffine,
      wallOffset, wall, affineCap, halfGate, ContinuousLinearMap.neg_apply]
    ring
  | full j =>
    simp only [margin, Affine.eval_sub, fullSquarePiece_eval, capPiece_eq_actualAffine,
      wallOffset, wall, affineCap, fullGate, ContinuousLinearMap.sub_apply,
      fullSquareLinear_apply]
    ring
  | selected j =>
    simp only [margin, Affine.eval_sub, selectedSquarePiece_eval, capPiece_eq_actualAffine,
      wallOffset, wall, affineCap, selectedGate, ContinuousLinearMap.sub_apply,
      selectedSquareLinear_apply]
    ring
  | wExtra =>
    have hp := eq_wPolicy_of_not_mask p hg
    subst p
    simp only [margin, Affine.eval_sub, wExtraPiece_eval, capPiece_eq_actualAffine,
      wallOffset, wall, affineCap, wExtraGate, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  | wX => simp only [margin, wXSlack_eval, wallOffset, wall, ContinuousLinearMap.proj_apply]

theorem actual_wall_ne_zero (p : Policy) (left : Bool) (g : Gate) (_hg : Required p g) :
    wall p left g ≠ 0 := by
  cases g with
  | half => exact halfGate_ne_zero p left
  | full j => exact fullGate_ne_zero p left j
  | selected j => exact selectedGate_ne_zero p left j
  | wExtra => exact wExtraGate_ne_zero left
  | wX => exact coordinateGate_ne_zero 0

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
