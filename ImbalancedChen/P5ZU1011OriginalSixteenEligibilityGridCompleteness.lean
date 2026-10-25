import ImbalancedChen.P5ZU1011OriginalSixteenEligibilityMargins

/-!
# Local completeness and actual thin strips for original16 box tests

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Every coefficient of every actual eligibility margin has absolute value
at most six, directly from the original sixteen-policy formula. A rational
box of coordinate widths at most delta therefore has lower/upper margin
endpoint error at most 24*delta at every contained point.

This proves a positive local completeness radius at every point off the
actual proper eligibility walls. It also proves that an uncertain box is
contained in one explicit 24*delta strip around one of those SAME proper
walls. No boundary-mass, cell-bound, continuity, or numerical premise is
used as a supplier.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityGridCertificates

noncomputable section

open Set U11Integral BoxCertificates
open P2OriginalFourthCapProducerInterface
open scoped BigOperators

def WidthLe (B : Box) (delta : ℝ) : Prop :=
  ∀ i : Fin 4, (B.hi i : ℝ) - (B.lo i : ℝ) ≤ delta

/-- The coefficient bound is proved from the actual source dictionary;
it is not requested as an estimate premise from an external producer. -/
theorem margin_coefficient_abs_le_six (p : Policy) (left : Bool) (g : Gate) (i : Fin 4) :
    |((margin p left g).coefficient i : ℝ)| ≤ 6 := by
  cases g <;> by_cases hp : p.val < 15 <;> cases left <;>
    simp [margin, capPiece, halfPiece, fullSquarePiece, selectedSquarePiece,
      wExtraPiece, wXSlack, Affine.sub, hp] <;>
    split_ifs <;> norm_num

private def lowerCorner (a : Affine) (B : Box) (i : Fin 4) : ℚ :=
  if 0 ≤ a.coefficient i then B.lo i else B.hi i

private theorem lower_eq_eval_corner (a : Affine) (B : Box) :
    (a.lower B.lo B.hi : ℝ) = a.eval (fun i => (lowerCorner a B i : ℝ)) := by
  simp only [Affine.lower, Affine.eval, Rat.cast_add, Rat.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hc : 0 ≤ a.coefficient i <;> simp [lowerCorner, hc]

/-- A short arithmetic consequence of the existing signed affine
evaluator. Only this private helper accepts a coefficient bound; every
public original16 theorem supplies that bound from its actual formula. -/
private theorem affine_lower_endpoint_error (a : Affine) (B : Box) (v : LogFour)
    (delta : ℝ) (hv : v ∈ B.region) (hwidth : WidthLe B delta)
    (hcoeff : ∀ i, |(a.coefficient i : ℝ)| ≤ 6) :
    |a.eval v - (a.lower B.lo B.hi : ℝ)| ≤ 24 * delta := by
  have hdist (i : Fin 4) : |v i - (lowerCorner a B i : ℝ)| ≤ delta := by
    by_cases hc : 0 ≤ a.coefficient i
    · simp only [lowerCorner, if_pos hc]
      rw [abs_of_nonneg (sub_nonneg.mpr (hv.1 i))]
      linarith only [hv.2 i, hwidth i]
    · simp only [lowerCorner, if_neg hc]
      rw [abs_of_nonpos (sub_nonpos.mpr (hv.2 i))]
      linarith only [hv.1 i, hwidth i]
  rw [lower_eq_eval_corner]
  have heq : a.eval v - a.eval (fun i => (lowerCorner a B i : ℝ)) =
      ∑ i : Fin 4, (a.coefficient i : ℝ) * (v i - (lowerCorner a B i : ℝ)) := by
    simp only [Affine.eval, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ ∑ i : Fin 4, |(a.coefficient i : ℝ) * (v i - (lowerCorner a B i : ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, 6 * delta := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hcoeff i) (hdist i) (abs_nonneg _) (by norm_num)
    _ = 24 * delta := by norm_num <;> ring

private theorem affine_upper_endpoint_error (a : Affine) (B : Box) (v : LogFour)
    (delta : ℝ) (hv : v ∈ B.region) (hwidth : WidthLe B delta)
    (hcoeff : ∀ i, |(a.coefficient i : ℝ)| ≤ 6) :
    |a.eval v - (a.upper B.lo B.hi : ℝ)| ≤ 24 * delta := by
  have hneg : ∀ i, |(a.neg.coefficient i : ℝ)| ≤ 6 := by
    intro i
    simpa only [Affine.neg, Rat.cast_neg, abs_neg] using hcoeff i
  have h := affine_lower_endpoint_error a.neg B v delta hv hwidth hneg
  rw [Affine.eval_neg] at h
  have heq : -a.eval v - (a.neg.lower B.lo B.hi : ℝ) =
      -(a.eval v + (a.neg.lower B.lo B.hi : ℝ)) := by ring
  rw [heq, abs_neg] at h
  simpa only [Affine.upper, Rat.cast_neg, sub_neg_eq_add] using h

theorem margin_endpoint_errors (p : Policy) (left : Bool) (g : Gate)
    (B : Box) {v : LogFour} (delta : ℝ) (hv : v ∈ B.region) (hwidth : WidthLe B delta) :
    |(margin p left g).eval v - ((margin p left g).lower B.lo B.hi : ℝ)| ≤ 24 * delta ∧
      |(margin p left g).eval v - ((margin p left g).upper B.lo B.hi : ℝ)| ≤ 24 * delta := by
  exact ⟨affine_lower_endpoint_error _ B v delta hv hwidth
      (margin_coefficient_abs_le_six p left g),
    affine_upper_endpoint_error _ B v delta hv hwidth
      (margin_coefficient_abs_le_six p left g)⟩

/-- A fixed actual gate witnesses the entire uncertain box's strip.
The strip's form is proper by the existing original-wall theorem. -/
theorem uncertain_box_in_actual_proper_strip (p : Policy) (B : Box) (delta : ℝ)
    (hwidth : WidthLe B delta)
    (htrue : correlatedEligibleTest p B = false)
    (hfalse : correlatedIneligibleTest p B = false) :
    ∃ g : Gate, Required p g ∧ ∃ left : Bool, wall p left g ≠ 0 ∧
      ∀ v ∈ B.region, |wall p left g v - wallOffset p left g| ≤ 24 * delta := by
  have hnT : ¬CorrelatedEligible p B := of_decide_eq_false htrue
  have hnF : ¬CorrelatedIneligible p B := of_decide_eq_false hfalse
  rw [correlatedEligible_iff_margins] at hnT
  push_neg at hnT
  obtain ⟨g, hg, left, hL⟩ := hnT
  have hU : 0 < (margin p left g).upper B.lo B.hi := by
    by_contra hn
    apply hnF
    apply correlatedIneligible_iff_margin.mpr
    exact ⟨g, hg, left, le_of_not_gt hn⟩
  refine ⟨g, hg, left, actual_wall_ne_zero p left g hg, ?_⟩
  intro v hv
  have herr := margin_endpoint_errors p left g B delta hv hwidth
  have hLR : ((margin p left g).lower B.lo B.hi : ℝ) ≤ 0 := by exact_mod_cast hL
  have hUR : (0 : ℝ) < ((margin p left g).upper B.lo B.hi : ℝ) := by exact_mod_cast hU
  have hlow := (abs_le.mp herr.1).2
  have hupp := (abs_le.mp herr.2).1
  have habs : |(margin p left g).eval v| ≤ 24 * delta := by
    apply abs_le.mpr
    constructor <;> linarith only [hLR, hUR, hlow, hupp]
  rw [margin_eq_actual_wall p left g hg v] at habs
  simpa only [abs_sub_comm] using habs

private theorem finite_positive_floor {I : Type*} (s : Finset I) (f : I → ℝ) :
    (∀ i ∈ s, 0 < f i) → ∃ eta : ℝ, 0 < eta ∧ ∀ i ∈ s, eta ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro h
    exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    intro h
    obtain ⟨eta, heta, hbound⟩ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine ⟨min (f a) eta, lt_min (h a (by simp)) heta, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | his
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hbound i his)

/-- Every actual non-wall point has one positive radius for ALL original
gate tests and every rational closed box containing that point. The
radius is constructed from the finite actual margins, not supplied as a
cell-classification or boundary estimate premise. -/
theorem exists_local_complete_radius (p : Policy) (v : LogFour)
    (hno : ∀ g : Gate, Required p g → ∀ left : Bool,
      wall p left g v ≠ wallOffset p left g) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ B : Box, v ∈ B.region → WidthLe B delta →
      (correlatedEligibleTest p B = true ↔ TypedEligible p v) ∧
        (correlatedIneligibleTest p B = true ↔ ¬TypedEligible p v) := by
  classical
  have hnzero (g : Gate) (hg : Required p g) (left : Bool) :
      (margin p left g).eval v ≠ 0 := by
    intro hz
    have heq := margin_eq_actual_wall p left g hg v
    apply hno g hg left
    linarith only [heq, hz]
  let f : Gate × Bool → ℝ := fun t =>
    if Required p t.1 then |(margin p t.2 t.1).eval v| else 1
  have hf : ∀ t ∈ (Finset.univ : Finset (Gate × Bool)), 0 < f t := by
    intro t ht
    by_cases hreq : Required p t.1
    · simp only [f, if_pos hreq]
      exact abs_pos.mpr (hnzero t.1 hreq t.2)
    · simp only [f, if_neg hreq, zero_lt_one]
  obtain ⟨eta, heta, hfloor⟩ := finite_positive_floor Finset.univ f hf
  have hgap (g : Gate) (hg : Required p g) (left : Bool) :
      eta ≤ |(margin p left g).eval v| := by
    have h := hfloor (g, left) (Finset.mem_univ _)
    simpa only [f, if_pos hg] using h
  refine ⟨eta / 48, div_pos heta (by norm_num), ?_⟩
  intro B hv hwidth
  have hE : TypedEligible p v → correlatedEligibleTest p B = true := by
    intro he
    apply decide_eq_true
    apply correlatedEligible_iff_margins.mpr
    intro g hg left
    have hpos := (typedEligible_iff_positive_margins p v).mp he g hg left
    have hgap' := hgap g hg left
    rw [abs_of_pos hpos] at hgap'
    have herr := (margin_endpoint_errors p left g B (eta / 48) hv hwidth).1
    have hlow := (abs_le.mp herr).2
    have hLpos : (0 : ℝ) < ((margin p left g).lower B.lo B.hi : ℝ) := by
      linarith only [hgap', hlow, heta]
    exact_mod_cast hLpos
  have hI : ¬TypedEligible p v → correlatedIneligibleTest p B = true := by
    intro he
    rw [typedEligible_iff_positive_margins] at he
    push_neg at he
    obtain ⟨g, hg, left, hnonpos⟩ := he
    have hneg : (margin p left g).eval v < 0 := by
      rcases lt_or_eq_of_le hnonpos with hlt | heq
      · exact hlt
      · exact (hnzero g hg left heq).elim
    have hgap' := hgap g hg left
    rw [abs_of_neg hneg] at hgap'
    have herr := (margin_endpoint_errors p left g B (eta / 48) hv hwidth).2
    have hupp := (abs_le.mp herr).1
    have hUnonpos : ((margin p left g).upper B.lo B.hi : ℝ) ≤ 0 := by
      linarith only [hgap', hupp, heta]
    have hUQ : (margin p left g).upper B.lo B.hi ≤ 0 := by exact_mod_cast hUnonpos
    apply decide_eq_true
    apply correlatedIneligible_iff_margin.mpr
    exact ⟨g, hg, left, hUQ⟩
  exact ⟨⟨fun ht => correlatedEligibleTest_sound p B ht v hv, hE⟩,
    ⟨fun ht => correlatedIneligibleTest_sound p B ht v hv, hI⟩⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
