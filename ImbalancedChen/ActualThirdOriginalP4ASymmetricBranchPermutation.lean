import ImbalancedChen.ActualThirdOriginalSixTentCandidates

/-!
SOURCEONLY / UNCOMPILED / OPEN30.
The original if/elif priority and x/y permutation of the six tent candidates.
This supplies source branch and score transport, not a saved leaf or a
replacement of the ordinary finite selector. No target integral bound is input.
-/

namespace ImbalancedChen.OriginalThirdP4ASymmetricBranchPermutationSourceOnly

noncomputable section
open Set
open OriginalThirdBoxMomentsSourceOnly
open OriginalThirdOldChordMeanSourceOnly
open OriginalThirdSixTentCandidatesSourceOnly

/-- Exact original if upper_delta<=0 / elif lower_delta>=0 order. -/
def sourceSide (s : TentSum) (a b : BoxPoint) : Option TentSide :=
  if sourceDelta s b ≤ 0 then some .rise
  else if 0 ≤ sourceDelta s a then some .fall else none

theorem sourceSide_eq_some_iff (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    sourceSide s a b = some k ↔ sourceActive s k a b := by
  cases k <;> unfold sourceSide sourceActive <;> split_ifs <;> simp_all

theorem sourceActive_rise_iff (s : TentSum) (a b : BoxPoint) :
    sourceActive s .rise a b ↔ tentSum s b ≤ VariableEnvelope.mu := by
  change sourceDelta s b ≤ 0 ↔ _
  rw [sourceDelta_eq]
  constructor <;> intro h <;> linarith

/-- Equality at the upper endpoint belongs to rise; fall has a strict upper
test because the producer's elif is reached only after rise failed. -/
theorem sourceActive_fall_iff (s : TentSum) (a b : BoxPoint) :
    sourceActive s .fall a b ↔
      VariableEnvelope.mu < tentSum s b ∧ VariableEnvelope.mu ≤ tentSum s a := by
  change (¬ sourceDelta s b ≤ 0 ∧ 0 ≤ sourceDelta s a) ↔ _
  rw [sourceDelta_eq, sourceDelta_eq]
  constructor
  · rintro ⟨hb, ha⟩
    constructor <;> linarith
  · rintro ⟨hb, ha⟩
    constructor <;> linarith

theorem sourceSide_none_iff (s : TentSum) (a b : BoxPoint) :
    sourceSide s a b = none ↔
      tentSum s a < VariableEnvelope.mu ∧ VariableEnvelope.mu < tentSum s b := by
  unfold sourceSide
  rw [sourceDelta_eq, sourceDelta_eq]
  split_ifs with hb ha
  · constructor
    · intro h
      cases h
    · rintro ⟨_, h⟩
      exfalso
      linarith
  · constructor
    · intro h
      cases h
    · rintro ⟨h, _⟩
      exfalso
      linarith
  · constructor
    · intro _
      constructor <;> linarith
    · intro _
      rfl

theorem sourceSide_upper_tie (s : TentSum) (a b : BoxPoint)
    (hb : tentSum s b = VariableEnvelope.mu) :
    sourceSide s a b = some .rise := by
  apply (sourceSide_eq_some_iff s .rise a b).2
  exact (sourceActive_rise_iff s a b).2 hb.le

theorem sourceSide_lower_tie (s : TentSum) (a b : BoxPoint)
    (ha : tentSum s a = VariableEnvelope.mu)
    (hb : VariableEnvelope.mu < tentSum s b) :
    sourceSide s a b = some .fall := by
  apply (sourceSide_eq_some_iff s .fall a b).2
  exact (sourceActive_fall_iff s a b).2 ⟨hb, ha.ge⟩

theorem sourceActive_disjoint (s : TentSum) (a b : BoxPoint) :
    ¬ (sourceActive s .rise a b ∧ sourceActive s .fall a b) := by
  rintro ⟨hr, hf⟩
  exact hf.1 hr

/-- Permutation of exactly the six source coefficient triples. -/
def swapSum : TentSum → TentSum
  | .x => .y | .y => .x | .xy => .xy
  | .xz => .yz | .yz => .xz | .xyz => .xyz

/-- A point permutation only; no false symmetry of the actual compact kernel
or ordered compact region is asserted. -/
def swapXY (t : BoxPoint) : BoxPoint := ![t 1, t 0, t 2]

theorem swapSum_involutive (s : TentSum) : swapSum (swapSum s) = s := by
  cases s <;> rfl

theorem swapXY_involutive (t : BoxPoint) : swapXY (swapXY t) = t := by
  funext i
  fin_cases i <;> simp [swapXY]

theorem sumX_swapSum (s : TentSum) : sumX (swapSum s) = sumY s := by
  cases s <;> rfl

theorem sumY_swapSum (s : TentSum) : sumY (swapSum s) = sumX s := by
  cases s <;> rfl

theorem sumZ_swapSum (s : TentSum) : sumZ (swapSum s) = sumZ s := by
  cases s <;> rfl

theorem tentSum_swap (s : TentSum) (t : BoxPoint) :
    tentSum (swapSum s) (swapXY t) = tentSum s t := by
  simp only [tentSum, sumX_swapSum, sumY_swapSum, sumZ_swapSum, swapXY,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  ring

theorem tentPlane_swap (s : TentSum) (k : TentSide) (t : BoxPoint) :
    tentPlane (swapSum s) k (swapXY t) = tentPlane s k t := by
  simp only [tentPlane, tentSum_swap]

theorem sourceDelta_swap (s : TentSum) (t : BoxPoint) :
    sourceDelta (swapSum s) (swapXY t) = sourceDelta s t := by
  simp only [sourceDelta, tentPlane_swap]

theorem sourceActive_swap_iff (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    sourceActive (swapSum s) k (swapXY a) (swapXY b) ↔
      sourceActive s k a b := by
  cases k <;> simp only [sourceActive, sourceDelta_swap]

theorem sourceSide_swap (s : TentSum) (a b : BoxPoint) :
    sourceSide (swapSum s) (swapXY a) (swapXY b) = sourceSide s a b := by
  simp only [sourceSide, sourceDelta_swap]

/-- Exact lower endpoint of plane_range, including the decreasing plane. -/
def sourcePlaneLower (s : TentSum) (k : TentSide) (a b : BoxPoint) : ℝ :=
  match k with
  | .rise => tentPlane s .rise a
  | .fall => tentPlane s .fall b

/-- Python minorant() compares low+high, not the OLD/Jensen result. -/
def sourcePlaneScore (s : TentSum) (k : TentSide) (a b : BoxPoint) : ℝ :=
  sourcePlaneLower s k a b + planeUpper s k a b

def sourceEligible (s : TentSum) (k : TentSide) (a b : BoxPoint) : Prop :=
  sourceActive s k a b ∧ planeUpper s k a b ≤ thirdPrefixTheta

theorem sourcePlaneLower_swap (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    sourcePlaneLower (swapSum s) k (swapXY a) (swapXY b) =
      sourcePlaneLower s k a b := by
  cases k <;> simp only [sourcePlaneLower, tentPlane_swap]

theorem planeUpper_swap (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    planeUpper (swapSum s) k (swapXY a) (swapXY b) = planeUpper s k a b := by
  cases k <;> simp only [planeUpper, tentPlane_swap]

theorem sourcePlaneScore_swap (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    sourcePlaneScore (swapSum s) k (swapXY a) (swapXY b) =
      sourcePlaneScore s k a b := by
  simp only [sourcePlaneScore, sourcePlaneLower_swap, planeUpper_swap]

theorem sourceEligible_swap_iff (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    sourceEligible (swapSum s) k (swapXY a) (swapXY b) ↔
      sourceEligible s k a b := by
  simp only [sourceEligible, sourceActive_swap_iff, planeUpper_swap]

theorem oldX_swapSum (s : TentSum) (k : TentSide) :
    oldX (swapSum s) k = oldY s k := by
  simp only [oldX, oldY, sumX_swapSum]

theorem oldY_swapSum (s : TentSum) (k : TentSide) :
    oldY (swapSum s) k = oldX s k := by
  simp only [oldX, oldY, sumY_swapSum]

theorem oldZ_swapSum (s : TentSum) (k : TentSide) :
    oldZ (swapSum s) k = oldZ s k := by
  simp only [oldZ, sumZ_swapSum]

theorem oldNumerator_swap (s : TentSum) (k : TentSide) (t : BoxPoint) :
    oldNumerator (swapSum s) k (swapXY t) = oldNumerator s k t := by
  simp only [oldNumerator, oldX_swapSum, oldY_swapSum, swapXY,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem tentOldArgument_swap (s : TentSum) (k : TentSide) (t : BoxPoint) :
    tentOldArgument (swapSum s) k (swapXY t) = tentOldArgument s k t := by
  simp only [tentOldArgument, affineArgument, oldX_swapSum, oldY_swapSum,
    oldZ_swapSum, swapXY, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  ring

theorem tentOldLow_swap (s : TentSum) (k : TentSide) (b : BoxPoint) :
    tentOldLow (swapSum s) k (swapXY b) = tentOldLow s k b := by
  exact tentOldArgument_swap s k b

theorem tentOldHigh_swap (s : TentSum) (k : TentSide) (a : BoxPoint) :
    tentOldHigh (swapSum s) k (swapXY a) = tentOldHigh s k a := by
  exact tentOldArgument_swap s k a

/-- The residual and endpoint support tests used after selecting the plane
transport with the same permutation, as do active/root eligibility tests. -/
theorem source_mean_tests_swap_iff (s : TentSum) (k : TentSide) (a b : BoxPoint) :
    (sourceEligible (swapSum s) k (swapXY a) (swapXY b) ∧
      0 < oldNumerator (swapSum s) k (swapXY b) ∧
      2 ≤ tentOldLow (swapSum s) k (swapXY b)) ↔
    (sourceEligible s k a b ∧ 0 < oldNumerator s k b ∧
      2 ≤ tentOldLow s k b) := by
  simp only [sourceEligible_swap_iff, oldNumerator_swap, tentOldLow_swap]

theorem swapXY_symmetric_endpoint (a c : ℝ) :
    swapXY (![a, a, c] : BoxPoint) = ![a, a, c] := by
  funext i
  fin_cases i <;> simp [swapXY]

/-- On a source symmetric rectangle, paired branches have identical original
active/root filters. This does not permute the producer's enumeration order. -/
theorem symmetric_sourceEligible_swap_iff (s : TentSum) (k : TentSide)
    (a b c d : ℝ) :
    sourceEligible (swapSum s) k ![a, a, c] ![b, b, d] ↔
      sourceEligible s k ![a, a, c] ![b, b, d] := by
  simpa only [swapXY_symmetric_endpoint] using
    sourceEligible_swap_iff s k (![a, a, c] : BoxPoint) ![b, b, d]

theorem symmetric_sourceSide_swap (s : TentSum) (a b c d : ℝ) :
    sourceSide (swapSum s) ![a, a, c] ![b, b, d] =
      sourceSide s ![a, a, c] ![b, b, d] := by
  simpa only [swapXY_symmetric_endpoint] using
    sourceSide_swap s (![a, a, c] : BoxPoint) ![b, b, d]

theorem symmetric_primary_sides_below (a b c d : ℝ)
    (hmu : b ≤ VariableEnvelope.mu) :
    sourceSide .x ![a, a, c] ![b, b, d] = some .rise ∧
      sourceSide .y ![a, a, c] ![b, b, d] = some .rise := by
  have hx : sourceSide .x ![a, a, c] ![b, b, d] = some .rise := by
    apply (sourceSide_eq_some_iff .x .rise _ _).2
    apply (sourceActive_rise_iff .x _ _).2
    simpa [tentSum, sumX, sumY, sumZ] using hmu
  refine ⟨hx, ?_⟩
  simpa only [swapSum] using (symmetric_sourceSide_swap .x a b c d).trans hx

theorem symmetric_primary_sides_above (a b c d : ℝ)
    (hab : a < b) (hmu : VariableEnvelope.mu ≤ a) :
    sourceSide .x ![a, a, c] ![b, b, d] = some .fall ∧
      sourceSide .y ![a, a, c] ![b, b, d] = some .fall := by
  have hx : sourceSide .x ![a, a, c] ![b, b, d] = some .fall := by
    apply (sourceSide_eq_some_iff .x .fall _ _).2
    apply (sourceActive_fall_iff .x _ _).2
    simpa [tentSum, sumX, sumY, sumZ] using And.intro (hmu.trans_lt hab) hmu
  refine ⟨hx, ?_⟩
  simpa only [swapSum] using (symmetric_sourceSide_swap .x a b c d).trans hx

theorem symmetric_sourcePlaneScore_swap (s : TentSum) (k : TentSide)
    (a b c d : ℝ) :
    sourcePlaneScore (swapSum s) k ![a, a, c] ![b, b, d] =
      sourcePlaneScore s k ![a, a, c] ![b, b, d] := by
  simpa only [swapXY_symmetric_endpoint] using
    sourcePlaneScore_swap s k (![a, a, c] : BoxPoint) ![b, b, d]

/-- These are genuine score ties in source order x,y,xy,xz,yz,xyz.
Consequently swapping the names of x/y or xz/yz cannot be treated as a
permutation of the selected label under Python's first-maximum rule. -/
theorem symmetric_paired_score_ties (k : TentSide) (a b c d : ℝ) :
    sourcePlaneScore .x k ![a, a, c] ![b, b, d] =
        sourcePlaneScore .y k ![a, a, c] ![b, b, d] ∧
    sourcePlaneScore .xz k ![a, a, c] ![b, b, d] =
        sourcePlaneScore .yz k ![a, a, c] ![b, b, d] := by
  constructor
  · exact (symmetric_sourcePlaneScore_swap .x k a b c d).symm
  · exact (symmetric_sourcePlaneScore_swap .xz k a b c d).symm

/-- A score maximum remains a score maximum after the symmetric sum
permutation. The conclusion deliberately preserves value/maximality rather
than asserting an equivariant selected label across source ties. -/
theorem symmetric_maximal_score_transport
    (s : TentSum) (k : TentSide) (a b c d : ℝ)
    (hmax : ∀ u l, sourceEligible u l ![a, a, c] ![b, b, d] →
      sourcePlaneScore u l ![a, a, c] ![b, b, d] ≤
        sourcePlaneScore s k ![a, a, c] ![b, b, d]) :
    ∀ u l, sourceEligible u l ![a, a, c] ![b, b, d] →
      sourcePlaneScore u l ![a, a, c] ![b, b, d] ≤
        sourcePlaneScore (swapSum s) k ![a, a, c] ![b, b, d] := by
  intro u l hu
  rw [symmetric_sourcePlaneScore_swap]
  exact hmax u l hu

end
end ImbalancedChen.OriginalThirdP4ASymmetricBranchPermutationSourceOnly
