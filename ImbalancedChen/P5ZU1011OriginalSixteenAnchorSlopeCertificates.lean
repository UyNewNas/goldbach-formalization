import ImbalancedChen.P5ZU1011OriginalSixteenAnchorFeedback
import ImbalancedChen.P5ZU1011OriginalSixteenTightRationalIntegralCertificates
import ImbalancedChen.P5ZU1011OriginalPairedFixedMaskHarmonic
import ImbalancedChen.P5OriginalCoefficientArithmetic

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.

A directed finite rational LOWER certificate for the genuine original16
method-zero anchor slope. The anchor is the literal K0=67619/10000.
Generated Buchstab intervals give a tight switched upper at K0 and a
switch-base lower endpoint. Every policy NOT proved ineligible remains
in the anchor comparison, using its literal H248 ordinary lower bound;
a failed positive-residual guard supplies zero rather than deleting it.

Automatic inner four-cells, exact volumes and reciprocal-coordinate lower
weights come from the existing original grid. Additional finite rational
separation tests preserve the complement of any selected original17572
row subfamily, including the LITERAL E0/E1 labels and half-open endpoints.
No cell bound, slope bound, whole mean or numerical passing check is a
premise or an assertion. No certificate is numerically evaluated here.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenAnchorSlopeCertificates

noncomputable section
open Set MeasureTheory
open Classical
open scoped BigOperators
open U11Integral U11Canonical U11H248
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenRationalIntegralCertificates
open U1011OriginalSixteenAnchorFeedback
open Certificates.PairedV2

abbrev Row := FullMask.Row

def anchorK : ℚ := 67619/10000

theorem anchorK_cast : (anchorK : ℝ)=P5OriginalCoefficientArithmetic.K0 := by
  norm_num [anchorK,P5OriginalCoefficientArithmetic.K0]

def baseLower (m : ℕ) (B : Box) : ℚ :=
  OriginalSixteenTightSwitchedBoxes.omegaLower m B/OriginalSixteenSwitchedBoxBounds.zUpper B

def anchorUpper (m : ℕ) (B : Box) : ℚ :=
  anchorK*OriginalSixteenTightSwitchedBoxes.omegaUpper m B/OriginalSixteenSwitchedBoxBounds.zLower B

/-- All possible ordinary policies remain in this finite test. -/
def AnchorTest (m : ℕ) (B : Box) : Prop := ∀ p : Policy,
  correlatedIneligibleTest p B≠true → anchorUpper m B≤OriginalSixteenEnvelopeBoxBounds.candidateLower p B

instance (m : ℕ) (B : Box) : Decidable (AnchorTest m B) := by
  unfold AnchorTest
  infer_instance

def anchorTest (m : ℕ) (B : Box) : Bool := decide (AnchorTest m B)

theorem tight_switch_bounds (m : ℕ) (hm : 0<m) (mask : Set (ℝ×ℝ)) (B : Box)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    (baseLower m B : ℝ)≤switchBase v ∧
      switchedKernel P5OriginalCoefficientArithmetic.K0 LiLiuPrereqBuchstab.buchstab v≤(anchorUpper m B : ℝ) := by
  have hz := OriginalSixteenTightSwitchedBoxes.coordinate_bounds mask B hv hD
  have hz0 : 0<v 2 := hz.1.trans_le hz.2.1
  have hω := OriginalSixteenTightSwitchedBoxes.omega_bounds m hm B
    (OriginalSixteenTightSwitchedBoxes.argument_bounds mask B hv hD)
  have hLo0 : (0 : ℝ)≤(OriginalSixteenTightSwitchedBoxes.omegaLower m B : ℝ) := by
    simp only [OriginalSixteenTightSwitchedBoxes.omegaLower,Rat.cast_max,Rat.cast_zero]
    exact le_max_left _ _
  have hU0 : (0 : ℝ)≤(OriginalSixteenTightSwitchedBoxes.omegaUpper m B : ℝ) :=
    hLo0.trans (hω.1.trans hω.2)
  have hK : (0 : ℝ)≤P5OriginalCoefficientArithmetic.K0 := by
    norm_num [P5OriginalCoefficientArithmetic.K0]
  simp only [baseLower,anchorUpper,Rat.cast_div,Rat.cast_mul,anchorK_cast,switchBase,switchedKernel,one_mul]
  constructor
  · exact (div_le_div_of_nonneg_left hLo0 hz0 hz.2.2).trans
      (div_le_div_of_nonneg_right hω.1 hz0.le)
  · exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω.2 hK) hz0.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hK hU0) hz.1 hz.2.1)

/-- A passing finite comparison places EVERY eligible original policy
above the actual anchor switch. No potentially active policy is omitted. -/
theorem anchorTest_sound (m : ℕ) (hm : 0<m) (B : Box) (ht : anchorTest m B=true)
    (mask : Set (ℝ×ℝ)) {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ originalDomain mask) :
    v ∈ anchorSwitchRegion P5OriginalCoefficientArithmetic.K0 := by
  have htest : AnchorTest m B := of_decide_eq_true ht
  intro j hj he
  have hj16 : j<16 := Finset.mem_range.mp hj
  let p : Policy := ⟨j,hj16⟩
  have heP : TypedEligible p v := (OriginalSixteenEnvelopeBoxBounds.eligible_policy p v).mp he
  have hpossible : correlatedIneligibleTest p B≠true := by
    intro hi
    exact correlatedIneligibleTest_sound p B hi v hv heP
  have hQ : anchorUpper m B≤OriginalSixteenEnvelopeBoxBounds.candidateLower p B := htest p hpossible
  have hR : (anchorUpper m B : ℝ)≤(OriginalSixteenEnvelopeBoxBounds.candidateLower p B : ℝ) := by
    exact_mod_cast hQ
  exact (tight_switch_bounds m hm mask B hv hD).2.trans
    (hR.trans (OriginalSixteenEnvelopeBoxBounds.candidateLower_le_actual mask p B hv hD heP))

/-- The original17572 row mask, retaining literal t/u half-open ownership. -/
def rowMask (S : Finset Row) : Set (ℝ×ℝ) := U1011OriginalPairedFixedMaskHarmonic.outerUnion S

def OutsideRows (S : Finset Row) (B : Box) : Prop := ∀ r ∈ S,
  B.hi 0≤tLower (FullMask.indices r).1 ∨ tUpper (FullMask.indices r).1≤B.lo 0 ∨
    B.hi 1≤uLower (FullMask.indices r).2 ∨ uUpper (FullMask.indices r).2≤B.lo 1

instance (S : Finset Row) (B : Box) : Decidable (OutsideRows S B) := by
  unfold OutsideRows
  infer_instance

def outsideRowsTest (S : Finset Row) (B : Box) : Bool := decide (OutsideRows S B)

theorem measurableSet_rowMask (S : Finset Row) : MeasurableSet (rowMask S) := by
  apply Finset.measurableSet_biUnion S
  intro r _
  have htL : MeasurableSet {q : ℝ×ℝ | (tLower (FullMask.indices r).1 : ℝ)≤q.1} :=
    measurableSet_le measurable_const measurable_fst
  have htU : MeasurableSet {q : ℝ×ℝ | q.1<(tUpper (FullMask.indices r).1 : ℝ)} :=
    measurableSet_lt measurable_fst measurable_const
  have huL : MeasurableSet {q : ℝ×ℝ | (uLower (FullMask.indices r).2 : ℝ)≤q.2} :=
    measurableSet_le measurable_const measurable_snd
  have huU : MeasurableSet {q : ℝ×ℝ | q.2<(uUpper (FullMask.indices r).2 : ℝ)} :=
    measurableSet_lt measurable_snd measurable_const
  exact htL.inter (htU.inter (huL.inter huU))

/-- The strict GRID upper wall makes <= separation safe against a
lower-inclusive mask edge; no boundary is silently removed. -/
theorem outsideRowsTest_sound (S : Finset Row) (n : ℕ) (j : Index n)
    (ht : outsideRowsTest S (gridBox n j)=true) {v : LogFour} (hv : v ∈ cell n j) :
    (v 0,v 1) ∉ rowMask S := by
  have htest : OutsideRows S (gridBox n j) := of_decide_eq_true ht
  intro hmask
  obtain ⟨r,hrS,hr⟩ := Set.mem_iUnion₂.mp hmask
  have hcoords := mem_logPrimeBox.mp hv
  rcases htest r hrS with h | h | h | h
  · have hR : ((gridBox n j).hi 0 : ℝ)≤(tLower (FullMask.indices r).1 : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge hr.1) ((hcoords 0).2.trans_le hR)
  · have hR : (tUpper (FullMask.indices r).1 : ℝ)≤((gridBox n j).lo 0 : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (hR.trans (hcoords 0).1)) hr.2.1
  · have hR : ((gridBox n j).hi 1 : ℝ)≤(uLower (FullMask.indices r).2 : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge hr.2.2.1) ((hcoords 1).2.trans_le hR)
  · have hR : (uUpper (FullMask.indices r).2 : ℝ)≤((gridBox n j).lo 1 : ℝ) := by exact_mod_cast h
    exact (not_lt_of_ge (hR.trans (hcoords 1).1)) hr.2.2.2

def certifiedCells (n m : ℕ) (S : Finset Row) : Finset (Index n) :=
  (inner n).filter (fun j => anchorTest m (gridBox n j)=true ∧ outsideRowsTest S (gridBox n j)=true)

def densityLower (n m : ℕ) (j : Index n) : ℚ := baseLower m (gridBox n j)*weightLower n j

def minorant (n m : ℕ) (j : Index n) : LogFour → ℝ :=
  (cell n j).indicator (fun _ => (densityLower n m j : ℝ))

def rationalSlopeLower (n m : ℕ) (S : Finset Row) : ℚ :=
  ∑ j ∈ certifiedCells n m S, densityLower n m j*cellVolume n

theorem certified_cell_subset (n m : ℕ) (hm : 0<m) (S : Finset Row) {j : Index n}
    (hj : j ∈ certifiedCells n m S) {v : LogFour} (hv : v ∈ cell n j) :
    v ∈ originalDomain (rowMask S) ∧ v ∈ anchorSwitchRegion P5OriginalCoefficientArithmetic.K0 := by
  obtain ⟨hinner,hcert,hout⟩ := Finset.mem_filter.mp hj
  have hD := inner_cell_subset_domain n hinner hv
  have hnot := outsideRowsTest_sound S n j hout hv
  have hDM : v ∈ originalDomain (rowMask S) :=
    ⟨hD.1,hD.2.1,hD.2.2.1,hD.2.2.2.1,hD.2.2.2.2.1,hD.2.2.2.2.2.1,hnot⟩
  exact ⟨hDM,anchorTest_sound m hm (gridBox n j) hcert (rowMask S)
    (cell_subset_closedBox n j hv) hDM⟩

theorem weighted_cell_lower (n m : ℕ) (hm : 0<m) (S : Finset Row) {j : Index n}
    (hj : j ∈ certifiedCells n m S) {v : LogFour} (hv : v ∈ cell n j) :
    (densityLower n m j : ℝ)≤slopeIntegrand P5OriginalCoefficientArithmetic.K0 v := by
  have hD := certified_cell_subset n m hm S hj hv
  have hB := cell_subset_closedBox n j hv
  have hbase := (tight_switch_bounds m hm (rowMask S) (gridBox n j) hB hD.1).1
  have hw := (weight_bounds n j hv).1
  have hw0 : (0 : ℝ)≤(weightLower n j : ℝ) := by
    exact_mod_cast (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_hi_pos n j i)).le) :
      (0 : ℚ)≤weightLower n j)
  have hb0 := switchBase_nonneg (rowMask S) v hD.1
  rw [slopeIntegrand,indicator_of_mem hD.2,U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]
  simpa only [densityLower,Rat.cast_mul,U1011OriginalSixteenRationalIntegralCertificates.weight] using
    mul_le_mul hbase hw hw0 hb0

theorem slope_indicator_nonneg (S : Finset Row) (v : LogFour) :
    0≤(originalDomain (rowMask S)).indicator (slopeIntegrand P5OriginalCoefficientArithmetic.K0) v := by
  by_cases hD : v ∈ originalDomain (rowMask S)
  · rw [indicator_of_mem hD]
    apply mul_nonneg
    · by_cases ha : v ∈ anchorSwitchRegion P5OriginalCoefficientArithmetic.K0
      · rw [indicator_of_mem ha]
        exact switchBase_nonneg (rowMask S) v hD
      · simp only [indicator_of_notMem ha,le_refl]
    · exact U1011OriginalSixteenReassembly.harmonicDensity_nonneg_on_original (rowMask S) v hD
  · simp only [indicator_of_notMem hD,le_refl]

/-- Entire automatic rational lower sum is below the TRUE actual slope,
with no hSlopeBound/hCellBound/mean input and no numeric pass asserted. -/
theorem rationalSlopeLower_le_actualSlope (n m : ℕ) (hm : 0<m) (S : Finset Row) :
    (rationalSlopeLower n m S : ℝ)≤anchorSlope P5OriginalCoefficientArithmetic.K0 (rowMask S) := by
  have hf : Integrable (fun v => ∑ j ∈ certifiedCells n m S, minorant n m j v) :=
    integrable_finsetSum _ (fun j _ => cell_constant_integrable n j _)
  have hg : Integrable ((originalDomain (rowMask S)).indicator
      (slopeIntegrand P5OriginalCoefficientArithmetic.K0)) :=
    (integrableOn_slopeIntegrand P5OriginalCoefficientArithmetic.K0 (rowMask S)).integrable_indicator
      (measurableSet_originalDomain (rowMask S) (measurableSet_rowMask S))
  have hpoint (v : LogFour) : (∑ j ∈ certifiedCells n m S, minorant n m j v)≤
      (originalDomain (rowMask S)).indicator (slopeIntegrand P5OriginalCoefficientArithmetic.K0) v := by
    by_cases hex : ∃ j ∈ certifiedCells n m S, v ∈ cell n j
    · obtain ⟨j,hj,hvj⟩ := hex
      have hD := certified_cell_subset n m hm S hj hvj
      have heq : (∑ k ∈ certifiedCells n m S, minorant n m k v)=minorant n m j v := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          exact indicator_of_notMem (fun hvk => hkj (cell_unique hvk hvj)) _
        · intro hnot
          exact (hnot hj).elim
      rw [heq,minorant,indicator_of_mem hvj,indicator_of_mem hD.1]
      exact weighted_cell_lower n m hm S hj hvj
    · have hz : (∑ j ∈ certifiedCells n m S, minorant n m j v)=0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun hvj => hex ⟨j,hj,hvj⟩) _
      rw [hz]
      exact slope_indicator_nonneg S v
  calc
    (rationalSlopeLower n m S : ℝ)=∑ j ∈ certifiedCells n m S,
        ((densityLower n m j*cellVolume n : ℚ) : ℝ) := by simp [rationalSlopeLower]
    _ = ∑ j ∈ certifiedCells n m S, ∫ v, minorant n m j v := by
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_cell_constant n j _).symm
    _ = ∫ v, ∑ j ∈ certifiedCells n m S, minorant n m j v :=
      (integral_finsetSum _ (fun j _ => cell_constant_integrable n j _)).symm
    _ ≤ ∫ v, (originalDomain (rowMask S)).indicator (slopeIntegrand P5OriginalCoefficientArithmetic.K0) v :=
      integral_mono hf hg hpoint
    _ = anchorSlope P5OriginalCoefficientArithmetic.K0 (rowMask S) :=
      integral_indicator (measurableSet_originalDomain (rowMask S) (measurableSet_rowMask S))

def slopeCheck (n m : ℕ) (S : Finset Row) (lower : ℚ) : Bool :=
  decide (0<m ∧ lower≤rationalSlopeLower n m S)

theorem slopeCheck_sound (n m : ℕ) (S : Finset Row) (lower : ℚ)
    (ht : slopeCheck n m S lower=true) :
    (lower : ℝ)≤anchorSlope P5OriginalCoefficientArithmetic.K0 (rowMask S) := by
  have h : 0<m ∧ lower≤rationalSlopeLower n m S := of_decide_eq_true ht
  have hL : (lower : ℝ)≤(rationalSlopeLower n m S : ℝ) := by exact_mod_cast h.2
  exact hL.trans (rationalSlopeLower_le_actualSlope n m h.1 S)

theorem rowMask_empty : rowMask ∅=∅ := by
  simp [rowMask,U1011OriginalPairedFixedMaskHarmonic.outerUnion]

/-- The empty deletion family gives the unaltered full anchor slope. -/
theorem rationalSlopeLower_le_full_anchorSlope (n m : ℕ) (hm : 0<m) :
    (rationalSlopeLower n m ∅ : ℝ)≤anchorSlope P5OriginalCoefficientArithmetic.K0 ∅ := by
  simpa only [rowMask_empty] using rationalSlopeLower_le_actualSlope n m hm ∅

theorem unmasked_slopeCheck_sound (n m : ℕ) (lower : ℚ)
    (ht : slopeCheck n m ∅ lower=true) :
    (lower : ℝ)≤anchorSlope P5OriginalCoefficientArithmetic.K0 ∅ := by
  simpa only [rowMask_empty] using slopeCheck_sound n m ∅ lower ht
/-- Literal E0/E1 row sets reuse the original source labels, not a new
rectangle mask. These are soundness corollaries, without passing checks. -/
theorem e0_slopeCheck_sound (n m : ℕ) (lower : ℚ)
    (ht : slopeCheck n m U1011OriginalPairedFixedMaskHarmonic.e0Rows lower=true) :
    (lower : ℝ)≤anchorSlope P5OriginalCoefficientArithmetic.K0 FullMask.P1E0E1.e0PairRegion := by
  simpa only [rowMask,U1011OriginalPairedFixedMaskHarmonic.outerUnion_e0] using
    slopeCheck_sound n m U1011OriginalPairedFixedMaskHarmonic.e0Rows lower ht

theorem e1_slopeCheck_sound (n m : ℕ) (lower : ℚ)
    (ht : slopeCheck n m U1011OriginalPairedFixedMaskHarmonic.e1Rows lower=true) :
    (lower : ℝ)≤anchorSlope P5OriginalCoefficientArithmetic.K0 FullMask.P1E0E1.e1PairRegion := by
  simpa only [rowMask,U1011OriginalPairedFixedMaskHarmonic.outerUnion_e1] using
    slopeCheck_sound n m U1011OriginalPairedFixedMaskHarmonic.e1Rows lower ht

end
end ImbalancedChen.P5Z.U1011OriginalSixteenAnchorSlopeCertificates

