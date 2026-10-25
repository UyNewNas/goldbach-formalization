import ImbalancedChen.P5ZU1011OriginalSixteenJointAnchorFeedback
import ImbalancedChen.P5ZU1011OriginalSixteenAnchorSlopeCertificates

/-!
SOURCE_ONLY / UNCOMPILED / NOT_ROOT_ACCEPTED.
Finite rational SOUNDNESS for the TRUE JOINT method-zero slope. The new
low-band inner grid has FIVE actual D10 source gates and is UNMASKED.
The tight generated Buchstab query interpreter is separately licensed on
D10's true [49/19,3332/417] range; no D11 support assertion is reused.
All possibly active ordinary policies retain their literal H248 lower
endpoints. The high-band same-row-mask lower sum is the existing9d86
certificate. Adding the two lower sums bounds the constructed TRUE SJ.
No numerical certificate is run, no saved-pass or retained-slope comparison
is asserted, and no hCellBound/hSlopeBound/mean is assumed.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenJointSlopeCertificates

noncomputable section
open Set MeasureTheory
open Classical
open scoped BigOperators
open U11Integral U11Canonical U11H248
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSixteenRationalIntegralCertificates
open U1011OriginalSixteenAnchorFeedback U1011OriginalSixteenJointAnchorFeedback
open U1011OriginalSixteenU10Geometry
open P2OriginalFourthCapProducerInterface

abbrev Row := Certificates.PairedV2.FullMask.Row

def sourcePiece10 : Fin 5 → Affine :=
  ![⟨417/5000,![0,0,0,-1]⟩,⟨0,![0,0,-1,1]⟩,⟨0,![0,-1,1,0]⟩,
    ⟨0,![-1,1,0,0]⟩,⟨-(19/125),![1,0,0,0]⟩]

def Inner10 (n : ℕ) (j : Index n) : Prop :=
  ∀ i : Fin 5,(sourcePiece10 i).upper (gridBox n j).lo (gridBox n j).hi<0
instance (n : ℕ) (j : Index n) : Decidable (Inner10 n j) := by unfold Inner10; infer_instance

def inner10 (n : ℕ) : Finset (Index n) := Finset.univ.filter (Inner10 n)

theorem inner10_cell_subset (n : ℕ) {j : Index n} (hj : j ∈ inner10 n) : cell n j ⊆ domain10 := by
  intro v hv
  have hB:=cell_subset_closedBox n j hv
  have hg (i : Fin 5) : (sourcePiece10 i).eval v<0 := by
    have hU:=(sourcePiece10 i).eval_le_upper (gridBox n j).lo (gridBox n j).hi v hB.1 hB.2
    have hQ : (((sourcePiece10 i).upper (gridBox n j).lo (gridBox n j).hi : ℚ) : ℝ)<0 := by
      exact_mod_cast (Finset.mem_filter.mp hj).2 i
    exact hU.trans_lt hQ
  have h0:=hg 0
  have h1:=hg 1
  have h2:=hg 2
  have h3:=hg 3
  have h4:=hg 4
  norm_num [sourcePiece10,Affine.eval,Fin.sum_univ_succ] at h0 h1 h2 h3 h4
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

/-- Actual denominator margins for a low-band point in a rational box. -/
theorem coordinate_bounds10 (B : Box) {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ domain10) :
    0<(OriginalSixteenSwitchedBoxBounds.zLower B : ℝ) ∧
      (OriginalSixteenSwitchedBoxBounds.zLower B : ℝ)≤v 2 ∧
      v 2≤(OriginalSixteenSwitchedBoxBounds.zUpper B : ℝ) := by
  have hA : (OriginalSixteenSwitchedBoxBounds.a : ℝ)≤v 2 := (domain10_subset_compactBox hD).1 2
  have hLo : (OriginalSixteenSwitchedBoxBounds.zLower B : ℝ)≤v 2 := by
    simp only [OriginalSixteenSwitchedBoxBounds.zLower,Rat.cast_max]
    exact max_le hA (hv.1 2)
  have hHi : v 2≤(OriginalSixteenSwitchedBoxBounds.zUpper B : ℝ) :=
    (hv.2 2).trans (by simp only [OriginalSixteenSwitchedBoxBounds.zUpper,Rat.cast_max]; exact le_max_right _ _)
  have ha : (0 : ℝ)<(OriginalSixteenSwitchedBoxBounds.a : ℝ) := by
    norm_num [OriginalSixteenSwitchedBoxBounds.a]
  have hLower : (OriginalSixteenSwitchedBoxBounds.a : ℝ)≤(OriginalSixteenSwitchedBoxBounds.zLower B : ℝ) := by
    simp only [OriginalSixteenSwitchedBoxBounds.zLower,Rat.cast_max]
    exact le_max_left _ _
  exact ⟨ha.trans_le hLower,hLo,hHi⟩

/-- The SAME generated rational query is now licensed on TRUE D10. -/
theorem argument_bounds10 (B : Box) {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ domain10) :
    (1-(v 0+v 1+v 2+v 3))/v 2 ∈ Icc
      (OriginalSixteenTightSwitchedBoxes.queryLower B : ℝ) (OriginalSixteenTightSwitchedBoxes.queryUpper B : ℝ) := by
  let s : ℝ:=(1-(v 0+v 1+v 2+v 3))/v 2
  let r : ℝ:=1-(v 0+v 1+v 2+v 3)
  have hz:=coordinate_bounds10 B hv hD
  have hz0 : 0<v 2:=hz.1.trans_le hz.2.1
  have hsD:=domain10_argument_bounds hD
  have hs2 : (2 : ℝ)≤s := by dsimp [s]; linarith [hsD.1]
  have hs8 : s≤(8 : ℝ) := by dsimp [s]; linarith [hsD.2]
  have hr0 : 0≤r := by
    have hh:=(le_div_iff₀ hz0).mp (show (0 : ℝ)≤r/v 2 from (by change 0≤s; linarith))
    simpa only [zero_mul] using hh
  have hnLo : (OriginalSixteenTightSwitchedBoxes.numeratorLower B : ℝ)≤r := by
    simp only [OriginalSixteenTightSwitchedBoxes.numeratorLower,Rat.cast_max,Rat.cast_zero,Rat.cast_sub,Rat.cast_one,Rat.cast_add]
    refine max_le hr0 ?_
    dsimp [r]
    linarith [hv.2 0,hv.2 1,hv.2 2,hv.2 3]
  have hnHi : r≤(OriginalSixteenTightSwitchedBoxes.numeratorUpper B : ℝ) := by
    have hh : r≤1-((B.lo 0 : ℝ)+B.lo 1+B.lo 2+B.lo 3) := by
      dsimp [r]
      linarith [hv.1 0,hv.1 1,hv.1 2,hv.1 3]
    simp only [OriginalSixteenTightSwitchedBoxes.numeratorUpper,Rat.cast_max,Rat.cast_zero,Rat.cast_sub,Rat.cast_one,Rat.cast_add]
    exact hh.trans (le_max_right _ _)
  have hnLo0 : (0 : ℝ)≤(OriginalSixteenTightSwitchedBoxes.numeratorLower B : ℝ) := by
    simp only [OriginalSixteenTightSwitchedBoxes.numeratorLower,Rat.cast_max,Rat.cast_zero]
    exact le_max_left _ _
  have hnHi0 : (0 : ℝ)≤(OriginalSixteenTightSwitchedBoxes.numeratorUpper B : ℝ):=hr0.trans hnHi
  have hRawLo : (OriginalSixteenTightSwitchedBoxes.numeratorLower B : ℝ)/
      (OriginalSixteenSwitchedBoxBounds.zUpper B : ℝ)≤s :=
    (div_le_div_of_nonneg_left hnLo0 hz0 hz.2.2).trans (div_le_div_of_nonneg_right hnLo hz0.le)
  have hRawHi : s≤(OriginalSixteenTightSwitchedBoxes.numeratorUpper B : ℝ)/
      (OriginalSixteenSwitchedBoxBounds.zLower B : ℝ) :=
    (div_le_div_of_nonneg_right hnHi hz0.le).trans (div_le_div_of_nonneg_left hnHi0 hz.1 hz.2.1)
  constructor
  · simp only [OriginalSixteenTightSwitchedBoxes.queryLower,Rat.cast_max,Rat.cast_min,Rat.cast_ofNat,Rat.cast_div]
    exact max_le hs2 ((min_le_right _ _).trans hRawLo)
  · have hh : s≤min 8 ((OriginalSixteenTightSwitchedBoxes.numeratorUpper B : ℝ)/
        (OriginalSixteenSwitchedBoxBounds.zLower B : ℝ)):=le_min hs8 hRawHi
    simp only [OriginalSixteenTightSwitchedBoxes.queryUpper,Rat.cast_max,Rat.cast_min,Rat.cast_ofNat,Rat.cast_div]
    exact hh.trans (le_max_right _ _)

theorem tight_switch_bounds10 (m : ℕ) (hm : 0<m) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ domain10) :
    (U1011OriginalSixteenAnchorSlopeCertificates.baseLower m B : ℝ)≤switchBase v ∧
      switchedKernel P5OriginalCoefficientArithmetic.K0 LiLiuPrereqBuchstab.buchstab v≤
        (U1011OriginalSixteenAnchorSlopeCertificates.anchorUpper m B : ℝ) := by
  have hz:=coordinate_bounds10 B hv hD
  have hz0 : 0<v 2:=hz.1.trans_le hz.2.1
  have hω:=OriginalSixteenTightSwitchedBoxes.omega_bounds m hm B (argument_bounds10 B hv hD)
  have hLo0 : (0 : ℝ)≤(OriginalSixteenTightSwitchedBoxes.omegaLower m B : ℝ) := by
    simp only [OriginalSixteenTightSwitchedBoxes.omegaLower,Rat.cast_max,Rat.cast_zero]
    exact le_max_left _ _
  have hU0 : (0 : ℝ)≤(OriginalSixteenTightSwitchedBoxes.omegaUpper m B : ℝ):=hLo0.trans (hω.1.trans hω.2)
  have hK : (0 : ℝ)≤P5OriginalCoefficientArithmetic.K0 := by norm_num [P5OriginalCoefficientArithmetic.K0]
  simp only [U1011OriginalSixteenAnchorSlopeCertificates.baseLower,
    U1011OriginalSixteenAnchorSlopeCertificates.anchorUpper,Rat.cast_div,Rat.cast_mul,
    U1011OriginalSixteenAnchorSlopeCertificates.anchorK_cast,switchBase,switchedKernel,one_mul]
  exact ⟨(div_le_div_of_nonneg_left hLo0 hz0 hz.2.2).trans (div_le_div_of_nonneg_right hω.1 hz0.le),
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω.2 hK) hz0.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hK hU0) hz.1 hz.2.1)⟩

theorem candidateLower_le_actual10 (p : Policy) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ domain10) (he : TypedEligible p v) :
    (OriginalSixteenEnvelopeBoxBounds.candidateLower p B : ℝ)≤ordinaryKernel H248 residual p.val v := by
  by_cases hg : OriginalSixteenOrdinaryBoxBounds.PositiveGuards p B
  · simpa only [OriginalSixteenEnvelopeBoxBounds.candidateLower,if_pos hg] using
      (OriginalSixteenOrdinaryBoxBounds.actual_ordinary_bounds p B hg hv).1
  · simp only [OriginalSixteenEnvelopeBoxBounds.candidateLower,if_neg hg,Rat.cast_zero]
    exact ordinary_nonneg_D10 hD p.val ((OriginalSixteenEnvelopeBoxBounds.eligible_policy p v).mpr he)

theorem anchorTest_sound10 (m : ℕ) (hm : 0<m) (B : Box)
    (ht : U1011OriginalSixteenAnchorSlopeCertificates.anchorTest m B=true)
    {v : LogFour} (hv : v ∈ B.region) (hD : v ∈ domain10) :
    v ∈ anchorSwitchRegion P5OriginalCoefficientArithmetic.K0 := by
  have htest : U1011OriginalSixteenAnchorSlopeCertificates.AnchorTest m B:=of_decide_eq_true ht
  intro j hj he
  have hj16 : j<16:=Finset.mem_range.mp hj
  let p : Policy:=⟨j,hj16⟩
  have heP : TypedEligible p v := (OriginalSixteenEnvelopeBoxBounds.eligible_policy p v).mp he
  have hpossible : correlatedIneligibleTest p B≠true := fun hi => correlatedIneligibleTest_sound p B hi v hv heP
  have hQ:=htest p hpossible
  have hR : (U1011OriginalSixteenAnchorSlopeCertificates.anchorUpper m B : ℝ)≤
      (OriginalSixteenEnvelopeBoxBounds.candidateLower p B : ℝ) := by exact_mod_cast hQ
  exact (tight_switch_bounds10 m hm B hv hD).2.trans (hR.trans (candidateLower_le_actual10 p B hv hD heP))

def certified10 (n m : ℕ) : Finset (Index n):=(inner10 n).filter
  (fun j => U1011OriginalSixteenAnchorSlopeCertificates.anchorTest m (gridBox n j)=true)
def densityLower10 (n m : ℕ) (j : Index n) : ℚ:=
  U1011OriginalSixteenAnchorSlopeCertificates.densityLower n m j
def minorant10 (n m : ℕ) (j : Index n) : LogFour → ℝ:=
  (cell n j).indicator (fun _ => (densityLower10 n m j : ℝ))
def rationalSlopeLower10 (n m : ℕ) : ℚ:=∑ j ∈ certified10 n m,densityLower10 n m j*cellVolume n

theorem certified10_cell (n m : ℕ) (hm : 0<m) {j : Index n} (hj : j ∈ certified10 n m)
    {v : LogFour} (hv : v ∈ cell n j) : v ∈ domain10 ∧ v ∈ anchorSwitchRegion P5OriginalCoefficientArithmetic.K0 := by
  obtain ⟨hi,ht⟩:=Finset.mem_filter.mp hj
  have hd:=inner10_cell_subset n hi hv
  exact ⟨hd,anchorTest_sound10 m hm (gridBox n j) ht (cell_subset_closedBox n j hv) hd⟩

theorem weighted_cell_lower10 (n m : ℕ) (hm : 0<m) {j : Index n} (hj : j ∈ certified10 n m)
    {v : LogFour} (hv : v ∈ cell n j) :
    (densityLower10 n m j : ℝ)≤slopeIntegrand P5OriginalCoefficientArithmetic.K0 v := by
  have hD:=certified10_cell n m hm hj hv
  have hb:=(tight_switch_bounds10 m hm (gridBox n j) (cell_subset_closedBox n j hv) hD.1).1
  have hw:=(weight_bounds n j hv).1
  have hw0 : (0 : ℝ)≤(weightLower n j : ℝ) := by
    exact_mod_cast (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_hi_pos n j i)).le) : (0 : ℚ)≤weightLower n j)
  rw [slopeIntegrand,indicator_of_mem hD.2,U1011OriginalSixteenFullHarmonic.harmonicDensity_eq_prod]
  simpa only [densityLower10,U1011OriginalSixteenAnchorSlopeCertificates.densityLower,Rat.cast_mul,
    U1011OriginalSixteenRationalIntegralCertificates.weight] using
    mul_le_mul hb hw hw0 (switchBase_nonneg_D10 hD.1)

theorem rationalSlopeLower10_le_actual10 (n m : ℕ) (hm : 0<m) :
    (rationalSlopeLower10 n m : ℝ)≤anchorSlope10 P5OriginalCoefficientArithmetic.K0 := by
  have hf : Integrable (fun v => ∑ j ∈ certified10 n m,minorant10 n m j v):=
    integrable_finsetSum _ (fun j _ => cell_constant_integrable n j _)
  have hg : Integrable (domain10.indicator (slopeIntegrand P5OriginalCoefficientArithmetic.K0)):=
    (integrableOn_slopeIntegrand_D10 P5OriginalCoefficientArithmetic.K0).integrable_indicator measurableSet_domain10
  have hpoint (v : LogFour) : (∑ j ∈ certified10 n m,minorant10 n m j v)≤
      domain10.indicator (slopeIntegrand P5OriginalCoefficientArithmetic.K0) v := by
    by_cases hex : ∃ j ∈ certified10 n m,v ∈ cell n j
    · obtain ⟨j,hj,hvj⟩:=hex
      have hd:=certified10_cell n m hm hj hvj
      have heq : (∑ k ∈ certified10 n m,minorant10 n m k v)=minorant10 n m j v := by
        apply Finset.sum_eq_single j
        · intro k _ hkj
          exact indicator_of_notMem (fun hvk => hkj (cell_unique hvk hvj)) _
        · intro hn
          exact (hn hj).elim
      rw [heq,minorant10,indicator_of_mem hvj,indicator_of_mem hd.1]
      exact weighted_cell_lower10 n m hm hj hvj
    · have hz : (∑ j ∈ certified10 n m,minorant10 n m j v)=0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun hvj => hex ⟨j,hj,hvj⟩) _
      rw [hz]
      by_cases hd : v ∈ domain10
      · rw [indicator_of_mem hd]
        exact slopeIntegrand_nonneg_D10 _ hd
      · simp only [indicator_of_notMem hd,le_refl]
  calc
    (rationalSlopeLower10 n m : ℝ)=∑ j ∈ certified10 n m,((densityLower10 n m j*cellVolume n : ℚ) : ℝ) := by
      simp [rationalSlopeLower10]
    _ = ∑ j ∈ certified10 n m,∫ v,minorant10 n m j v := by
      apply Finset.sum_congr rfl
      intro j _
      exact (integral_cell_constant n j _).symm
    _ = ∫ v,∑ j ∈ certified10 n m,minorant10 n m j v:=
      (integral_finsetSum _ (fun j _ => cell_constant_integrable n j _)).symm
    _ ≤ ∫ v,domain10.indicator (slopeIntegrand P5OriginalCoefficientArithmetic.K0) v:=integral_mono hf hg hpoint
    _ = anchorSlope10 P5OriginalCoefficientArithmetic.K0:=integral_indicator measurableSet_domain10

/-- Low band remains UNMASKED; only the genuine D11 high-band program
uses its original17572-row complement guard. -/
def rationalJointSlopeLower (n10 m10 n11 m11 : ℕ) (S : Finset Row) : ℚ:=
  rationalSlopeLower10 n10 m10+U1011OriginalSixteenAnchorSlopeCertificates.rationalSlopeLower n11 m11 S

theorem rationalJointSlopeLower_le_actualJoint (n10 m10 n11 m11 : ℕ)
    (hm10 : 0<m10) (hm11 : 0<m11) (S : Finset Row) :
    (rationalJointSlopeLower n10 m10 n11 m11 S : ℝ)≤jointAnchorSlope P5OriginalCoefficientArithmetic.K0
      (U1011OriginalSixteenAnchorSlopeCertificates.rowMask S) := by
  simpa only [rationalJointSlopeLower,Rat.cast_add,jointAnchorSlope] using
    add_le_add (rationalSlopeLower10_le_actual10 n10 m10 hm10)
      (U1011OriginalSixteenAnchorSlopeCertificates.rationalSlopeLower_le_actualSlope n11 m11 hm11 S)

def jointSlopeCheck (n10 m10 n11 m11 : ℕ) (S : Finset Row) (lower : ℚ) : Bool:=
  decide (0<m10 ∧ 0<m11 ∧ lower≤rationalJointSlopeLower n10 m10 n11 m11 S)

theorem jointSlopeCheck_sound (n10 m10 n11 m11 : ℕ) (S : Finset Row) (lower : ℚ)
    (ht : jointSlopeCheck n10 m10 n11 m11 S lower=true) :
    (lower : ℝ)≤jointAnchorSlope P5OriginalCoefficientArithmetic.K0
      (U1011OriginalSixteenAnchorSlopeCertificates.rowMask S) := by
  have h : 0<m10 ∧ 0<m11 ∧ lower≤rationalJointSlopeLower n10 m10 n11 m11 S:=of_decide_eq_true ht
  have hL : (lower : ℝ)≤(rationalJointSlopeLower n10 m10 n11 m11 S : ℝ) := by exact_mod_cast h.2.2
  exact hL.trans (rationalJointSlopeLower_le_actualJoint n10 m10 n11 m11 h.1 h.2.1 S)

/-- A finite rational slope check feeds the TRUE both-band functional.
Neither a real slope bound nor feedback inequality is an input. -/
theorem joint_feedback_of_slopeCheck (n10 m10 n11 m11 : ℕ) (S : Finset Row) (lower : ℚ)
    (ht : jointSlopeCheck n10 m10 n11 m11 S lower=true)
    {k : ℝ} (hk : 0≤k) (hkk0 : k≤P5OriginalCoefficientArithmetic.K0) :
    jointCostIntegral k (U1011OriginalSixteenAnchorSlopeCertificates.rowMask S)≤
      jointCostIntegral P5OriginalCoefficientArithmetic.K0 (U1011OriginalSixteenAnchorSlopeCertificates.rowMask S)-
        (P5OriginalCoefficientArithmetic.K0-k)*(lower : ℝ) := by
  have hS:=jointSlopeCheck_sound n10 m10 n11 m11 S lower ht
  have hF:=joint_feedback hk hkk0 (U1011OriginalSixteenAnchorSlopeCertificates.rowMask S)
    (U1011OriginalSixteenAnchorSlopeCertificates.measurableSet_rowMask S)
  exact hF.trans (sub_le_sub_left (mul_le_mul_of_nonneg_left hS (sub_nonneg.mpr hkk0)) _)

theorem unmasked_jointSlopeCheck_sound (n10 m10 n11 m11 : ℕ) (lower : ℚ)
    (ht : jointSlopeCheck n10 m10 n11 m11 ∅ lower=true) :
    (lower : ℝ)≤jointAnchorSlope P5OriginalCoefficientArithmetic.K0 ∅ := by
  simpa only [U1011OriginalSixteenAnchorSlopeCertificates.rowMask_empty] using
    jointSlopeCheck_sound n10 m10 n11 m11 ∅ lower ht

/-- Original E0/E1 labels keep their literal high-band row mask.
D10 remains unmasked; no passing check is asserted. -/
theorem e0_jointSlopeCheck_sound (n10 m10 n11 m11 : ℕ) (lower : ℚ)
    (ht : jointSlopeCheck n10 m10 n11 m11 U1011OriginalPairedFixedMaskHarmonic.e0Rows lower=true) :
    (lower : ℝ)≤jointAnchorSlope P5OriginalCoefficientArithmetic.K0
      Certificates.PairedV2.FullMask.P1E0E1.e0PairRegion := by
  simpa only [U1011OriginalSixteenAnchorSlopeCertificates.rowMask,
    U1011OriginalPairedFixedMaskHarmonic.outerUnion_e0] using
    jointSlopeCheck_sound n10 m10 n11 m11 U1011OriginalPairedFixedMaskHarmonic.e0Rows lower ht

theorem e1_jointSlopeCheck_sound (n10 m10 n11 m11 : ℕ) (lower : ℚ)
    (ht : jointSlopeCheck n10 m10 n11 m11 U1011OriginalPairedFixedMaskHarmonic.e1Rows lower=true) :
    (lower : ℝ)≤jointAnchorSlope P5OriginalCoefficientArithmetic.K0
      Certificates.PairedV2.FullMask.P1E0E1.e1PairRegion := by
  simpa only [U1011OriginalSixteenAnchorSlopeCertificates.rowMask,
    U1011OriginalPairedFixedMaskHarmonic.outerUnion_e1] using
    jointSlopeCheck_sound n10 m10 n11 m11 U1011OriginalPairedFixedMaskHarmonic.e1Rows lower ht

theorem adopted_jointSlopeCheck_sound (n10 m10 n11 m11 : ℕ) (lower : ℚ)
    (ht : jointSlopeCheck n10 m10 n11 m11 (Finset.univ : Finset Row) lower=true) :
    (lower : ℝ)≤jointAnchorSlope P5OriginalCoefficientArithmetic.K0
      Certificates.PairedV2.FullMask.P1E0E1.pairRegion := by
  simpa only [U1011OriginalSixteenAnchorSlopeCertificates.rowMask,
    U1011OriginalPairedFixedMaskHarmonic.outerUnion_all] using
    jointSlopeCheck_sound n10 m10 n11 m11 (Finset.univ : Finset Row) lower ht

end
end ImbalancedChen.P5Z.U1011OriginalSixteenJointSlopeCertificates
