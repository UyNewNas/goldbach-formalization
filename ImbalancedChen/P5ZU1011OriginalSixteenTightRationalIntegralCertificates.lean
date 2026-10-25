import ImbalancedChen.P5ZU1011OriginalSixteenRationalIntegralCertificates
import ImbalancedChen.P5ZU1011OriginalSixteenTightSwitchedBoxes
import ImbalancedChen.P5ZU1011OriginalSixteenCorrelatedBoxCertificates

/-!
# Explicit tight rational certificates for the actual original16 integral

SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

The switched endpoints use the proved GENERATED Buchstab interval program,
not the coarse [1/2,1] range and not a supplied switched-cell bound. The
ordinary endpoints use the literal finite H248 interval extrema. ALL16
policy gates, including both W gates, use correlated actual affine tests.

The automatic original4D grid, domain cover, disjoint ownership, volumes,
weighted integrability and exact fullIntegral dictionary are reused from
the genuine preceding source. There is no hCover/hCellBound/hMean premise.
This leaf proves program soundness. It does not claim a saved finite
check passes, and does not assert an unproved enclosure-width limit.
-/

namespace ImbalancedChen.P5Z.U1011OriginalSixteenTightRationalIntegralCertificates

noncomputable section

open Set MeasureTheory U11Integral Part5UpperTables
open U1011OriginalSixteenPolicyBank U1011OriginalSixteenPolicyBank.BoxCertificates
open U1011OriginalSixteenPolicyBank.EligibilityGridCertificates
open U1011OriginalSixteenRationalGridGeometry U1011OriginalSourceGeometryMesh
open U1011OriginalSixteenRationalIntegralCertificates OriginalSixteenOrdinaryBoxBounds
open OriginalSixteenEnvelopeBoxBounds
open scoped BigOperators
open Classical

def possible (p : Policy) (B : Box) : Prop := correlatedIneligibleTest p B ≠ true
def certified (p : Policy) (B : Box) : Prop :=
  correlatedEligibleTest p B = true ∧ PositiveGuards p B

instance (p : Policy) (B : Box) : Decidable (possible p B) := by unfold possible; infer_instance
instance (p : Policy) (B : Box) : Decidable (certified p B) := by unfold certified; infer_instance

def lowerValues (m : ℕ) (B : Box) : Finset ℚ :=
  insert (OriginalSixteenTightSwitchedBoxes.switchedLower m B)
    ((Finset.univ.filter (fun p : Policy => possible p B)).image (fun p => candidateLower p B))

def upperValues (m : ℕ) (B : Box) : Finset ℚ :=
  insert (OriginalSixteenTightSwitchedBoxes.switchedUpper m B)
    ((Finset.univ.filter (fun p : Policy => certified p B)).image (fun p => ordinaryUpper p B))

theorem lowerValues_nonempty (m : ℕ) (B : Box) : (lowerValues m B).Nonempty :=
  Finset.insert_nonempty _ _
theorem upperValues_nonempty (m : ℕ) (B : Box) : (upperValues m B).Nonempty :=
  Finset.insert_nonempty _ _

def boxLower (m : ℕ) (B : Box) : ℚ := (lowerValues m B).min' (lowerValues_nonempty m B)
def boxUpper (m : ℕ) (B : Box) : ℚ := (upperValues m B).min' (upperValues_nonempty m B)

theorem possible_of_actual_eligible (p : Policy) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (he : TypedEligible p v) : possible p B := by
  intro ht
  exact correlatedIneligibleTest_sound p B ht v hv he

theorem lower_le_switched (m : ℕ) (hm : 0 < m) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ sourceDomain) :
    (boxLower m B : ℝ) ≤ switchedKernel currentK LiLiuPrereqBuchstab.buchstab v := by
  have hQ : boxLower m B ≤ OriginalSixteenTightSwitchedBoxes.switchedLower m B :=
    Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hR : (boxLower m B : ℝ) ≤
      (OriginalSixteenTightSwitchedBoxes.switchedLower m B : ℝ) := by exact_mod_cast hQ
  exact hR.trans (OriginalSixteenTightSwitchedBoxes.switched_box_bounds m hm ∅ B hv hD).1

theorem lower_le_ordinary (m : ℕ) (p : Policy) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ sourceDomain) (he : TypedEligible p v) :
    (boxLower m B : ℝ) ≤ ordinaryKernel H248 residual p.val v := by
  have hp := possible_of_actual_eligible p B hv he
  have hmem : candidateLower p B ∈ lowerValues m B := Finset.mem_insert_of_mem
    (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩)
  have hQ : boxLower m B ≤ candidateLower p B := Finset.min'_le _ _ hmem
  have hR : (boxLower m B : ℝ) ≤ (candidateLower p B : ℝ) := by exact_mod_cast hQ
  exact hR.trans (candidateLower_le_actual ∅ p B hv hD he)

theorem lower_bound_sound (m : ℕ) (hm : 0 < m) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ sourceDomain) :
    (boxLower m B : ℝ) ≤ actualEnvelope v := by
  unfold actualEnvelope
  rw [envelope_eq_min]
  apply Finset.le_min'
  intro q hq
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hq
  rcases Finset.mem_insert.mp hc with rfl | hc
  · simpa only [guarded, if_pos rfl] using lower_le_switched m hm B hv hD
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
    have hj16 : j < 16 := Finset.mem_range.mp hj
    let p : Policy := ⟨j, hj16⟩
    by_cases he : eligible j v
    · have heP : TypedEligible p v := (eligible_policy p v).mp he
      simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_pos he] using
        lower_le_ordinary m p B hv hD heP
    · simpa only [guarded, Nat.succ_ne_zero, if_false, Nat.pred_succ, if_neg he] using
        lower_le_switched m hm B hv hD

theorem upper_bound_sound (m : ℕ) (hm : 0 < m) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ sourceDomain) :
    actualEnvelope v ≤ (boxUpper m B : ℝ) := by
  have hmem := Finset.min'_mem (upperValues m B) (upperValues_nonempty m B)
  change boxUpper m B ∈ upperValues m B at hmem
  rcases Finset.mem_insert.mp hmem with hs | hp
  · rw [hs]
    exact (guarded_envelope_le_switched bank eligible
      (switchedKernel currentK LiLiuPrereqBuchstab.buchstab) (ordinaryKernel H248 residual) v).trans
      (OriginalSixteenTightSwitchedBoxes.switched_box_bounds m hm ∅ B hv hD).2
  · obtain ⟨p, hp, heq⟩ := Finset.mem_image.mp hp
    have hc := (Finset.mem_filter.mp hp).2
    have he := correlatedEligibleTest_sound p B hc.1 v hv
    rw [← heq]
    exact (actualEnvelope_le_eligible p he).trans (actual_ordinary_bounds p B hc.2 hv).2

theorem box_bounds (m : ℕ) (hm : 0 < m) (B : Box) {v : LogFour}
    (hv : v ∈ B.region) (hD : v ∈ sourceDomain) :
    (boxLower m B : ℝ) ≤ actualEnvelope v ∧ actualEnvelope v ≤ (boxUpper m B : ℝ) :=
  ⟨lower_bound_sound m hm B hv hD, upper_bound_sound m hm B hv hD⟩

def densityLower (n m : ℕ) (j : Index n) : ℚ :=
  max 0 (boxLower m (gridBox n j)) * weightLower n j
def densityUpper (n m : ℕ) (j : Index n) : ℚ :=
  max 0 (boxUpper m (gridBox n j)) * weightUpper n j

theorem densityUpper_nonneg (n m : ℕ) (j : Index n) : 0 ≤ densityUpper n m j :=
  mul_nonneg (le_max_left _ _) (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_lo_pos n j i)).le))

theorem weighted_cell_bounds (n m : ℕ) (hm : 0 < m) (j : Index n) {v : LogFour}
    (hv : v ∈ cell n j) (hD : v ∈ sourceDomain) :
    (densityLower n m j : ℝ) ≤ weightedKernel v ∧
      weightedKernel v ≤ (densityUpper n m j : ℝ) := by
  have hB := cell_subset_closedBox n j hv
  have hc := box_bounds m hm (gridBox n j) hB hD
  have hw := weight_bounds n j hv
  have hE0 := actualEnvelope_nonneg hD
  have hw0 := weight_nonneg_on_domain hD
  have hWL0 : (0 : ℝ) ≤ (weightLower n j : ℝ) := by
    exact_mod_cast (Finset.prod_nonneg (fun i _ => (one_div_pos.mpr (grid_hi_pos n j i)).le) :
      (0 : ℚ) ≤ weightLower n j)
  have hEL : ((max (0 : ℚ) (boxLower m (gridBox n j)) : ℚ) : ℝ) ≤ actualEnvelope v := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact max_le hE0 hc.1
  have hEU : actualEnvelope v ≤ ((max (0 : ℚ) (boxUpper m (gridBox n j)) : ℚ) : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact hc.2.trans (le_max_right _ _)
  have hEU0 : (0 : ℝ) ≤ ((max (0 : ℚ) (boxUpper m (gridBox n j)) : ℚ) : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero]
    exact le_max_left _ _
  simp only [densityLower, densityUpper, Rat.cast_mul, weightedKernel]
  exact ⟨mul_le_mul hEL hw.1 hWL0 hE0, mul_le_mul hEU hw.2 hw0 hEU0⟩

def minorant (n m : ℕ) (j : Index n) : LogFour → ℝ :=
  (cell n j).indicator (fun _ => (densityLower n m j : ℝ))
def majorant (n m : ℕ) (j : Index n) : LogFour → ℝ :=
  (cell n j).indicator (fun _ => (densityUpper n m j : ℝ))

theorem majorant_nonneg (n m : ℕ) (j : Index n) (v : LogFour) : 0 ≤ majorant n m j v := by
  by_cases hv : v ∈ cell n j
  · rw [majorant, indicator_of_mem hv]
    exact_mod_cast densityUpper_nonneg n m j
  · simp only [majorant, indicator_of_notMem hv, le_refl]

def rationalLower (n m : ℕ) : ℚ :=
  ∑ j ∈ inner n, densityLower n m j * cellVolume n
def rationalUpper (n m : ℕ) : ℚ :=
  ∑ j ∈ outer n, densityUpper n m j * cellVolume n

theorem actual_fullIntegral_le_rationalUpper (n m : ℕ) (hm : 0 < m) :
    fullIntegral ≤ (rationalUpper n m : ℝ) := by
  have hg : Integrable (fun v => ∑ j ∈ outer n, majorant n m j v) :=
    integrable_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
  have hpoint (v : LogFour) : sourceDomain.indicator weightedKernel v ≤
      ∑ j ∈ outer n, majorant n m j v := by
    by_cases hv : v ∈ sourceDomain
    · obtain ⟨j, hj, hvj⟩ := domain_outer_cover n hv
      rw [indicator_of_mem hv]
      calc
        weightedKernel v ≤ (densityUpper n m j : ℝ) := (weighted_cell_bounds n m hm j hvj hv).2
        _ = majorant n m j v := (indicator_of_mem hvj _).symm
        _ ≤ _ := Finset.single_le_sum (fun k _ => majorant_nonneg n m k v) hj
    · rw [indicator_of_notMem hv]
      exact Finset.sum_nonneg (fun j _ => majorant_nonneg n m j v)
  calc
    fullIntegral = ∫ v, sourceDomain.indicator weightedKernel v :=
      (integral_indicator sourceDomain_measurable).symm
    _ ≤ ∫ v, ∑ j ∈ outer n, majorant n m j v :=
      integral_mono weighted_indicator_integrable hg hpoint
    _ = ∑ j ∈ outer n, ∫ v, majorant n m j v :=
      integral_finsetSum (outer n) (fun j _ => cell_constant_integrable n j _)
    _ = ∑ j ∈ outer n, ((densityUpper n m j * cellVolume n : ℚ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact integral_cell_constant n j _
    _ = (rationalUpper n m : ℝ) := by simp [rationalUpper]

theorem rationalLower_le_actual_fullIntegral (n m : ℕ) (hm : 0 < m) :
    (rationalLower n m : ℝ) ≤ fullIntegral := by
  have hf : Integrable (fun v => ∑ j ∈ inner n, minorant n m j v) :=
    integrable_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)
  have hpoint (v : LogFour) : (∑ j ∈ inner n, minorant n m j v) ≤
      sourceDomain.indicator weightedKernel v := by
    by_cases hex : ∃ j ∈ inner n, v ∈ cell n j
    · obtain ⟨j, hj, hvj⟩ := hex
      have hvD := inner_cell_subset_domain n hj hvj
      have heq : (∑ k ∈ inner n, minorant n m k v) = minorant n m j v := by
        apply Finset.sum_eq_single j
        · intro k hk hkj
          exact indicator_of_notMem (fun hvk => hkj (cell_unique hvk hvj)) _
        · intro hnot
          exact (hnot hj).elim
      rw [heq, minorant, indicator_of_mem hvj, indicator_of_mem hvD]
      exact (weighted_cell_bounds n m hm j hvj hvD).1
    · have hz : (∑ j ∈ inner n, minorant n m j v) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun hvj => hex ⟨j, hj, hvj⟩) _
      rw [hz]
      exact weighted_indicator_nonneg v
  calc
    (rationalLower n m : ℝ) = ∑ j ∈ inner n, ((densityLower n m j * cellVolume n : ℚ) : ℝ) := by
      simp [rationalLower]
    _ = ∑ j ∈ inner n, ∫ v, minorant n m j v := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (integral_cell_constant n j _).symm
    _ = ∫ v, ∑ j ∈ inner n, minorant n m j v :=
      (integral_finsetSum (inner n) (fun j _ => cell_constant_integrable n j _)).symm
    _ ≤ ∫ v, sourceDomain.indicator weightedKernel v :=
      integral_mono hf weighted_indicator_integrable hpoint
    _ = fullIntegral := integral_indicator sourceDomain_measurable

def directedCheck (nL mL nU mU : ℕ) (lower upper : ℚ) : Bool := decide
  (lower ≤ rationalLower nL mL ∧ rationalUpper nU mU ≤ upper)

theorem directedCheck_sound (nL mL nU mU : ℕ) (lower upper : ℚ)
    (hmL : 0 < mL) (hmU : 0 < mU)
    (hcheck : directedCheck nL mL nU mU lower upper = true) :
    (lower : ℝ) ≤ fullIntegral ∧ fullIntegral ≤ (upper : ℝ) := by
  have hc : lower ≤ rationalLower nL mL ∧ rationalUpper nU mU ≤ upper := of_decide_eq_true hcheck
  have hL : (lower : ℝ) ≤ (rationalLower nL mL : ℝ) := by exact_mod_cast hc.1
  have hU : (rationalUpper nU mU : ℝ) ≤ (upper : ℝ) := by exact_mod_cast hc.2
  exact ⟨hL.trans (rationalLower_le_actual_fullIntegral nL mL hmL),
    (actual_fullIntegral_le_rationalUpper nU mU hmU).trans hU⟩

end

end ImbalancedChen.P5Z.U1011OriginalSixteenTightRationalIntegralCertificates
