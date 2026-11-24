import ImbalancedChen.P5OriginalTaylorSameBoxGeometry
import ImbalancedChen.P5OriginalTaylorWeightedHessian
import ImbalancedChen.P5OriginalTaylorRationalData

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original full weighted five-dimensional Taylor lower bound, for the
same accepted cell and its same signed raw15+W integrand. All derivative,
continuity and Hessian inputs of the tensor lemma are discharged by the
actual affine extension and the original pilot formulas. The terminal
assumes only the original finite rational smooth-box tests.
-/
namespace ImbalancedChen.P5OriginalTaylorActualMidpointIntegral
noncomputable section
open Set MeasureTheory
open scoped BigOperators Classical
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OldFifthPointwiseQ P5OriginalTaylorActualSignedKernel
open P5OriginalTaylorAffineBranchBinding P5OriginalTaylorAffineRatioDerivatives
open P5OriginalTaylorProfileDerivatives P5OriginalTaylorWeightDerivatives
open P5OriginalTaylorWeightedAxisCalculus P5OriginalTaylorWeightedHessian
open P5OriginalTaylorFiveDimensionalMidpoint P5OriginalTaylorSameBoxGeometry
open P5OriginalTaylorRationalData

/-- Actual same-box signed Taylor integral. The hypotheses are geometric
branch/range data, never an integral, derivative or Hessian bound. Endpoint
seams use the SAME affine extension, which agrees on the whole closed box. -/
theorem original_same_box_midpoint_lower
    (raw : FifthWireRow) (newSide : Bool) (oldSides : OldSides) (selected : Option OldMask)
    (hbranch : BranchFacts raw newSide oldSides selected)
    (hg : 0 < raw.grid) (hl : ∀ k, 0 < (raw.lower k : ℝ))
    (a snMax soMax delta : ℝ) (ha2 : 2 ≤ a)
    (hrange : ∀ t ∈ rawClosedBox raw,
      a ≤ affineArgument (selectedOldPlane oldSides selected) t ∧
      affineArgument (selectedOldPlane oldSides selected) t ≤ affineArgument (newPlane raw newSide) t ∧
      affineArgument (newPlane raw newSide) t ≤ 4 ∧
      affineArgument (newPlane raw newSide) t ≤ snMax ∧
      affineArgument (selectedOldPlane oldSides selected) t ≤ soMax ∧
      affineArgument (newPlane raw newSide) t -
        affineArgument (selectedOldPlane oldSides selected) t ≤ delta) :
    rawVolume raw * (originalTaylorMidpointLower raw (rawMidpoint raw) -
      rawRemainder raw (pilotHessian raw (newPlane raw newSide)
        (selectedOldPlane oldSides selected) a snMax soMax delta)) ≤
      ∫ t in raw.originalBox, originalTaylorSignedKernel raw t := by
  let new := newPlane raw newSide
  let old := selectedOldPlane oldSides selected
  let M := pilotHessian raw new old a snMax soMax delta
  have hp (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) : ∀ k, 0 < t k :=
    fun k => (hl k).trans_le (ht k).1
  have haxis (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (i : Fin 5)
      (x : ℝ) (hx : x ∈ Icc (raw.lower i : ℝ) (raw.upper i : ℝ)) :
      t 4 ≠ 0 ∧ x ≠ 0 ∧ 1 < axisArgument new t i x ∧ 1 < axisArgument old t i x := by
    have hu := update_mem_rawClosedBox raw t ht i x hx
    rcases hrange (Function.update t i x) hu with ⟨hao, hon, _, _, _, _⟩
    have hn : 1 < affineArgument new (Function.update t i x) := by
      dsimp [new]
      linarith
    have ho : 1 < affineArgument old (Function.update t i x) := by
      dsimp [old]
      linarith
    exact ⟨(hp t ht 4).ne', ((hl i).trans_le hx.1).ne',
      by simpa only [original_argument_on_axis] using hn,
      by simpa only [original_argument_on_axis] using ho⟩
  have hc := continuousOn_affineTaylorSignedKernel raw new old hl (by
    intro t ht
    rcases hrange t ht with ⟨hao, hon, _, _, _, _⟩
    constructor <;> dsimp [new, old] <;> linarith)
  have hF := five_dimensional_midpoint_lower
    (fun i => (raw.lower i : ℝ)) (fun i => (raw.upper i : ℝ)) M
    (affineTaylorSignedKernel new old) (axisKernelSlope new old) (axisKernelCurvature new old)
    (raw_lower_le_upper raw hg) (by rwa [← rawClosedBox_eq_Icc])
    (by
      intro t ht i x hx
      have ht' : t ∈ rawClosedBox raw := by rwa [rawClosedBox_eq_Icc]
      rcases haxis t ht' i x hx with ⟨h4, hx0, hn, ho⟩
      simpa only [original_affine_kernel_on_axis] using
        hasDerivAt_axisKernel new old t i x h4 hx0 hn ho)
    (by
      intro t ht i x hx
      have ht' : t ∈ rawClosedBox raw := by rwa [rawClosedBox_eq_Icc]
      rcases haxis t ht' i x hx with ⟨h4, hx0, hn, ho⟩
      exact hasDerivAt_axisKernelSlope new old t i x h4 hx0 hn ho)
    (by
      intro t ht i
      have ht' : t ∈ rawClosedBox raw := by rwa [rawClosedBox_eq_Icc]
      exact continuousOn_axisKernelCurvature new old t i _ _ (hp t ht' 4).ne'
        (fun x hx => (haxis t ht' i x hx).2))
    (by
      intro t ht i x hx
      have ht' : t ∈ rawClosedBox raw := by rwa [rawClosedBox_eq_Icc]
      have hu := update_mem_rawClosedBox raw t ht' i x hx
      rcases hrange (Function.update t i x) hu with ⟨hao, hon, hn4, hnMax, hoMax, hdelta⟩
      have hb := original_selected_axisKernelCurvature_le_pilotHessian raw newSide oldSides
        selected a snMax soMax delta hl (Function.update t i x) hu i
        ha2 hao hon hn4 hnMax hoMax hdelta
      simpa only [Function.update_same, axisKernelCurvature_rebase] using hb)
  have hAffine : rawVolume raw *
      (affineTaylorSignedKernel new old (rawMidpoint raw)-rawRemainder raw M) ≤
        ∫ t in rawClosedBox raw, affineTaylorSignedKernel new old t := by
    simpa only [rawVolume, rawWidth, rawMidpoint, rawRemainder, rawClosedBox_eq_Icc] using hF
  have hcm := rawMidpoint_mem raw hg
  have hnew : originalTaylorNewArgument raw (rawMidpoint raw) =
      affineArgument new (rawMidpoint raw) := by
    unfold originalTaylorNewArgument
    rw [original_new_eq_affine raw newSide hbranch.new_active _ hcm]
    rfl
  have hold : originalTaylorOldArgument (rawMidpoint raw) =
      affineArgument old (rawMidpoint raw) := by
    unfold originalTaylorOldArgument
    rw [original_old_eq_selected_affine raw newSide oldSides selected hbranch _ hcm]
    rfl
  have hmid := originalTaylorMidpointLower_le_signed raw (rawMidpoint raw) (hp _ hcm)
    (by rw [hnew]; exact ha2.trans ((hrange _ hcm).1.trans (hrange _ hcm).2.1))
    (by rw [hold]; exact ha2.trans (hrange _ hcm).1)
  rw [original_signed_kernel_eq_affine raw newSide oldSides selected hbranch _ hcm] at hmid
  have hle := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hmid (rawRemainder raw M)) (rawVolume_nonneg raw hg)
  have hmeas : MeasurableSet (rawClosedBox raw) := by
    rw [rawClosedBox_eq_Icc]
    exact measurableSet_Icc
  have hInt : (∫ t in rawClosedBox raw, originalTaylorSignedKernel raw t) =
      ∫ t in rawClosedBox raw, affineTaylorSignedKernel new old t := by
    apply setIntegral_congr_fun hmeas
    intro t ht
    exact original_signed_kernel_eq_affine raw newSide oldSides selected hbranch t ht
  rw [originalBox_integral_eq_closed raw, hInt]
  exact hle.trans hAffine

/-- Rational-to-real midpoint dictionary, using the physical cell endpoints. -/
theorem midpointQ_cast (raw : FifthWireRow) :
    (fun i => (P5OriginalTaylorRationalData.midpointQ raw i : ℝ)) = rawMidpoint raw := by
  ext i
  simp [P5OriginalTaylorRationalData.midpointQ, rawMidpoint]

theorem weightQ_cast (t : Fin 5 → ℚ) :
    (weightQ t : ℝ) = originalTaylorWeight (fun i => (t i : ℝ)) := by
  rw [originalTaylorWeight_eq_source]
  simp [weightQ]

theorem m1Q_cast (raw : FifthWireRow) :
    (m1Q raw : ℝ) = pilotM1 (aMin raw : ℝ) := by
  simp [m1Q, pilotM1, logLower14Q_cast]

theorem m2Q_cast (raw : FifthWireRow) :
    (m2Q raw : ℝ) = pilotM2 (aMin raw : ℝ) := by
  simp [m2Q, pilotM2]

theorem residualCoefficientQ_cast (a : Affine5) (i : Fin 5) :
    (residualCoefficientQ a i : ℝ) = residualCoefficient a i := by
  simp [residualCoefficientQ, residualCoefficient]

theorem DQ_cast (raw : FifthWireRow) (a : Affine5) (sMax : ℚ) (i : Fin 5) :
    (DQ raw a sMax i : ℝ) = pilotD raw a (sMax : ℝ) i := by
  by_cases hi : i = 4 <;>
    simp [DQ, pilotD, hi, residualCoefficientQ_cast]

theorem EQ_cast (raw : FifthWireRow) (a : Affine5) (sMax : ℚ) (i : Fin 5) :
    (EQ raw a sMax i : ℝ) = pilotE raw a (sMax : ℝ) i := by
  by_cases hi : i = 4 <;> simp [EQ, pilotE, hi, DQ_cast]

theorem TQ_cast (raw : FifthWireRow) (i : Fin 5) :
    (TQ raw i : ℝ) = pilotT raw (newAffine raw) (oldAffine raw) (gap raw : ℝ) i := by
  by_cases hi : i = 4 <;>
    simp [TQ, pilotT, hi, residualCoefficientQ_cast]

theorem kQ_cast (raw : FifthWireRow) (i : Fin 5) :
    (kQ raw i : ℝ) = pilotK raw i := by
  by_cases hi : i = 4 <;> simp [kQ, powerQ, pilotK, axisPower, hi]

theorem qQ_cast (raw : FifthWireRow) (i : Fin 5) :
    (qQ raw i : ℝ) = pilotR raw i := by
  by_cases hi : i = 4 <;> simp [qQ, powerQ, pilotR, axisPower, hi]

theorem wmaxQ_cast (raw : FifthWireRow) :
    (wmaxQ raw : ℝ) = pilotWMax raw := by
  exact weightQ_cast raw.lower

/-- Exact M[i] identity, including the minimum that retains the new/old
first-derivative cancellation and the last-coordinate power TWO. -/
theorem hessianQ_cast (raw : FifthWireRow) (i : Fin 5) :
    (hessianQ raw i : ℝ) =
      pilotHessian raw (newAffine raw) (oldAffine raw) (aMin raw : ℝ)
        (newMax raw : ℝ) (oldMax raw : ℝ) (gap raw : ℝ) i := by
  simp only [hessianQ, pilotHessian, pilotSecondBound, pilotFirstBound,
    Rat.cast_mul, Rat.cast_add, Rat.cast_ofNat, Rat.cast_min,
    wmaxQ_cast, qQ_cast, kQ_cast, m1Q_cast, m2Q_cast,
    DQ_cast, EQ_cast, TQ_cast, pow_two]

/-- Actual original M[i] instance. The only input is the same finite
smooth-box predicate used for the stored Taylor branch; no derivative
estimate is an input. This also pins S05's free analytic parameters to
S07's original rational new/old extrema and correlated gap. -/
theorem actual_hessian_bound (raw : FifthWireRow) (h : TaylorFiniteFacts raw)
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (i : Fin 5) :
    |axisKernelCurvature (newAffine raw) (oldAffine raw) t i (t i)| ≤
      (hessianQ raw i : ℝ) := by
  rw [hessianQ_cast]
  have hl : ∀ k, 0 < (raw.lower k : ℝ) := fun k => by exact_mod_cast h.2.1 k
  rcases actual_ranges raw h t ht with ⟨_, ha2, hao, hon, hn4, hnMax, hoMax, hdelta⟩
  exact original_selected_axisKernelCurvature_le_pilotHessian raw (newSide raw)
    (oldSides raw) (selected raw) (aMin raw : ℝ) (newMax raw : ℝ)
    (oldMax raw : ℝ) (gap raw : ℝ) hl t ht i ha2 hao hon.le hn4 hnMax hoMax hdelta

/-- The original lower/upper log signs at the actual midpoint. -/
theorem midpointLowerQ_cast (raw : FifthWireRow) (hbranch : BranchChecks raw)
    (hg : 0 < raw.grid) :
    (midpointLowerQ raw : ℝ) = originalTaylorMidpointLower raw (rawMidpoint raw) := by
  have hcm := rawMidpoint_mem raw hg
  have hn : (newArgumentQ raw (P5OriginalTaylorRationalData.midpointQ raw) : ℝ) =
      originalTaylorNewArgument raw (rawMidpoint raw) := by
    rw [newArgumentQ, argumentQ_cast, midpointQ_cast]
    unfold originalTaylorNewArgument
    rw [original_new_eq_affine raw (newSide raw) (branchFacts raw hbranch).new_active _ hcm]
    rfl
  have ho : (oldArgumentQ raw (P5OriginalTaylorRationalData.midpointQ raw) : ℝ) =
      originalTaylorOldArgument (rawMidpoint raw) := by
    rw [oldArgumentQ, argumentQ_cast, midpointQ_cast]
    unfold originalTaylorOldArgument
    rw [original_old_eq_selected_affine raw (newSide raw) (oldSides raw) (selected raw)
      (branchFacts raw hbranch) _ hcm]
    rfl
  simp only [midpointLowerQ, originalTaylorMidpointLower,
    P5OriginalTaylorLogBounds.midpointLower, Rat.cast_mul, Rat.cast_sub, Rat.cast_div,
    Rat.cast_one, weightQ_cast, midpointQ_cast, logLower14Q_cast, logUpper14Q_cast, hn, ho]

/-- Exact rational volume and 1/24 remainder, with no Chen renormalization
or reciprocal-prime mass applied after averaging. -/
theorem taylorLowerQ_cast (raw : FifthWireRow) (hbranch : BranchChecks raw)
    (hg : 0 < raw.grid) :
    (taylorLowerQ raw : ℝ) = rawVolume raw *
      (originalTaylorMidpointLower raw (rawMidpoint raw) -
        rawRemainder raw (pilotHessian raw (newAffine raw) (oldAffine raw)
          (aMin raw : ℝ) (newMax raw : ℝ) (oldMax raw : ℝ) (gap raw : ℝ))) := by
  rw [rawVolume_eq_grid_power, rawRemainder_eq_pilot]
  simp [taylorLowerQ, remainderQ, widthQ, midpointLowerQ_cast raw hbranch hg,
    hessianQ_cast]

/-- Actual producer formula -> its genuine same-box signed integral.
Every analytic input is supplied internally; the caller gives only the
finite rational original smooth-box tests, suitable for archive evaluation. -/
theorem original_taylorLowerQ_le_signedIntegral (raw : FifthWireRow)
    (h : TaylorFiniteFacts raw) :
    (taylorLowerQ raw : ℝ) ≤
      ∫ t in raw.originalBox, originalTaylorSignedKernel raw t := by
  have hg : 0 < raw.grid := by rw [h.1]; norm_num
  have hl : ∀ i, 0 < (raw.lower i : ℝ) := fun i => by exact_mod_cast h.2.1 i
  have hb : BranchChecks raw := h.2.2.1
  rw [taylorLowerQ_cast raw hb hg]
  apply original_same_box_midpoint_lower raw (newSide raw) (oldSides raw) (selected raw)
    (branchFacts raw hb) hg hl (aMin raw : ℝ) (newMax raw : ℝ) (oldMax raw : ℝ)
      (gap raw : ℝ)
  · exact_mod_cast h.2.2.2.1
  · intro t ht
    rcases actual_ranges raw h t ht with ⟨_, _, hao, hon, hn4, hnMax, hoMax, hdelta⟩
    exact ⟨hao, hon.le, hn4, hnMax, hoMax, hdelta⟩

end
end ImbalancedChen.P5OriginalTaylorActualMidpointIntegral

