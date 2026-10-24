import ImbalancedChen.P5U6RetainedAdoptedIntegral

/-!
SOURCE_ONLY / UNCOMPILED. Exact slicing bridge for the original Runbo U6
enhancement. Here u is the first prime exponent and t the second. The
correction uses R = 1/2-u-t, and the Chen-quarter coefficient cancels the
single factor 4 in the full kernel. The adopted closed-cell lookup is replaced
by the half-open table only under an integral, using the proved null profile
walls. No arithmetic mean or numerical L6 enclosure is asserted.
-/

namespace ImbalancedChen.P5U6OriginalSlicedIntegralSourceOnly

noncomputable section

open MeasureTheory Set
open scoped BigOperators
open Classical
open P5U6RunboProductSlicesSourceOnly
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open P5U6AdoptedH248BindingSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly

abbrev Point := Fin 2 → ℝ

/-- The original h248 weight has the exact corrected product slices, with
the inclusive product wall and both half-open prime bands unchanged. -/
theorem originalWeight_integral_eq_nested (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, originalWeight x) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        ∫ t in productSlice eta u, originalWeight ![u, t] :=
  integral_productDomain_eq_nested eta originalWeight integrableOn_originalWeight

/-- Every weighted h248 band retains the same moving product slices. -/
theorem originalBandWeight_integral_eq_nested (lo hi eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta ∩ profileBand lo hi,
        originalWeight x) =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        ∫ t in productSlice eta u,
          (profileBand lo hi).indicator originalWeight ![u, t] := by
  rw [← setIntegral_indicator (measurableSet_profileBand lo hi)]
  exact integral_productDomain_eq_nested eta
    ((profileBand lo hi).indicator originalWeight)
    (integrableOn_originalBandWeight lo hi)

/-- The actual adopted closed-cell floor can be sliced exactly after its
proved a.e. identification with the finite half-open floor. The RHS is a
genuine iterated integral of the original R-denominator kernel. -/
theorem adopted_full_zero_eq_original_split :
    fullIntegral 0 =
      ∫ u in Ico (417 / 5000 : ℝ) (19 / 125),
        if u ≤ (243 / 2500 : ℝ) then
          ∫ t in Ico (19 / 125 : ℝ) (59 / 250),
            originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) ![u, t]
        else
          ∫ t in Icc (19 / 125 : ℝ) ((833 / 2500 : ℝ) - u),
            originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) ![u, t] := by
  calc
    fullIntegral 0 =
        ∫ x in currentChenUpsilon6LogDomain 0,
          originalEnhancedKernel adoptedH248Floor x := rfl
    _ = ∫ x in currentChenUpsilon6LogDomain 0,
          originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) x :=
      integral_congr_ae (adopted_enhancedKernel_ae_eq_halfopen (by norm_num))
    _ = _ := integral_productDomain_zero_eq_split
      (originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients))
      (integrableOn_currentChenUpsilon6OrdinaryKernel.add
        (integrableOn_originalFloorEnhancement adoptedKnots adoptedCoefficients))

/-- In Chen-quarter units there is exactly one factor 4, and the h248
contribution has denominator R*u*t rather than a*u*t. -/
theorem adopted_quarter_integrand (x : Point) :
    (1 / 4 : ℝ) * adoptedKernel x =
      (Real.log (currentChenUpsilon6OrdinaryProfile x - 1) +
        adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x)) /
          (originalResidual x * x 0 * x 1) := by
  rw [adoptedKernel_eq_original_log]
  ring

end

end ImbalancedChen.P5U6OriginalSlicedIntegralSourceOnly
