import ImbalancedChen.P5OriginalTaylorWeightedAxisCalculus

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original full M[i] formula of certify_fifth_prefix_taylor_pilot.py
lines 66--91, including the signed derivative cancellation minimum.
The only geometric inputs are primitive argument ranges/gap, the actual
raw box and positivity. No first/second derivative estimate, Hessian
licence, stored-floor licence or integral bound is assumed.
-/
namespace ImbalancedChen.P5OriginalTaylorWeightedHessian
noncomputable section
open Set
open scoped Classical
open P1OriginalPrefixRowDecodeSoundness P1OriginalFifthCorrelatedRawBoxGates
open P5OldFifthPointwiseQ P5OldFifthFirstFConcavity
open P5OriginalTaylorProfileDerivatives P5OriginalTaylorActualSignedKernel
open P5OriginalTaylorAffineBranchBinding P5OriginalTaylorAffineRatioDerivatives
open P5OriginalTaylorWeightDerivatives P5OriginalTaylorWeightedAxisCalculus

def pilotSecondBound (a Dn Do En Eo : ℝ) : ℝ :=
  pilotM2 a * (Dn ^ 2 + Do ^ 2) + pilotM1 a * (En + Eo)

/-- This is the producer's M[i], using the original D/E/T and weight
formulas rather than an independently enlarged Hessian enclosure. -/
def pilotHessian (raw : FifthWireRow) (new old : Affine5)
    (a snMax soMax delta : ℝ) (i : Fin 5) : ℝ :=
  pilotWMax raw *
    (pilotR raw i * (pilotM1 a * delta) +
      2 * pilotK raw i * pilotFirstBound a delta
        (pilotD raw new snMax i) (pilotD raw old soMax i) (pilotT raw new old delta i) +
      pilotSecondBound a (pilotD raw new snMax i) (pilotD raw old soMax i)
        (pilotE raw new snMax i) (pilotE raw old soMax i))

/-- The second chain rule bound for the actual first-interval profile. -/
theorem original_second_chain_bound {a sn so dn do_ en eo Dn Do En Eo : ℝ}
    (ha2 : 2 ≤ a) (hao : a ≤ so) (hon : so ≤ sn) (hn4 : sn ≤ 4)
    (hdn : |dn| ≤ Dn) (hdo : |do_| ≤ Do) (hen : |en| ≤ En) (heo : |eo| ≤ Eo) :
    |(firstCurvature sn * dn ^ 2 + firstSlope sn * en) -
      (firstCurvature so * do_ ^ 2 + firstSlope so * eo)| ≤
      pilotSecondBound a Dn Do En Eo := by
  have hm1 := pilotM1_nonneg a ha2 (hao.trans (hon.trans hn4))
  have hm2 := pilotM2_nonneg a ha2
  have hsn := firstSlope_abs_le_pilotM1 ha2 (hao.trans hon) hn4
  have hso := firstSlope_abs_le_pilotM1 ha2 hao (hon.trans hn4)
  have hcn := firstCurvature_abs_le_pilotM2 ha2 (hao.trans hon) hn4
  have hco := firstCurvature_abs_le_pilotM2 ha2 hao (hon.trans hn4)
  have hdn2 : dn ^ 2 ≤ Dn ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg dn) ((abs_nonneg dn).trans hdn)).2 hdn
    simpa only [sq_abs] using h
  have hdo2 : do_ ^ 2 ≤ Do ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg do_) ((abs_nonneg do_).trans hdo)).2 hdo
    simpa only [sq_abs] using h
  have hn : |firstCurvature sn * dn ^ 2 + firstSlope sn * en| ≤
      pilotM2 a * Dn ^ 2 + pilotM1 a * En := by
    calc
      _ ≤ |firstCurvature sn * dn ^ 2| + |firstSlope sn * en| := abs_add _ _
      _ = |firstCurvature sn| * dn ^ 2 + |firstSlope sn| * |en| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg dn)]
      _ ≤ _ := add_le_add (mul_le_mul hcn hdn2 (sq_nonneg dn) hm2)
        (mul_le_mul hsn hen (abs_nonneg en) hm1)
  have ho : |firstCurvature so * do_ ^ 2 + firstSlope so * eo| ≤
      pilotM2 a * Do ^ 2 + pilotM1 a * Eo := by
    calc
      _ ≤ |firstCurvature so * do_ ^ 2| + |firstSlope so * eo| := abs_add _ _
      _ = |firstCurvature so| * do_ ^ 2 + |firstSlope so| * |eo| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg do_)]
      _ ≤ _ := add_le_add (mul_le_mul hco hdo2 (sq_nonneg do_) hm2)
        (mul_le_mul hso heo (abs_nonneg eo) hm1)
  calc
    _ ≤ |firstCurvature sn * dn ^ 2 + firstSlope sn * en| +
        |firstCurvature so * do_ ^ 2 + firstSlope so * eo| := abs_sub _ _
    _ ≤ (pilotM2 a * Dn ^ 2 + pilotM1 a * En) +
        (pilotM2 a * Do ^ 2 + pilotM1 a * Eo) := add_le_add hn ho
    _ = _ := by unfold pilotSecondBound; ring

/-- No bound for G'' occurs among the hypotheses: all three terms of
the weighted product rule are paid by the original explicit factors. -/
theorem original_axisKernelCurvature_le_pilotHessian
    (raw : FifthWireRow) (new old : Affine5) (a snMax soMax delta : ℝ)
    (hl : ∀ k, 0 < (raw.lower k : ℝ)) (t : Fin 5 → ℝ)
    (ht : t ∈ rawClosedBox raw) (i : Fin 5)
    (ha2 : 2 ≤ a) (hao : a ≤ affineArgument old t)
    (hon : affineArgument old t ≤ affineArgument new t)
    (hn4 : affineArgument new t ≤ 4)
    (hnMax : affineArgument new t ≤ snMax) (hoMax : affineArgument old t ≤ soMax)
    (hdelta : affineArgument new t - affineArgument old t ≤ delta)
    (hnCoef : residualCoefficient new 4 ≤ 0) (hoCoef : residualCoefficient old 4 ≤ 0) :
    |axisKernelCurvature new old t i (t i)| ≤
      pilotHessian raw new old a snMax soMax delta i := by
  have hp : ∀ k, 0 < t k := fun k => (hl k).trans_le (ht k).1
  have ho2 : 2 ≤ affineArgument old t := ha2.trans hao
  have hn2 : 2 ≤ affineArgument new t := ho2.trans hon
  have hDn := original_axisSlope_le_pilotD raw new snMax t i (hl 4) ht hn2 hnMax hnCoef
  have hDo := original_axisSlope_le_pilotD raw old soMax t i (hl 4) ht ho2 hoMax hoCoef
  have hEn := original_axisCurvature_le_pilotE raw new snMax t i (hl 4) ht hn2 hnMax hnCoef
  have hEo := original_axisCurvature_le_pilotE raw old soMax t i (hl 4) ht ho2 hoMax hoCoef
  have hT := original_axisSlope_difference_le_pilotT raw new old delta t i (hl 4) ht hon hdelta
  have hd : |axisDifference new old t i (t i)| ≤ pilotM1 a * delta := by
    simpa only [axisDifference, axisArgument_at_base] using
      firstF_difference_le_pilotM1 ha2 hao hon hn4 hdelta
  have hd' : |axisDifferenceSlope new old t i (t i)| ≤
      pilotFirstBound a delta (pilotD raw new snMax i) (pilotD raw old soMax i)
        (pilotT raw new old delta i) := by
    simpa only [axisDifferenceSlope, axisArgument_at_base] using
      original_derivative_cancellation ha2 hao hon hn4 hdelta hDn hDo hT
  have hd'' : |axisDifferenceCurvature new old t i (t i)| ≤
      pilotSecondBound a (pilotD raw new snMax i) (pilotD raw old soMax i)
        (pilotE raw new snMax i) (pilotE raw old soMax i) := by
    simpa only [axisDifferenceCurvature, axisArgument_at_base] using
      original_second_chain_bound ha2 hao hon hn4 hDn hDo hEn hEo
  have hw : |axisWeight t i (t i)| ≤ pilotWMax raw := by
    rw [axisWeight_at_base, abs_of_nonneg (originalTaylorWeight_nonneg t hp)]
    exact original_weight_le_pilotWMax raw hl t ht
  have hw' := original_weightSlope_le_pilotK raw hl t ht i
  have hw'' := original_weightCurvature_le_pilotR raw hl t ht i
  have hterm0 := mul_le_mul hw'' hd (abs_nonneg _)
    ((abs_nonneg _).trans hw'')
  have hterm1 := mul_le_mul hw' hd' (abs_nonneg _)
    ((abs_nonneg _).trans hw')
  have hterm2 := mul_le_mul hw hd'' (abs_nonneg _)
    ((abs_nonneg _).trans hw)
  have hcross : |2 * axisWeightSlope t i (t i) * axisDifferenceSlope new old t i (t i)| ≤
      2 * (pilotWMax raw * pilotK raw i) *
        pilotFirstBound a delta (pilotD raw new snMax i) (pilotD raw old soMax i)
          (pilotT raw new old delta i) := by
    calc
      _ = 2 * (|axisWeightSlope t i (t i)| * |axisDifferenceSlope new old t i (t i)|) := by
        rw [abs_mul, abs_mul]
        norm_num <;> ring
      _ ≤ 2 * ((pilotWMax raw * pilotK raw i) *
          pilotFirstBound a delta (pilotD raw new snMax i) (pilotD raw old soMax i)
            (pilotT raw new old delta i)) :=
        mul_le_mul_of_nonneg_left hterm1 (by norm_num)
      _ = _ := by ring
  unfold axisKernelCurvature
  calc
    _ ≤ |axisWeightCurvature t i (t i) * axisDifference new old t i (t i) +
          2 * axisWeightSlope t i (t i) * axisDifferenceSlope new old t i (t i)| +
        |axisWeight t i (t i) * axisDifferenceCurvature new old t i (t i)| := abs_add _ _
    _ ≤ (|axisWeightCurvature t i (t i) * axisDifference new old t i (t i)| +
          |2 * axisWeightSlope t i (t i) * axisDifferenceSlope new old t i (t i)|) +
        |axisWeight t i (t i) * axisDifferenceCurvature new old t i (t i)| :=
      add_le_add_right (abs_add _ _) _
    _ ≤ ((pilotWMax raw * pilotR raw i) * (pilotM1 a * delta) +
          2 * (pilotWMax raw * pilotK raw i) *
            pilotFirstBound a delta (pilotD raw new snMax i) (pilotD raw old soMax i)
              (pilotT raw new old delta i)) +
        pilotWMax raw * pilotSecondBound a (pilotD raw new snMax i) (pilotD raw old soMax i)
          (pilotE raw new snMax i) (pilotE raw old soMax i) := by
      exact add_le_add
        (add_le_add (by simpa only [abs_mul] using hterm0) hcross)
        (by simpa only [abs_mul] using hterm2)
    _ = _ := by unfold pilotHessian; ring

/-- Actual original new and selected old planes: coefficient signs are
discharged from the original tent/W formulas, not supplied by the caller. -/
theorem original_selected_axisKernelCurvature_le_pilotHessian
    (raw : FifthWireRow) (newSide : Bool) (oldSides : OldSides) (selected : Option OldMask)
    (a snMax soMax delta : ℝ) (hl : ∀ k, 0 < (raw.lower k : ℝ))
    (t : Fin 5 → ℝ) (ht : t ∈ rawClosedBox raw) (i : Fin 5)
    (ha2 : 2 ≤ a) (hao : a ≤ affineArgument (selectedOldPlane oldSides selected) t)
    (hon : affineArgument (selectedOldPlane oldSides selected) t ≤
      affineArgument (newPlane raw newSide) t)
    (hn4 : affineArgument (newPlane raw newSide) t ≤ 4)
    (hnMax : affineArgument (newPlane raw newSide) t ≤ snMax)
    (hoMax : affineArgument (selectedOldPlane oldSides selected) t ≤ soMax)
    (hdelta : affineArgument (newPlane raw newSide) t -
      affineArgument (selectedOldPlane oldSides selected) t ≤ delta) :
    |axisKernelCurvature (newPlane raw newSide) (selectedOldPlane oldSides selected) t i (t i)| ≤
      pilotHessian raw (newPlane raw newSide) (selectedOldPlane oldSides selected)
        a snMax soMax delta i :=
  original_axisKernelCurvature_le_pilotHessian raw _ _ a snMax soMax delta hl t ht i
    ha2 hao hon hn4 hnMax hoMax hdelta
    (new_residualCoefficient_nonpos raw newSide 4)
    (selected_old_residualCoefficient_nonpos oldSides selected 4)

/-- The original signed raw kernel has this affine C2 extension on its
entire original closed box, including endpoint seams. The displayed M
is the actual bound of that extension's genuine diagonal derivative. -/
theorem original_signed_weighted_hessian
    (raw : FifthWireRow) (newSide : Bool) (oldSides : OldSides) (selected : Option OldMask)
    (hbranch : BranchFacts raw newSide oldSides selected)
    (a snMax soMax delta : ℝ) (hl : ∀ k, 0 < (raw.lower k : ℝ)) (ha2 : 2 ≤ a)
    (hrange : ∀ t ∈ rawClosedBox raw,
      a ≤ affineArgument (selectedOldPlane oldSides selected) t ∧
      affineArgument (selectedOldPlane oldSides selected) t ≤ affineArgument (newPlane raw newSide) t ∧
      affineArgument (newPlane raw newSide) t ≤ 4 ∧
      affineArgument (newPlane raw newSide) t ≤ snMax ∧
      affineArgument (selectedOldPlane oldSides selected) t ≤ soMax ∧
      affineArgument (newPlane raw newSide) t -
        affineArgument (selectedOldPlane oldSides selected) t ≤ delta) :
    (∀ t ∈ rawClosedBox raw, originalTaylorSignedKernel raw t =
      affineTaylorSignedKernel (newPlane raw newSide) (selectedOldPlane oldSides selected) t) ∧
    (∀ t ∈ rawClosedBox raw, ∀ i : Fin 5,
      |axisKernelCurvature (newPlane raw newSide) (selectedOldPlane oldSides selected) t i (t i)| ≤
        pilotHessian raw (newPlane raw newSide) (selectedOldPlane oldSides selected)
          a snMax soMax delta i) := by
  constructor
  · exact fun t ht => original_signed_kernel_eq_affine raw newSide oldSides selected hbranch t ht
  · intro t ht i
    rcases hrange t ht with ⟨hao, hon, hn4, hnMax, hoMax, hdelta⟩
    exact original_selected_axisKernelCurvature_le_pilotHessian raw newSide oldSides selected
      a snMax soMax delta hl t ht i ha2 hao hon hn4 hnMax hoMax hdelta

end
end ImbalancedChen.P5OriginalTaylorWeightedHessian
