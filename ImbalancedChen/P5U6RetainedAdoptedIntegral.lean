import ImbalancedChen.P5U6AdoptedH248Binding

/-!
SOURCE_ONLY / UNCOMPILED. Original normalized adopted U6 estimator integrals
on one fixed measurable literal logmask. The original correction is 4h/(Ruv),
R=1/2-u-v. Full minus selected ESTIMATOR integral equals retained integral.
Selected estimator integrals are never identified with actual selected counts.

The actual serialized 200-entry array supplies nonnegativity through ordinary
source proofs, with no recurrence conclusion. Exact masked floor-band sums,
an explicit integrable finite-table dominator and right buffer limits are
proved. No P2 mask, numerical L6 endpoint or arithmetic coordinate API is added.
-/

namespace ImbalancedChen.P5U6RetainedAdoptedIntegralSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open Part5OriginalUpsilon5CausalDictionary
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open P5U6AdoptedH248BindingSourceOnly

abbrev Point := Fin 2 → ℝ

def adoptedKernel : Point → ℝ := originalEnhancedKernel adoptedH248Floor

def fullIntegral (eta : ℝ) : ℝ :=
  ∫ x in currentChenUpsilon6LogDomain eta, adoptedKernel x

def selectedEstimatorIntegral (E : Point → Prop) (eta : ℝ) : ℝ :=
  ∫ x in currentChenUpsilon6LogDomain eta ∩ {x | E x}, adoptedKernel x

def retainedEstimatorIntegral (E : Point → Prop) (eta : ℝ) : ℝ :=
  ∫ x in currentChenUpsilon6LogDomain eta ∩ {x | ¬ E x}, adoptedKernel x

/-- Literal original corrected enhanced integrand, with R in the complete
denominator and the adopted h value in the same normalized numerator. -/
theorem adoptedKernel_eq_original_log (x : Point) :
    adoptedKernel x =
      4 * (Real.log (currentChenUpsilon6OrdinaryProfile x - 1) +
        adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x)) /
          (originalResidual x * x 0 * x 1) := by
  have hR : currentChenUpsilon6OrdinaryProfile x * (417 / 5000 : ℝ) = originalResidual x := by
    rw [originalResidual_eq_a_mul_profile]
    ring
  unfold adoptedKernel originalEnhancedKernel currentChenUpsilon6OrdinaryKernel originalEnhancement
  rw [hR]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Nonnegativity of literal adopted integers, not a delay recurrence claim.
This is source only; neither this tactic nor any numerical replay was run. -/
theorem adoptedNumerators_nonneg (i : Fin 200) : 0 ≤ adoptedH248Numerators i := by
  fin_cases i <;> norm_num [adoptedH248Numerators]

theorem adoptedValue_nonneg (i : Fin 200) :
    0 ≤ floorValue adoptedH248Numerators i := by
  unfold floorValue
  exact div_nonneg (by exact_mod_cast adoptedNumerators_nonneg i) (by positivity)

theorem adoptedKnotValue_nonneg (j : Fin 201) :
    0 ≤ floorKnotValue adoptedH248Numerators j := by
  unfold floorKnotValue
  split_ifs
  · exact adoptedValue_nonneg _
  · exact adoptedValue_nonneg _
  · exact le_min (adoptedValue_nonneg _) (adoptedValue_nonneg _)

theorem adoptedAtomValue_nonneg (b : FloorAtom) :
    0 ≤ floorAtomValue adoptedH248Numerators b := by
  cases b with
  | inl i => exact adoptedValue_nonneg i
  | inr j => exact adoptedKnotValue_nonneg j

theorem adoptedFloor_nonneg (s : ℝ) : 0 ≤ adoptedH248Floor s := by
  unfold adoptedH248Floor floorStep
  apply Finset.sum_nonneg
  intro b _
  by_cases hb : s ∈ floorAtomSet b
  · rw [indicator_of_mem hb]
    exact adoptedAtomValue_nonneg b
  · rw [indicator_of_notMem hb]

theorem adoptedKernel_nonneg {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) : 0 ≤ adoptedKernel x := by
  have hR : 0 < originalResidual x :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 * (417 / 5000 : ℝ))
      (originalResidual_ge_two_a heta hx)
  obtain ⟨hu, hv⟩ := currentChenUpsilon6LogRectangle_coordinates_pos hx.1
  unfold adoptedKernel originalEnhancedKernel
  apply add_nonneg (currentChenUpsilon6OrdinaryKernel_nonneg heta hx)
  unfold originalEnhancement
  exact div_nonneg (mul_nonneg (by norm_num) (adoptedFloor_nonneg _))
    (mul_nonneg (mul_nonneg hR.le hu.le) hv.le)

/-- Concrete finite-table integrable dominator. Its table constant is the
actual finite sum of norms of the 401 cell/knot values, not a supplied bound. -/
def adoptedDominator (x : Point) : ℝ :=
  ‖currentChenUpsilon6OrdinaryKernel x‖ +
    (4 * floorBound adoptedH248Numerators) * ‖originalWeight x‖

theorem integrableOn_adoptedDominator :
    IntegrableOn adoptedDominator currentChenUpsilon6LogRectangle :=
  integrableOn_currentChenUpsilon6OrdinaryKernel.norm.add
    (integrableOn_originalWeight.norm.const_mul _)

theorem adoptedKernel_norm_le_dominator (x : Point) :
    ‖adoptedKernel x‖ ≤ adoptedDominator x := by
  have heq : originalEnhancement adoptedH248Floor x =
      4 * adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * originalWeight x := by
    unfold originalEnhancement originalWeight
    ring
  have hh : ‖originalEnhancement adoptedH248Floor x‖ ≤
      (4 * floorBound adoptedH248Numerators) * ‖originalWeight x‖ := by
    rw [heq]
    calc
      ‖4 * adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) * originalWeight x‖ =
          (4 * ‖adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x)‖) * ‖originalWeight x‖ := by
        simp only [norm_mul, norm_ofNat]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_adoptedH248Floor_le _) (by norm_num)) (norm_nonneg _)
  change ‖currentChenUpsilon6OrdinaryKernel x + originalEnhancement adoptedH248Floor x‖ ≤
    ‖currentChenUpsilon6OrdinaryKernel x‖ +
      (4 * floorBound adoptedH248Numerators) * ‖originalWeight x‖
  exact (norm_add_le _ _).trans (add_le_add_left hh _)

/-- Measurable same-mask subtraction of estimator integrals is exact. -/
theorem full_sub_selected_eq_retained (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {eta : ℝ} (heta : 0 ≤ eta) :
    fullIntegral eta - selectedEstimatorIntegral E eta = retainedEstimatorIntegral E eta := by
  have hdiff : currentChenUpsilon6LogDomain eta \ {x : Point | E x} =
      currentChenUpsilon6LogDomain eta ∩ {x : Point | ¬ E x} := by
    ext x
    rfl
  have h := integral_inter_add_sdiff hE (integrableOn_adoptedEnhancedKernel heta)
  rw [hdiff] at h
  change selectedEstimatorIntegral E eta + retainedEstimatorIntegral E eta = fullIntegral eta at h
  linarith

theorem selectedEstimatorIntegral_nonneg (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ selectedEstimatorIntegral E eta := by
  apply setIntegral_nonneg
    ((P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter hE)
  intro x hx
  exact adoptedKernel_nonneg heta hx.1

theorem retainedEstimatorIntegral_nonneg (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {eta : ℝ} (heta : 0 ≤ eta) :
    0 ≤ retainedEstimatorIntegral E eta := by
  apply setIntegral_nonneg
    ((P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter hE.compl)
  intro x hx
  exact adoptedKernel_nonneg heta hx.1

/-- Any measurable mask restriction uses the actual original weighted bands.
The band masses contain the mask exactly, rather than a surrogate bound. -/
theorem integral_adopted_on_subset {eta : ℝ} (heta : 0 ≤ eta)
    (S : Set Point) (hS : S ⊆ currentChenUpsilon6LogDomain eta) :
    (∫ x in S, adoptedKernel x) =
      (∫ x in S, currentChenUpsilon6OrdinaryKernel x) +
        ∑ i : Fin 200, (4 * adoptedCoefficients i) *
          ∫ x in S ∩ profileBand (adoptedKnots i.castSucc) (adoptedKnots i.succ), originalWeight x := by
  have hrect : S ⊆ currentChenUpsilon6LogRectangle :=
    fun x hx => (hS hx).1
  have heq : adoptedKernel =ᵐ[volume.restrict S]
      originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) :=
    ae_restrict_of_ae_restrict_of_subset hS (adopted_enhancedKernel_ae_eq_halfopen heta)
  rw [integral_congr_ae heq]
  unfold originalEnhancedKernel
  rw [integral_add (integrableOn_currentChenUpsilon6OrdinaryKernel.mono_set hrect)
    ((integrableOn_originalFloorEnhancement adoptedKnots adoptedCoefficients).mono_set hrect)]
  congr 1
  simp_rw [originalEnhancement_floor_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    ((integrableOn_originalBandWeight (adoptedKnots i.castSucc) (adoptedKnots i.succ)).const_mul
      (4 * adoptedCoefficients i)).mono_set hrect)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, setIntegral_indicator (measurableSet_profileBand _ _)]

theorem selectedEstimatorIntegral_eq_band_sum (E : Point → Prop)
    {eta : ℝ} (heta : 0 ≤ eta) :
    selectedEstimatorIntegral E eta =
      (∫ x in currentChenUpsilon6LogDomain eta ∩ {x | E x}, currentChenUpsilon6OrdinaryKernel x) +
        ∑ i : Fin 200, (4 * adoptedCoefficients i) *
          ∫ x in (currentChenUpsilon6LogDomain eta ∩ {x | E x}) ∩
            profileBand (adoptedKnots i.castSucc) (adoptedKnots i.succ), originalWeight x :=
  integral_adopted_on_subset heta _ inter_subset_left

theorem retainedEstimatorIntegral_eq_band_sum (E : Point → Prop)
    {eta : ℝ} (heta : 0 ≤ eta) :
    retainedEstimatorIntegral E eta =
      (∫ x in currentChenUpsilon6LogDomain eta ∩ {x | ¬ E x}, currentChenUpsilon6OrdinaryKernel x) +
        ∑ i : Fin 200, (4 * adoptedCoefficients i) *
          ∫ x in (currentChenUpsilon6LogDomain eta ∩ {x | ¬ E x}) ∩
            profileBand (adoptedKnots i.castSucc) (adoptedKnots i.succ), originalWeight x :=
  integral_adopted_on_subset heta _ inter_subset_left

private theorem productDomain_subset_zero {eta : ℝ} (heta : 0 ≤ eta) :
    currentChenUpsilon6LogDomain eta ⊆ currentChenUpsilon6LogDomain 0 := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hgate : x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta := hx.2
  change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0
  linarith

/-- Fixed-mask buffer limit from an integrable D0 kernel. Extension by zero
lets the already proved genuine DCT apply without any assumed mask-tail bound. -/
theorem tendsto_masked_integral_right (f : Point → ℝ)
    (hf : IntegrableOn f (currentChenUpsilon6LogDomain 0))
    (E : Point → Prop) (hE : MeasurableSet {x : Point | E x}) :
    Tendsto (fun eta : ℝ => ∫ x in currentChenUpsilon6LogDomain eta ∩ {x | E x}, f x)
      (𝓝[>] 0) (𝓝 (∫ x in currentChenUpsilon6LogDomain 0 ∩ {x | E x}, f x)) := by
  let g := ({x : Point | E x}).indicator ((currentChenUpsilon6LogDomain 0).indicator f)
  have hg : Integrable g :=
    (hf.integrable_indicator (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0)).indicator hE
  have heq (eta : ℝ) (heta : 0 ≤ eta) :
      (∫ x in currentChenUpsilon6LogDomain eta, g x) =
        ∫ x in currentChenUpsilon6LogDomain eta ∩ {x | E x}, f x := by
    dsimp only [g]
    rw [setIntegral_indicator hE]
    apply setIntegral_congr_fun
      ((P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter hE)
    intro x hx
    exact indicator_of_mem (productDomain_subset_zero heta hx.1) f
  have h := (P5U6RunboBufferLimitSourceOnly.tendsto_integral_productDomain g hg.integrableOn).mono_left
    nhdsWithin_le_nhds
  rw [heq 0 (by norm_num)] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact heq eta heta.le

theorem tendsto_selectedEstimatorIntegral_right (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) :
    Tendsto (selectedEstimatorIntegral E) (𝓝[>] 0) (𝓝 (selectedEstimatorIntegral E 0)) :=
  tendsto_masked_integral_right adoptedKernel (integrableOn_adoptedEnhancedKernel (by norm_num)) E hE

theorem tendsto_retainedEstimatorIntegral_right (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) :
    Tendsto (retainedEstimatorIntegral E) (𝓝[>] 0) (𝓝 (retainedEstimatorIntegral E 0)) :=
  tendsto_masked_integral_right adoptedKernel (integrableOn_adoptedEnhancedKernel (by norm_num))
    (fun x => ¬ E x) hE.compl

/-- The same fixed-mask full-minus-selected expression converges exactly to
the retained original estimator integral. No selected arithmetic count occurs. -/
theorem tendsto_full_sub_selected_right (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) :
    Tendsto (fun eta => fullIntegral eta - selectedEstimatorIntegral E eta)
      (𝓝[>] 0) (𝓝 (retainedEstimatorIntegral E 0)) := by
  have hf : Tendsto fullIntegral (𝓝[>] 0) (𝓝 (fullIntegral 0)) :=
    tendsto_adoptedEnhancedKernel_integral_right
  have h := hf.sub (tendsto_selectedEstimatorIntegral_right E hE)
  rw [full_sub_selected_eq_retained E hE (eta := 0) (by norm_num)] at h
  exact h

/-- Concrete quantifier interface for the retained L6 arithmetic consumer:
first fix the mask and epsilon, then choose one positive buffer before N. -/
theorem exists_retained_positive_buffer (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧ retainedEstimatorIntegral E 0 - epsilon <
      fullIntegral eta - selectedEstimatorIntegral E eta := by
  have hlimit := tendsto_full_sub_selected_right E hE
  have hnear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0 < eta ∧
      retainedEstimatorIntegral E 0 - epsilon < fullIntegral eta - selectedEstimatorIntegral E eta := by
    filter_upwards [self_mem_nhdsWithin,
      hlimit.eventually (Ioi_mem_nhds
        (by linarith : retainedEstimatorIntegral E 0 - epsilon < retainedEstimatorIntegral E 0))]
      with eta heta hI
    exact ⟨heta, hI⟩
  exact hnear.exists

end

end ImbalancedChen.P5U6RetainedAdoptedIntegralSourceOnly
