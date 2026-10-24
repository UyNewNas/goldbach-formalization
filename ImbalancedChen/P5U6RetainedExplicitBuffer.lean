import ImbalancedChen.P5U6RetainedAdoptedIntegral
import ImbalancedChen.P5U6RunboQuantitativeBuffer

/-!
SOURCE_ONLY / UNCOMPILED. Explicit original adopted U6 buffer budget.
Literal adopted cells satisfy 0<=h<=1 by source proofs on the serialized
integers. The scalar closed-cell floor is bounded by one INCLUDING knots:
uniqueness of cell/knot atoms prevents a sum-of-200 overestimate.

The correct original enhancement 4h/(Ruv) is at most2000 using R>=2a;
the ordinary kernel is at most4000. Hence actual kernel norm<=6000, and
the already proved21/250 strip rate gives retained loss<=504*eta for every
fixed measurable literal logmask. No numeric integration/data replay ran.
-/

namespace ImbalancedChen.P5U6RetainedExplicitBufferSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators
open Classical
open Part5OriginalUpsilon5CausalDictionary
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open P5U6AdoptedH248BindingSourceOnly
open P5U6RetainedAdoptedIntegralSourceOnly

abbrev Point := Fin 2 → ℝ

theorem adoptedNumerators_le_Q (i : Fin 200) :
    adoptedH248Numerators i ≤ (2 ^ 80 : ℤ) := by
  fin_cases i <;> norm_num [adoptedH248Numerators]

theorem adoptedValue_le_one (i : Fin 200) :
    floorValue adoptedH248Numerators i ≤ 1 := by
  unfold floorValue
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 80)).mpr
  rw [one_mul]
  exact_mod_cast adoptedNumerators_le_Q i

theorem adoptedKnotValue_le_one (j : Fin 201) :
    floorKnotValue adoptedH248Numerators j ≤ 1 := by
  unfold floorKnotValue
  split_ifs
  · exact adoptedValue_le_one _
  · exact adoptedValue_le_one _
  · exact (min_le_left _ _).trans (adoptedValue_le_one _)

theorem adoptedAtomValue_le_one (b : FloorAtom) :
    floorAtomValue adoptedH248Numerators b ≤ 1 := by
  cases b with
  | inl i => exact adoptedValue_le_one i
  | inr j => exact adoptedKnotValue_le_one j

private theorem grid_mono {m n : ℕ} (h : m ≤ n) : floorGrid m ≤ floorGrid n := by
  unfold floorGrid
  exact add_le_add_left (div_le_div_of_nonneg_right (by exact_mod_cast h) (by norm_num)) _

private theorem grid_injective : Function.Injective floorGrid := by
  intro m n h
  have hc : (m : ℝ) = (n : ℝ) := by unfold floorGrid at h; linarith
  exact_mod_cast hc

/-- Every scalar point belongs to at most one open-cell/singleton atom.
This preserves exactly the adjacent-minimum lookup convention at knots. -/
theorem floorAtom_unique {s : ℝ} {b c : FloorAtom}
    (hb : s ∈ floorAtomSet b) (hc : s ∈ floorAtomSet c) : b = c := by
  cases b with
  | inl i =>
    cases c with
    | inl j =>
      have hij : i.val = j.val := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hg := grid_mono (show i.val + 1 ≤ j.val by omega)
          linarith [hb.2.2, hc.2.1]
        · have hg := grid_mono (show j.val + 1 ≤ i.val by omega)
          linarith [hc.2.2, hb.2.1]
      exact congrArg Sum.inl (Fin.ext hij)
    | inr j =>
      have heq : s = floorGrid j.val := hc.2
      have hl := hb.2.1
      have hh := hb.2.2
      rw [heq] at hl hh
      by_cases hj : j.val ≤ i.val
      · have hg := grid_mono hj
        exact False.elim (by linarith)
      · have hg := grid_mono (show i.val + 1 ≤ j.val by omega)
        exact False.elim (by linarith)
  | inr i =>
    cases c with
    | inl j =>
      have heq : s = floorGrid i.val := hb.2
      have hl := hc.2.1
      have hh := hc.2.2
      rw [heq] at hl hh
      by_cases hi : i.val ≤ j.val
      · have hg := grid_mono hi
        exact False.elim (by linarith)
      · have hg := grid_mono (show j.val + 1 ≤ i.val by omega)
        exact False.elim (by linarith)
    | inr j =>
      have hgrid : floorGrid i.val = floorGrid j.val := hb.2.symm.trans hc.2
      exact congrArg Sum.inr (Fin.ext (grid_injective hgrid))

/-- Actual adopted scalar upper bound, including every endpoint and knot. -/
theorem adoptedFloor_le_one (s : ℝ) : adoptedH248Floor s ≤ 1 := by
  by_cases hex : ∃ b : FloorAtom, s ∈ floorAtomSet b
  · obtain ⟨b, hb⟩ := hex
    have heq : adoptedH248Floor s = floorAtomValue adoptedH248Numerators b := by
      unfold adoptedH248Floor floorStep
      calc
        _ = (floorAtomSet b).indicator (fun _ => floorAtomValue adoptedH248Numerators b) s :=
          Finset.sum_eq_single b
            (fun c _ hcb => indicator_of_notMem
              (fun hc => hcb (floorAtom_unique hc hb)) _)
            (by simp)
        _ = _ := indicator_of_mem hb _
    rw [heq]
    exact adoptedAtomValue_le_one b
  · have hz : adoptedH248Floor s = 0 := by
      unfold adoptedH248Floor floorStep
      apply Finset.sum_eq_zero
      intro b _
      exact indicator_of_notMem (fun hb => hex ⟨b, hb⟩) _
    rw [hz]
    norm_num

theorem adoptedFloor_mem_unitInterval (s : ℝ) : adoptedH248Floor s ∈ Icc (0 : ℝ) 1 :=
  ⟨adoptedFloor_nonneg s, adoptedFloor_le_one s⟩

/-- Exact R>=2a and positive prime-coordinate margins give the original
enhancement bound. This is a rational estimate, not a numerical sample. -/
theorem originalEnhancement_le_2000 {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain 0) :
    originalEnhancement adoptedH248Floor x ≤ (2000 : ℝ) := by
  have hRlower := originalResidual_ge_two_a (by norm_num) hx
  have hRp : 0 < originalResidual x := lt_of_lt_of_le (by norm_num) hRlower
  have hinv : 1 / originalResidual x ≤ 1 / (2 * (417 / 5000 : ℝ)) :=
    one_div_le_one_div_of_le (by norm_num) hRlower
  have hnum : 4 * adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x) ≤ (4 : ℝ) := by
    nlinarith only [adoptedFloor_le_one (currentChenUpsilon6OrdinaryProfile x)]
  obtain ⟨hu, hv⟩ := currentChenUpsilon6LogRectangle_coordinates_pos hx.1
  have hrec0 : 0 ≤ 1 / (x 0 * x 1) := by positivity
  have hrec : 1 / (x 0 * x 1) ≤ (625000 / 7923 : ℝ) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      P5U6RunboQuantitativeBufferSourceOnly.reciprocal_norm_bound hx.1)
  have heq : originalEnhancement adoptedH248Floor x =
      (4 * adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x)) *
        (1 / originalResidual x) * (1 / (x 0 * x 1)) := by
    unfold originalEnhancement
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  calc
    _ ≤ (4 * (1 / (2 * (417 / 5000 : ℝ)))) * (625000 / 7923 : ℝ) :=
      mul_le_mul (mul_le_mul hnum hinv (one_div_nonneg.mpr hRp.le) (by norm_num))
        hrec hrec0 (by norm_num)
    _ ≤ _ := by norm_num

theorem adoptedKernel_norm_le_6000 {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain 0) : ‖adoptedKernel x‖ ≤ (6000 : ℝ) := by
  have hord : currentChenUpsilon6OrdinaryKernel x ≤ (4000 : ℝ) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
      P5U6RunboQuantitativeBufferSourceOnly.ordinary_norm_bound hx)
  have hcorr := originalEnhancement_le_2000 hx
  rw [Real.norm_eq_abs, abs_of_nonneg (adoptedKernel_nonneg (by norm_num) hx)]
  change currentChenUpsilon6OrdinaryKernel x + originalEnhancement adoptedH248Floor x ≤ 6000
  linarith

private theorem productDomain_subset_zero {eta : ℝ} (heta : 0 ≤ eta) :
    currentChenUpsilon6LogDomain eta ⊆ currentChenUpsilon6LogDomain 0 := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hgate : x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta := hx.2
  change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0
  linarith

/-- The original same-mask retained estimator loses at most504*eta.
Only the proven strip-area theorem is used; no mask boundary regularity or
assumed tail convergence is required beyond measurability of the fixed mask. -/
theorem retained_abs_buffer_loss_le (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {eta : ℝ} (heta : 0 ≤ eta) :
    |retainedEstimatorIntegral E 0 - retainedEstimatorIntegral E eta| ≤ 504 * eta := by
  let g := ({x : Point | ¬ E x}).indicator ((currentChenUpsilon6LogDomain 0).indicator adoptedKernel)
  have hg : Integrable g :=
    ((integrableOn_adoptedEnhancedKernel (by norm_num)).integrable_indicator
      (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0)).indicator hE.compl
  have heq (eta : ℝ) (hη : 0 ≤ eta) :
      (∫ x in currentChenUpsilon6LogDomain eta, g x) = retainedEstimatorIntegral E eta := by
    dsimp only [g]
    rw [setIntegral_indicator hE.compl]
    apply setIntegral_congr_fun
      ((P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta).inter hE.compl)
    intro x hx
    exact indicator_of_mem (productDomain_subset_zero hη hx.1) adoptedKernel
  have hb : ∀ᵐ x : Point ∂volume.restrict (currentChenUpsilon6LogDomain 0), ‖g x‖ ≤ (6000 : ℝ) := by
    filter_upwards [ae_restrict_mem
      (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain 0)] with x hx
    have hi := norm_indicator_le_norm_self (s := {x : Point | ¬ E x})
      ((currentChenUpsilon6LogDomain 0).indicator adoptedKernel) x
    rw [indicator_of_mem hx] at hi
    exact hi.trans (adoptedKernel_norm_le_6000 hx)
  have h := P5U6RunboQuantitativeBufferSourceOnly.abs_buffer_loss_le g hg.integrableOn
    heta (by norm_num : (0 : ℝ) ≤ 6000) hb
  rw [heq 0 (by norm_num), heq eta heta] at h
  norm_num at h ⊢
  exact h

theorem retained_loss_le_tolerance (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {eta epsilon : ℝ}
    (heta : 0 ≤ eta) (hbudget : eta ≤ epsilon / 504) :
    |retainedEstimatorIntegral E 0 - retainedEstimatorIntegral E eta| ≤ epsilon := by
  have h := retained_abs_buffer_loss_le E hE heta
  have hb : 504 * eta ≤ epsilon := by linarith
  exact h.trans hb

/-- Directly executable rational buffer choice for a future certificate:
eta=epsilon/504 works for every fixed measurable original logmask. -/
theorem explicit_retained_buffer (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < epsilon / 504 ∧
      |retainedEstimatorIntegral E 0 - retainedEstimatorIntegral E (epsilon / 504)| ≤ epsilon := by
  have heta : 0 < epsilon / 504 := div_pos hepsilon (by norm_num)
  exact ⟨heta, retained_loss_le_tolerance E hE heta.le le_rfl⟩

/-- The adopted retained L6 consumer can use the explicit buffered
full-minus-selected estimator directly, with no existential small-buffer input. -/
theorem retained_lower_from_explicit_buffer (E : Point → Prop)
    (hE : MeasurableSet {x : Point | E x}) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    retainedEstimatorIntegral E 0 - epsilon ≤
      fullIntegral (epsilon / 504) - selectedEstimatorIntegral E (epsilon / 504) := by
  have heta : 0 ≤ epsilon / 504 := le_of_lt (div_pos hepsilon (by norm_num))
  have habs := (explicit_retained_buffer E hE hepsilon).2
  have hle := (le_abs_self _).trans habs
  rw [full_sub_selected_eq_retained E hE heta]
  linarith

end

end ImbalancedChen.P5U6RetainedExplicitBufferSourceOnly
