import ImbalancedChen.P5U6RunboEnhancedFloorInterface
import ImbalancedChen.Part5OriginalUpsilon5FloorKernel

/-!
SOURCE_ONLY / UNCOMPILED. The adopted 200-entry h248 scalar floor, with
grid 1+j/50 and denominator 2^80, binds to the U6 half-open finite floor.
The exact scalar closed-cell convention is retained at knots. Equality with
the half-open floor is proved off the finite family of affine profile walls;
those walls are proved null, so all displayed integral equalities are exact.

The adjacent-minimum convention and literal adopted integer array come from
the sibling Part5OriginalUpsilon5FloorKernel / Part5AdoptedH248Data sources.
No data replay, table recurrence, lower correctness, or original-prime mean
is asserted. The original enhancement here has denominator R*u*v, where
R=1/2-u-v=a*s. The earlier a-denominator model is explicitly auxiliary.
Original physical lower-coefficient correctness and arithmetic mean remain
separate from the scalar adopted-table identification proved here.
-/

namespace ImbalancedChen.P5U6AdoptedH248BindingSourceOnly

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
open P5U6RunboEnhancedFloorInterfaceSourceOnly
open Part5OriginalUpsilon5CausalDictionary

abbrev Point := Fin 2 → ℝ

def adoptedKnots (j : Fin 201) : ℝ := floorGrid j.val

def adoptedCoefficients (i : Fin 200) : ℝ := floorValue adoptedH248Numerators i

def originalResidual (x : Point) : ℝ := (1 / 2 : ℝ) - x 0 - x 1

def originalWeight (x : Point) : ℝ := 1 / (originalResidual x * x 0 * x 1)

/-- Original h correction, with R=a*s, not with a alone. -/
def originalEnhancement (h : ℝ → ℝ) (x : Point) : ℝ :=
  4 * h (currentChenUpsilon6OrdinaryProfile x) /
    (originalResidual x * x 0 * x 1)

def originalEnhancedKernel (h : ℝ → ℝ) (x : Point) : ℝ :=
  currentChenUpsilon6OrdinaryKernel x + originalEnhancement h x

theorem originalResidual_eq_a_mul_profile (x : Point) :
    originalResidual x = (417 / 5000 : ℝ) * currentChenUpsilon6OrdinaryProfile x := by
  unfold originalResidual currentChenUpsilon6OrdinaryProfile
  ring

theorem originalResidual_ge_two_a {eta : ℝ} (heta : 0 ≤ eta) {x : Point}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    2 * (417 / 5000 : ℝ) ≤ originalResidual x := by
  rw [originalResidual_eq_a_mul_profile]
  have h := mul_le_mul_of_nonneg_left (profile_range heta hx).1
    (by norm_num : (0 : ℝ) ≤ 417 / 5000)
  linarith

/-- Integrability of the true 1/(R*u*v) weight is paid on the full literal
rectangle using its compact closure and strictly positive margins. -/
theorem integrableOn_originalWeight :
    IntegrableOn originalWeight currentChenUpsilon6LogRectangle := by
  let C : Set Point := Set.univ.pi (fun i => Set.Icc
    (![(417 / 5000 : ℝ), 19 / 125] i) (![(19 / 125 : ℝ), 59 / 250] i))
  have hC : IsCompact C := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hcoords (x : Point) (hx : x ∈ C) :
      0 < x 0 ∧ 0 < x 1 ∧ (14 / 125 : ℝ) ≤ originalResidual x := by
    have hx0 := hx 0 (Set.mem_univ _)
    have hx1 := hx 1 (Set.mem_univ _)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx0 hx1
    unfold originalResidual
    constructor
    · linarith [hx0.1]
    constructor
    · linarith [hx1.1]
    · linarith [hx0.2, hx1.2]
  have hcR : Continuous originalResidual := by
    unfold originalResidual
    fun_prop
  have hc : ContinuousOn originalWeight C := by
    unfold originalWeight
    apply continuousOn_const.div
      ((hcR.continuousOn.mul (continuous_apply 0).continuousOn).mul
        (continuous_apply 1).continuousOn)
    intro x hx
    obtain ⟨h0, h1, hR⟩ := hcoords x hx
    have hRp : 0 < originalResidual x := lt_of_lt_of_le (by norm_num) hR
    exact mul_ne_zero (mul_ne_zero hRp.ne' h0.ne') h1.ne'
  have hsub : currentChenUpsilon6LogRectangle ⊆ C := by
    intro x hx i _
    obtain ⟨ha, hh, hh', hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
    fin_cases i
    · exact ⟨ha, hh.le⟩
    · exact ⟨hh', hd.le⟩
  exact (hc.integrableOn_compact hC).mono_set hsub

theorem originalEnhancement_floor_eq_sum {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (x : Point) :
    originalEnhancement (finiteFloor knots c) x =
      ∑ i : Fin n, (4 * c i) *
        (profileBand (knots i.castSucc) (knots i.succ)).indicator originalWeight x := by
  unfold originalEnhancement finiteFloor
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : currentChenUpsilon6OrdinaryProfile x ∈
      Ico (knots i.castSucc) (knots i.succ)
  · have hx : x ∈ profileBand (knots i.castSucc) (knots i.succ) := hi
    rw [if_pos hi, indicator_of_mem hx]
    unfold originalWeight
    ring
  · have hx : x ∉ profileBand (knots i.castSucc) (knots i.succ) := hi
    rw [if_neg hi, indicator_of_notMem hx]
    ring

theorem integrableOn_originalBandWeight (lo hi : ℝ) :
    IntegrableOn ((profileBand lo hi).indicator originalWeight)
      currentChenUpsilon6LogRectangle :=
  integrableOn_originalWeight.indicator (measurableSet_profileBand lo hi)

theorem integrableOn_originalFloorEnhancement {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) :
    IntegrableOn (originalEnhancement (finiteFloor knots c)) currentChenUpsilon6LogRectangle := by
  have heq : originalEnhancement (finiteFloor knots c) = fun x =>
      ∑ i : Fin n, (4 * c i) *
        (profileBand (knots i.castSucc) (knots i.succ)).indicator originalWeight x := by
    funext x
    exact originalEnhancement_floor_eq_sum knots c x
  rw [heq]
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (integrableOn_originalBandWeight (knots i.castSucc) (knots i.succ)).const_mul _)

theorem integral_originalFloorEnhancement_eq_band_sum {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, originalEnhancement (finiteFloor knots c) x) =
      ∑ i : Fin n, (4 * c i) *
        ∫ x in currentChenUpsilon6LogDomain eta ∩
          profileBand (knots i.castSucc) (knots i.succ), originalWeight x := by
  simp_rw [originalEnhancement_floor_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    ((integrableOn_originalBandWeight (knots i.castSucc) (knots i.succ)).const_mul
      (4 * c i)).mono_set inter_subset_left)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, setIntegral_indicator (measurableSet_profileBand _ _)]

theorem integral_originalEnhancedFloor_eq_ordinary_add {n : ℕ}
    (knots : Fin (n + 1) → ℝ) (c : Fin n → ℝ) (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, originalEnhancedKernel (finiteFloor knots c) x) =
      (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x) +
        ∑ i : Fin n, (4 * c i) *
          ∫ x in currentChenUpsilon6LogDomain eta ∩
            profileBand (knots i.castSucc) (knots i.succ), originalWeight x := by
  unfold originalEnhancedKernel
  rw [integral_add (integrableOn_currentChenUpsilon6OrdinaryKernel_domain eta)
    ((integrableOn_originalFloorEnhancement knots c).mono_set inter_subset_left),
    integral_originalFloorEnhancement_eq_band_sum]

/-- Scalar equality away from knots. The proof compares the actual finite
atom sum, including all 201 singleton atoms, with the half-open cells. -/
theorem floorStep_eq_halfopen_of_ne_grid (nums : Fin 200 → ℤ) (s : ℝ)
    (hs : s ∈ Icc (2 : ℝ) 5)
    (hne : ∀ j : Fin 201, s ≠ floorGrid j.val) :
    floorStep nums s = finiteFloor adoptedKnots (floorValue nums) s := by
  have hk : (∑ j : Fin 201,
      (floorAtomSet (Sum.inr j)).indicator (fun _ => floorAtomValue nums (Sum.inr j)) s) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : s ∉ floorAtomSet (Sum.inr j) := by
      intro h
      exact hne j h.2
    exact indicator_of_notMem hj _
  have hc : (∑ i : Fin 200,
      (floorAtomSet (Sum.inl i)).indicator (fun _ => floorAtomValue nums (Sum.inl i)) s) =
        finiteFloor adoptedKnots (floorValue nums) s := by
    apply Finset.sum_congr rfl
    intro i _
    have hnelo : s ≠ floorGrid i.val := hne i.castSucc
    have heq : s ∈ floorAtomSet (Sum.inl i) ↔
        s ∈ Ico (adoptedKnots i.castSucc) (adoptedKnots i.succ) := by
      change (s ∈ Icc (2 : ℝ) 5 ∧
        floorGrid i.val < s ∧ s < floorGrid (i.val + 1)) ↔
          (floorGrid i.val ≤ s ∧ s < floorGrid (i.val + 1))
      constructor
      · exact fun h => ⟨h.2.1.le, h.2.2⟩
      · intro h
        exact ⟨hs, lt_of_le_of_ne h.1 (Ne.symm hnelo), h.2⟩
    by_cases hi : s ∈ Ico (adoptedKnots i.castSucc) (adoptedKnots i.succ)
    · rw [indicator_of_mem (heq.mpr hi), if_pos hi]
      rfl
    · have hnot : s ∉ floorAtomSet (Sum.inl i) := fun h => hi (heq.mp h)
      rw [indicator_of_notMem hnot, if_neg hi]
  unfold floorStep
  rw [Fintype.sum_sum_type, hk, add_zero]
  exact hc

/-- Every lookup knot pulls back to the corresponding literal affine line. -/
theorem profile_wall_eq (s : ℝ) :
    {x : Point | currentChenUpsilon6OrdinaryProfile x = s} =
      {x : Point | x 0 + x 1 = (1 / 2 : ℝ) - (417 / 5000 : ℝ) * s} := by
  ext x
  change currentChenUpsilon6OrdinaryProfile x = s ↔ _
  unfold currentChenUpsilon6OrdinaryProfile
  constructor <;> intro h <;> norm_num at * <;> linarith

theorem profile_wall_volume_zero (s : ℝ) :
    volume {x : Point | currentChenUpsilon6OrdinaryProfile x = s} = 0 := by
  rw [profile_wall_eq]
  exact currentChenUpsilon6_productWall_volume_zero _

/-- All 201 possible scalar knot discrepancies lie on a finite family of
proved null affine walls, before restriction to any corrected product domain. -/
theorem ae_profile_ne_all_knots :
    ∀ᵐ x : Point ∂volume, ∀ j : Fin 201,
      currentChenUpsilon6OrdinaryProfile x ≠ floorGrid j.val := by
  apply ae_all_iff.mpr
  intro j
  rw [ae_iff]
  simpa only [not_not] using profile_wall_volume_zero (floorGrid j.val)

/-- Adopted lookup identification is a conclusion from the literal table
definitions and null affine walls, rather than an identification premise. -/
theorem adoptedFloor_profile_ae_eq_halfopen {eta : ℝ} (heta : 0 ≤ eta) :
    (fun x : Point => adoptedH248Floor (currentChenUpsilon6OrdinaryProfile x)) =ᵐ[
      volume.restrict (currentChenUpsilon6LogDomain eta)]
        (fun x : Point => finiteFloor adoptedKnots adoptedCoefficients
          (currentChenUpsilon6OrdinaryProfile x)) := by
  filter_upwards [ae_restrict_of_ae ae_profile_ne_all_knots,
    ae_restrict_mem (P5U6RunboProductSlicesSourceOnly.measurableSet_productDomain eta)]
    with x hne hx
  have hp := profile_range heta hx
  have hs : currentChenUpsilon6OrdinaryProfile x ∈ Icc (2 : ℝ) 5 :=
    ⟨hp.1, hp.2.trans (by norm_num)⟩
  exact floorStep_eq_halfopen_of_ne_grid adoptedH248Numerators _ hs hne

theorem adopted_enhancement_ae_eq_halfopen {eta : ℝ} (heta : 0 ≤ eta) :
    originalEnhancement adoptedH248Floor =ᵐ[volume.restrict (currentChenUpsilon6LogDomain eta)]
      originalEnhancement (finiteFloor adoptedKnots adoptedCoefficients) := by
  filter_upwards [adoptedFloor_profile_ae_eq_halfopen heta] with x hx
  unfold originalEnhancement
  rw [hx]

theorem adopted_enhancedKernel_ae_eq_halfopen {eta : ℝ} (heta : 0 ≤ eta) :
    originalEnhancedKernel adoptedH248Floor =ᵐ[volume.restrict (currentChenUpsilon6LogDomain eta)]
      originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) := by
  filter_upwards [adopted_enhancement_ae_eq_halfopen heta] with x hx
  unfold originalEnhancedKernel
  rw [hx]

/-- Integrability on the actual U6 corrected domain follows by a.e. equality
to the already integrable finite table; no adopted-table soundness is used. -/
theorem integrableOn_adoptedEnhancement {eta : ℝ} (heta : 0 ≤ eta) :
    IntegrableOn (originalEnhancement adoptedH248Floor) (currentChenUpsilon6LogDomain eta) :=
  ((integrableOn_originalFloorEnhancement adoptedKnots adoptedCoefficients).mono_set inter_subset_left).congr
    (adopted_enhancement_ae_eq_halfopen heta).symm

theorem integrableOn_adoptedEnhancedKernel {eta : ℝ} (heta : 0 ≤ eta) :
    IntegrableOn (originalEnhancedKernel adoptedH248Floor) (currentChenUpsilon6LogDomain eta) :=
  (integrableOn_currentChenUpsilon6OrdinaryKernel_domain eta).add
    (integrableOn_adoptedEnhancement heta)

/-- Exact integral floor-band sum for the literal adopted lookup. Singleton
minimum values at knots contribute zero because their U6 pullbacks are null. -/
theorem integral_adoptedEnhancement_eq_band_sum {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ x in currentChenUpsilon6LogDomain eta, originalEnhancement adoptedH248Floor x) =
      ∑ i : Fin 200, (4 * adoptedCoefficients i) *
        ∫ x in currentChenUpsilon6LogDomain eta ∩
          profileBand (adoptedKnots i.castSucc) (adoptedKnots i.succ), originalWeight x := by
  calc
    _ = ∫ x in currentChenUpsilon6LogDomain eta,
        originalEnhancement (finiteFloor adoptedKnots adoptedCoefficients) x :=
      integral_congr_ae (adopted_enhancement_ae_eq_halfopen heta)
    _ = _ := integral_originalFloorEnhancement_eq_band_sum adoptedKnots adoptedCoefficients eta

theorem integral_adoptedEnhancedKernel_eq_ordinary_add {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ x in currentChenUpsilon6LogDomain eta, originalEnhancedKernel adoptedH248Floor x) =
      (∫ x in currentChenUpsilon6LogDomain eta, currentChenUpsilon6OrdinaryKernel x) +
        ∑ i : Fin 200, (4 * adoptedCoefficients i) *
          ∫ x in currentChenUpsilon6LogDomain eta ∩
            profileBand (adoptedKnots i.castSucc) (adoptedKnots i.succ), originalWeight x := by
  calc
    _ = ∫ x in currentChenUpsilon6LogDomain eta,
        originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) x :=
      integral_congr_ae (adopted_enhancedKernel_ae_eq_halfopen heta)
    _ = _ := integral_originalEnhancedFloor_eq_ordinary_add adoptedKnots adoptedCoefficients eta

/-- The original normalized adopted enhancement has a proved right buffer
limit, after identifying it a.e. with the actual finite floor on each domain. -/
theorem tendsto_adoptedEnhancedKernel_integral_right :
    Tendsto (fun eta : ℝ => ∫ x in currentChenUpsilon6LogDomain eta,
      originalEnhancedKernel adoptedH248Floor x) (𝓝[>] 0)
        (𝓝 (∫ x in currentChenUpsilon6LogDomain 0, originalEnhancedKernel adoptedH248Floor x)) := by
  have h := (P5U6RunboBufferLimitSourceOnly.tendsto_integral_productDomain
    (originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients))
    (integrableOn_currentChenUpsilon6OrdinaryKernel.add
      (integrableOn_originalFloorEnhancement adoptedKnots adoptedCoefficients))).mono_left
        nhdsWithin_le_nhds
  have hzero : (∫ x in currentChenUpsilon6LogDomain 0, originalEnhancedKernel adoptedH248Floor x) =
      ∫ x in currentChenUpsilon6LogDomain 0,
        originalEnhancedKernel (finiteFloor adoptedKnots adoptedCoefficients) x :=
    integral_congr_ae (adopted_enhancedKernel_ae_eq_halfopen (by norm_num))
  rw [← hzero] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with eta heta
  exact (integral_congr_ae (adopted_enhancedKernel_ae_eq_halfopen heta.le)).symm

end

end ImbalancedChen.P5U6AdoptedH248BindingSourceOnly
