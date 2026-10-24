import ImbalancedChen.AffinePrimeGates
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The literal real three-exponent domain for marked U9

SOURCE ONLY / UNCOMPILED. Everything here is a real Lebesgue-domain fact.
No arithmetic prime boundary estimate or fixed-buffer source-mass estimate
is inferred from a null wall or from dominated convergence.
-/

namespace ImbalancedChen.P5U9RealDomain

noncomputable section

open MeasureTheory Filter Set
open scoped Classical BigOperators Topology

abbrev Point := Fin 3 → ℝ

/-- Exact mixed ownership from the original pair bands, moving p₂ wall,
and original square-root lower/physical-product upper walls for q. -/
def domain : Set Point :=
  {x | (19 / 125 : ℝ) ≤ x 0 ∧ x 0 < 59 / 250 ∧ 59 / 250 ≤ x 1 ∧
    x 0 + 2 * x 1 < 1 ∧ 1 ≤ x 0 + x 1 + 2 * x 2 ∧ x 0 + x 1 + x 2 < 1}

def forms : Fin 6 → Point →L[ℝ] ℝ :=
  ![-(ContinuousLinearMap.proj (0 : Fin 3) : Point →L[ℝ] ℝ), (ContinuousLinearMap.proj (0 : Fin 3) : Point →L[ℝ] ℝ),
    -(ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ),
    (ContinuousLinearMap.proj (0 : Fin 3) : Point →L[ℝ] ℝ) + (2 : ℝ) • (ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ),
    -((ContinuousLinearMap.proj (0 : Fin 3) : Point →L[ℝ] ℝ) + (ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ) +
      (2 : ℝ) • (ContinuousLinearMap.proj (2 : Fin 3) : Point →L[ℝ] ℝ)),
    (ContinuousLinearMap.proj (0 : Fin 3) : Point →L[ℝ] ℝ) + (ContinuousLinearMap.proj (1 : Fin 3) : Point →L[ℝ] ℝ) + (ContinuousLinearMap.proj (2 : Fin 3) : Point →L[ℝ] ℝ)]

def bounds : Fin 6 → ℝ := ![-(19 / 125), 59 / 250, -(59 / 250), 1, -1, 1]

def weakDomain : Set Point := {x | ∀ j, forms j x ≤ bounds j}

def cube : Set Point := Set.univ.pi (fun _ => Icc (19 / 125 : ℝ) 1)

theorem forms_ne_zero : ∀ j, forms j ≠ 0 := by
  intro j hj
  have h := congrArg (fun L : Point →L[ℝ] ℝ => L (fun _ => 1)) hj
  fin_cases j <;> norm_num [forms] at h

theorem mem_weakDomain_iff (x : Point) :
    x ∈ weakDomain ↔
      (19 / 125 : ℝ) ≤ x 0 ∧ x 0 ≤ 59 / 250 ∧ 59 / 250 ≤ x 1 ∧
      x 0 + 2 * x 1 ≤ 1 ∧ 1 ≤ x 0 + x 1 + 2 * x 2 ∧ x 0 + x 1 + x 2 ≤ 1 := by
  constructor
  · intro hx
    have h0 := hx (0 : Fin 6)
    have h1 := hx (1 : Fin 6)
    have h2 := hx (2 : Fin 6)
    have h3 := hx (3 : Fin 6)
    have h4 := hx (4 : Fin 6)
    have h5 := hx (5 : Fin 6)
    simp [forms, bounds] at h0 h1 h2 h3 h4 h5
    exact ⟨h0, h1, h2, h3, by linarith only [h4], h5⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5⟩ j
    fin_cases j <;> simp [forms, bounds] <;> linarith

theorem domain_vec_iff (t u w : ℝ) :
    ![t, u, w] ∈ domain ↔
      t ∈ Ico (19 / 125 : ℝ) (59 / 250 : ℝ) ∧
      u ∈ Ico (59 / 250 : ℝ) ((1 - t) / 2) ∧
      w ∈ Ico ((1 - t - u) / 2) (1 - t - u) := by
  change ((19 / 125 : ℝ) ≤ t ∧ t < 59 / 250 ∧ 59 / 250 ≤ u ∧
    t + 2 * u < 1 ∧ 1 ≤ t + u + 2 * w ∧ t + u + w < 1) ↔ _
  constructor
  · rintro ⟨ht0, ht1, hu0, hu1, hw0, hw1⟩
    exact ⟨⟨ht0, ht1⟩, ⟨hu0, by linarith only [hu1]⟩,
      ⟨by linarith only [hw0], by linarith only [hw1]⟩⟩
  · rintro ⟨ht, hu, hw⟩
    exact ⟨ht.1, ht.2, hu.1, by linarith only [hu.2],
      by linarith only [hw.1], by linarith only [hw.2]⟩

theorem domain_subset_weakDomain : domain ⊆ weakDomain := by
  intro x hx
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hx
  exact (mem_weakDomain_iff x).mpr ⟨h0, h1.le, h2, h3.le, h4, h5.le⟩

theorem strictDomain_subset_domain : primeAffineGateRegion forms bounds ⊆ domain := by
  intro x hx
  have h0 := hx (0 : Fin 6)
  have h1 := hx (1 : Fin 6)
  have h2 := hx (2 : Fin 6)
  have h3 := hx (3 : Fin 6)
  have h4 := hx (4 : Fin 6)
  have h5 := hx (5 : Fin 6)
  simp [forms, bounds] at h0 h1 h2 h3 h4 h5
  exact ⟨h0.le, h1, h2.le, h3, by linarith only [h4], h5⟩

theorem measurableSet_domain : MeasurableSet domain := by
  have h0 : Continuous (fun x : Point => x 0) := continuous_apply 0
  have h1 : Continuous (fun x : Point => x 1) := continuous_apply 1
  have h2 : Continuous (fun x : Point => x 2) := continuous_apply 2
  exact (isClosed_le continuous_const h0).measurableSet.inter
    ((isOpen_lt h0 continuous_const).measurableSet.inter
      ((isClosed_le continuous_const h1).measurableSet.inter
        ((isOpen_lt (h0.add (continuous_const.mul h1)) continuous_const).measurableSet.inter
          ((isClosed_le continuous_const ((h0.add h1).add (continuous_const.mul h2))).measurableSet.inter
            (isOpen_lt ((h0.add h1).add h2) continuous_const).measurableSet))))

theorem isClosed_weakDomain : IsClosed weakDomain := by
  simpa only [weakDomain, ofPred_forall] using
    isClosed_iInter (fun j => isClosed_le (forms j).continuous continuous_const)

theorem weakDomain_coordinate_bounds {x : Point} (hx : x ∈ weakDomain) :
    ∀ i, (19 / 125 : ℝ) ≤ x i ∧ x i ≤ 1 := by
  obtain ⟨ht0, ht1, hu0, hu1, hw0, hw1⟩ := (mem_weakDomain_iff x).mp hx
  intro i
  fin_cases i
  · change (19 / 125 : ℝ) ≤ x 0 ∧ x 0 ≤ 1
    constructor <;> linarith
  · change (19 / 125 : ℝ) ≤ x 1 ∧ x 1 ≤ 1
    constructor <;> linarith
  · change (19 / 125 : ℝ) ≤ x 2 ∧ x 2 ≤ 1
    constructor <;> linarith

theorem weakDomain_terminal_lower {x : Point} (hx : x ∈ weakDomain) :
    (191 / 1000 : ℝ) ≤ x 2 := by
  obtain ⟨ht0, ht1, hu0, hu1, hw0, hw1⟩ := (mem_weakDomain_iff x).mp hx
  linarith

theorem weakDomain_subset_cube : weakDomain ⊆ cube := by
  intro x hx i _hi
  exact weakDomain_coordinate_bounds hx i

theorem isCompact_cube : IsCompact cube := isCompact_univ_pi (fun _ => isCompact_Icc)

theorem isCompact_weakDomain : IsCompact weakDomain :=
  isCompact_cube.of_isClosed_subset isClosed_weakDomain weakDomain_subset_cube

/-- The actual closure is compact and retains the same uniform lower
coordinate gate; identifying it with the full polytope is unnecessary. -/
theorem closure_domain_subset_weakDomain : closure domain ⊆ weakDomain :=
  closure_minimal domain_subset_weakDomain isClosed_weakDomain

theorem isCompact_closure_domain : IsCompact (closure domain) :=
  isCompact_weakDomain.of_isClosed_subset isClosed_closure closure_domain_subset_weakDomain

theorem closure_domain_coordinate_bounds {x : Point} (hx : x ∈ closure domain) :
    ∀ i, (19 / 125 : ℝ) ≤ x i ∧ x i ≤ 1 :=
  weakDomain_coordinate_bounds (closure_domain_subset_weakDomain hx)

/-- Every one of the six genuine boundary planes is a proper affine
subspace, hence null for the actual three-dimensional Lebesgue volume. -/
theorem wall_volume_zero (j : Fin 6) : volume {x : Point | forms j x = bounds j} = 0 :=
  affinePrimeWall_volume_zero (forms j) (forms_ne_zero j) (bounds j)

theorem ae_no_walls : ∀ᵐ x : Point ∂volume, ∀ j, forms j x ≠ bounds j :=
  ae_primeAffineGate_no_wall forms bounds forms_ne_zero

def boundaryWalls : Set Point := {x | ∃ j, forms j x = bounds j}

theorem boundaryWalls_volume_zero : volume boundaryWalls = 0 := by
  have h : ∀ᵐ x : Point ∂volume, x ∉ boundaryWalls := by
    filter_upwards [ae_no_walls] with x hx
    rintro ⟨j, hj⟩
    exact hx j hj
  rw [ae_iff] at h
  simpa only [not_not, Set.ofPred_mem_eq] using h

theorem domain_ae_weakDomain : domain =ᵐ[volume] weakDomain := by
  filter_upwards [ae_no_walls] with x hx
  apply propext
  refine ⟨fun hd => domain_subset_weakDomain hd, ?_⟩
  intro hw
  apply strictDomain_subset_domain
  intro j
  exact lt_of_le_of_ne (hw j) (hx j)

theorem setIntegral_domain_eq_weakDomain (f : Point → ℝ) :
    (∫ x in domain, f x) = ∫ x in weakDomain, f x :=
  setIntegral_congr_set domain_ae_weakDomain

def kernel (x : Point) : ℝ := 1 / (x 0 * x 1 * x 2)
def squaredTerminalKernel (x : Point) : ℝ := 1 / (x 0 * x 1 * (x 2) ^ 2)

theorem continuousOn_kernel_cube : ContinuousOn kernel cube := by
  apply continuousOn_const.div
    (((continuous_apply 0).mul (continuous_apply 1)).mul (continuous_apply 2)).continuousOn
  intro x hx
  apply ne_of_gt
  have hpos (i : Fin 3) : 0 < x i :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 19 / 125) (hx i (Set.mem_univ i)).1
  exact mul_pos (mul_pos (hpos 0) (hpos 1)) (hpos 2)

theorem continuousOn_squaredTerminalKernel_cube : ContinuousOn squaredTerminalKernel cube := by
  apply continuousOn_const.div
    (((continuous_apply 0).mul (continuous_apply 1)).mul ((continuous_apply 2).pow 2)).continuousOn
  intro x hx
  apply ne_of_gt
  have hpos (i : Fin 3) : 0 < x i :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 19 / 125) (hx i (Set.mem_univ i)).1
  exact mul_pos (mul_pos (hpos 0) (hpos 1)) (sq_pos_of_pos (hpos 2))

theorem integrableOn_kernel_cube : IntegrableOn kernel cube :=
  continuousOn_kernel_cube.integrableOn_compact isCompact_cube

theorem integrableOn_squaredTerminalKernel_cube : IntegrableOn squaredTerminalKernel cube :=
  continuousOn_squaredTerminalKernel_cube.integrableOn_compact isCompact_cube

theorem integrableOn_kernel_domain : IntegrableOn kernel domain :=
  integrableOn_kernel_cube.mono_set (domain_subset_weakDomain.trans weakDomain_subset_cube)

theorem integrableOn_squaredTerminalKernel_domain : IntegrableOn squaredTerminalKernel domain :=
  integrableOn_squaredTerminalKernel_cube.mono_set
    (domain_subset_weakDomain.trans weakDomain_subset_cube)

theorem continuousOn_kernel_closure : ContinuousOn kernel (closure domain) :=
  continuousOn_kernel_cube.mono (closure_domain_subset_weakDomain.trans weakDomain_subset_cube)

theorem continuousOn_squaredTerminalKernel_closure :
    ContinuousOn squaredTerminalKernel (closure domain) :=
  continuousOn_squaredTerminalKernel_cube.mono
    (closure_domain_subset_weakDomain.trans weakDomain_subset_cube)

theorem integrableOn_kernel_closure : IntegrableOn kernel (closure domain) :=
  continuousOn_kernel_closure.integrableOn_compact isCompact_closure_domain

theorem integrableOn_squaredTerminalKernel_closure :
    IntegrableOn squaredTerminalKernel (closure domain) :=
  continuousOn_squaredTerminalKernel_closure.integrableOn_compact isCompact_closure_domain

def gate (eta : ℝ) : Set Point := {x | ∀ j, forms j x ≤ bounds j - eta}
def bufferDomain (eta : ℝ) : Set Point := cube ∩ gate eta

theorem measurableSet_gate (eta : ℝ) : MeasurableSet (gate eta) := by
  simpa only [gate, ofPred_forall] using
    MeasurableSet.iInter (fun j => (isClosed_le (forms j).continuous continuous_const).measurableSet)

theorem bufferDomain_zero : bufferDomain 0 = weakDomain := by
  ext x
  simp only [bufferDomain, gate, sub_zero, Set.mem_inter_iff, Set.mem_setOf_eq]
  exact ⟨fun hx => hx.2, fun hx => ⟨weakDomain_subset_cube hx, hx⟩⟩

private theorem eventually_gate_membership (x : Point) (hx : ∀ j, forms j x ≠ bounds j) :
    ∀ᶠ eta : ℝ in 𝓝 0, (x ∈ gate eta ↔ x ∈ gate 0) := by
  have heach (j : Fin 6) : ∀ᶠ eta : ℝ in 𝓝 0,
      (forms j x ≤ bounds j - eta ↔ forms j x ≤ bounds j) := by
    rcases lt_or_gt_of_ne (hx j) with hlt | hgt
    · filter_upwards [Iio_mem_nhds (sub_pos.mpr hlt)] with eta heta
      change eta < bounds j - forms j x at heta
      constructor <;> intro _h <;> linarith only [hlt, heta]
    · filter_upwards [Ioi_mem_nhds (sub_neg.mpr hgt)] with eta heta
      change bounds j - forms j x < eta at heta
      constructor <;> intro hh <;> linarith only [hgt, heta, hh]
  filter_upwards [eventually_all.mpr heach] with eta heta
  simpa only [gate, Set.mem_setOf_eq, sub_zero] using forall_congr' heta

/-- Genuine real-domain DCT on a fixed compact cube. This is deliberately
not an assertion that a fixed exponent erosion preserves actual prime mass. -/
theorem tendsto_integral_bufferDomain (f : Point → ℝ) (hf : IntegrableOn f cube) :
    Tendsto (fun eta : ℝ => ∫ x in bufferDomain eta, f x) (𝓝 0)
      (𝓝 (∫ x in domain, f x)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict cube) (f := (gate 0).indicator f)
    (F := fun eta : ℝ => (gate eta).indicator f) (fun x : Point => ‖f x‖)
    (Eventually.of_forall (fun eta => (hf.indicator (measurableSet_gate eta)).aestronglyMeasurable))
    (Eventually.of_forall (fun eta => Eventually.of_forall
      (fun x => norm_indicator_le_norm_self (s := gate eta) f x)))
    hf.norm
    (show ∀ᵐ x : Point ∂volume.restrict cube,
      Tendsto (fun eta : ℝ => (gate eta).indicator f x) (𝓝 0)
        (𝓝 ((gate 0).indicator f x)) from by
      filter_upwards [ae_restrict_of_ae ae_no_walls] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gate_membership x hx] with eta heta
      by_cases hx0 : x ∈ gate 0
      · simp only [indicator_of_mem hx0, indicator_of_mem (heta.mpr hx0)]
      · simp only [indicator_of_notMem hx0, indicator_of_notMem (mt heta.mp hx0)])
  have hlim' : Tendsto (fun eta : ℝ => ∫ x in bufferDomain eta, f x) (𝓝 0)
      (𝓝 (∫ x in weakDomain, f x)) := by
    simp only [setIntegral_indicator (measurableSet_gate _)] at hlim
    change Tendsto (fun eta : ℝ => ∫ x in bufferDomain eta, f x) (𝓝 0)
      (𝓝 (∫ x in bufferDomain 0, f x)) at hlim
    simpa only [bufferDomain_zero] using hlim
  rwa [← setIntegral_domain_eq_weakDomain f] at hlim'

theorem tendsto_abs_buffer_loss_right (f : Point → ℝ) (hf : IntegrableOn f cube) :
    Tendsto (fun eta : ℝ => |(∫ x in domain, f x) - (∫ x in bufferDomain eta, f x)|)
      (𝓝[>] 0) (𝓝 0) := by
  have hc : Tendsto (fun _eta : ℝ => ∫ x in domain, f x) (𝓝 0)
      (𝓝 (∫ x in domain, f x)) := tendsto_const_nhds
  have h := (hc.sub (tendsto_integral_bufferDomain f hf)).abs
  have hzero : Tendsto
      (fun eta : ℝ => |(∫ x in domain, f x) - (∫ x in bufferDomain eta, f x)|)
      (𝓝 0) (𝓝 0) := by simpa only [sub_self, abs_zero] using h
  exact hzero.mono_left nhdsWithin_le_nhds

/-- Select one positive real buffer after the desired real-integral
tolerance. No arithmetic threshold or arithmetic source mass occurs. -/
theorem exists_positive_buffer (f : Point → ℝ) (hf : IntegrableOn f cube)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ eta : ℝ, 0 < eta ∧
      |(∫ x in domain, f x) - (∫ x in bufferDomain eta, f x)| < ε := by
  have hnear : ∀ᶠ eta : ℝ in 𝓝[>] 0, 0 < eta ∧
      |(∫ x in domain, f x) - (∫ x in bufferDomain eta, f x)| < ε := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_abs_buffer_loss_right f hf).eventually (Iio_mem_nhds hε)] with eta heta hI
    exact ⟨heta, hI⟩
  exact hnear.exists

theorem tendsto_kernel_buffer_integral :
    Tendsto (fun eta : ℝ => ∫ x in bufferDomain eta, kernel x) (𝓝 0)
      (𝓝 (∫ x in domain, kernel x)) :=
  tendsto_integral_bufferDomain kernel integrableOn_kernel_cube

theorem tendsto_squaredKernel_buffer_integral :
    Tendsto (fun eta : ℝ => ∫ x in bufferDomain eta, squaredTerminalKernel x) (𝓝 0)
      (𝓝 (∫ x in domain, squaredTerminalKernel x)) :=
  tendsto_integral_bufferDomain squaredTerminalKernel integrableOn_squaredTerminalKernel_cube

/-- Continuous affine clamps approximate the actual mixed sharp domain
in its genuine real integral. The integrable dominator is the fixed kernel
norm on the compact cube, not an arithmetic wall-density hypothesis. -/
theorem tendsto_integral_continuous_ramps (f : Point → ℝ)
    (hf : ContinuousOn f cube) (upper : Bool) :
    Tendsto (fun m : ℕ => ∫ x in cube, f x * affinePrimeGateRamp forms bounds upper m x)
      atTop (𝓝 (∫ x in domain, f x)) := by
  have hfi : IntegrableOn f cube (volume : Measure Point) :=
    hf.integrableOn_compact isCompact_cube
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict cube) (fun x : Point => ‖f x‖)
    (fun m => ((hf.mul (continuous_affinePrimeGateRamp forms bounds upper m).continuousOn).integrableOn_compact
      isCompact_cube).aestronglyMeasurable)
    hfi.norm
    (fun m => by
      filter_upwards [] with x
      have hb := affinePrimeGateRamp_bounds forms bounds upper m x
      change ‖f x * affinePrimeGateRamp forms bounds upper m x‖ ≤ ‖f x‖
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1]
      exact mul_le_of_le_one_right (abs_nonneg (f x)) hb.2)
    (show ∀ᵐ x : Point ∂volume.restrict cube,
      Tendsto (fun m : ℕ => f x * affinePrimeGateRamp forms bounds upper m x)
        atTop (𝓝 (domain.indicator f x)) from by
      filter_upwards [ae_restrict_of_ae ae_no_walls] with x hx
      have hmem : x ∈ primeAffineGateRegion forms bounds ↔ x ∈ domain := by
        refine ⟨fun hs => strictDomain_subset_domain hs, ?_⟩
        intro hd j
        exact lt_of_le_of_ne (domain_subset_weakDomain hd j) (hx j)
      have hvalue : f x * (primeAffineGateRegion forms bounds).indicator (fun _ => (1 : ℝ)) x =
          domain.indicator f x := by
        by_cases hd : x ∈ domain
        · rw [indicator_of_mem hd, indicator_of_mem (hmem.mpr hd), mul_one]
        · rw [indicator_of_notMem hd, indicator_of_notMem (mt hmem.mp hd), mul_zero]
      simpa only [hvalue] using
        (tendsto_affinePrimeGateRamp forms bounds upper x hx).const_mul (f x))
  have hinter : cube ∩ domain = domain :=
    inter_eq_right.mpr (domain_subset_weakDomain.trans weakDomain_subset_cube)
  simp only [setIntegral_indicator measurableSet_domain, hinter] at hlim
  exact hlim

theorem tendsto_kernel_continuous_ramps (upper : Bool) :
    Tendsto (fun m : ℕ => ∫ x in cube, kernel x * affinePrimeGateRamp forms bounds upper m x)
      atTop (𝓝 (∫ x in domain, kernel x)) :=
  tendsto_integral_continuous_ramps kernel continuousOn_kernel_cube upper

theorem tendsto_squaredKernel_continuous_ramps (upper : Bool) :
    Tendsto (fun m : ℕ => ∫ x in cube,
      squaredTerminalKernel x * affinePrimeGateRamp forms bounds upper m x)
      atTop (𝓝 (∫ x in domain, squaredTerminalKernel x)) :=
  tendsto_integral_continuous_ramps squaredTerminalKernel continuousOn_squaredTerminalKernel_cube upper

end

end ImbalancedChen.P5U9RealDomain
