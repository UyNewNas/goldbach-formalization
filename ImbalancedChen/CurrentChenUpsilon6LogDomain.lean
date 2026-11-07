import ImbalancedChen.CurrentChenUpsilon6ProductRestriction
import ImbalancedChen.LogPrimeBoxIntegral
import ImbalancedChen.AffinePrimeGates
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# The literal current sixth selector and its logarithmic boundary

The original labelled prime carrier, coprimality with the centre, deletion
mask, and half-open bands are retained. The extra product bound is exactly
`u + t <= 833/2500 - eta` in the actual logarithmic coordinates.

The analytic statements concern only Lebesgue mass with density `1/(u*t)`
on `[417/5000,19/125) x [19/125,59/250)`. Integrability is proved on this
specific positive rectangle. Its coordinate and product walls have zero
mass, and its product-boundary strips have mass tending to zero.

No measurability is attributed to the arithmetic mask E. The frozen
manuscript's L6 uses the improved h248 kernel; that kernel, the arithmetic
mean, its numerical coefficient, and any interchange of N and eta limits
are not supplied here. The fixed currentC is unchanged.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

/-- The two coordinates keep their original prime labels. -/
def currentChenUpsilon6LogCoordinates (N : ℕ) (p : ℕ × ℕ) : Fin 2 → ℝ :=
  ![Real.log (p.1 : ℝ) / Real.log (N : ℝ),
    Real.log (p.2 : ℝ) / Real.log (N : ℝ)]

/-- The actual current pair rectangle, with its original half-open walls. -/
def currentChenUpsilon6LogRectangle : Set (Fin 2 → ℝ) :=
  logPrimeBox ![(417 / 5000 : ℝ), 19 / 125] ![(19 / 125 : ℝ), 59 / 250]

@[simp] theorem mem_currentChenUpsilon6LogRectangle {x : Fin 2 → ℝ} :
    x ∈ currentChenUpsilon6LogRectangle ↔
      (417 / 5000 : ℝ) ≤ x 0 ∧ x 0 < 19 / 125 ∧
      (19 / 125 : ℝ) ≤ x 1 ∧ x 1 < 59 / 250 := by
  simp [currentChenUpsilon6LogRectangle, mem_logPrimeBox,
    Fin.forall_fin_succ, and_assoc]

/-- The extra buffered product gate on the actual logarithmic rectangle. -/
def currentChenUpsilon6LogDomain (eta : ℝ) : Set (Fin 2 → ℝ) :=
  currentChenUpsilon6LogRectangle ∩ {x | x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta}

private theorem currentChenUpsilon6_log_rpow {N p : ℕ}
    (hN : (1 : ℝ) < N) (hp : 0 < p) :
    (N : ℝ) ^ (Real.log (p : ℝ) / Real.log (N : ℝ)) = p := by
  apply (Real.mul_log_eq_log_iff (zero_lt_one.trans hN)
    (by exact_mod_cast hp)).mp
  exact div_mul_cancel₀ _ (Real.log_pos hN).ne'

/-- Literal selector equivalence; neither prime carrier nor the mask is
replaced by an unproved continuous surrogate. -/
theorem mem_currentChenUpsilon6RetainedSelector_log_iff {N : ℕ}
    (hN : (1 : ℝ) < N) (E : ℕ × ℕ → Prop) (eta : ℝ) (p : ℕ × ℕ) :
    p ∈ currentChenUpsilon6RetainedSelector N E eta ↔
      p.1 ∈ chenAdditivePrimeCarrier N ∧ p.2 ∈ chenAdditivePrimeCarrier N ∧
      ¬ E p ∧ currentChenUpsilon6LogCoordinates N p ∈ currentChenUpsilon6LogDomain eta := by
  have hbands (hp : 0 < p.1) (hq : 0 < p.2) :
      ((N : ℝ) ^ (417 / 5000 : ℝ) ≤ (p.1 : ℝ) ∧
        (p.1 : ℝ) < (N : ℝ) ^ (19 / 125 : ℝ) ∧
        (N : ℝ) ^ (19 / 125 : ℝ) ≤ (p.2 : ℝ) ∧
        (p.2 : ℝ) < (N : ℝ) ^ (59 / 250 : ℝ)) ∧
        ((p.1 * p.2 : ℕ) : ℝ) ≤
          (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta) ↔
      currentChenUpsilon6LogCoordinates N p ∈ currentChenUpsilon6LogDomain eta := by
    have hpw := currentChenUpsilon6_log_rpow hN hp
    have hqw := currentChenUpsilon6_log_rpow hN hq
    have hlo (b : ℝ) : (N : ℝ) ^ b ≤ (p.1 : ℝ) ↔
        b ≤ Real.log (p.1 : ℝ) / Real.log (N : ℝ) := by
      simpa only [hpw] using (Real.rpow_le_rpow_left_iff hN :
        (N : ℝ) ^ b ≤ (N : ℝ) ^ (Real.log (p.1 : ℝ) / Real.log (N : ℝ)) ↔ _)
    have hhi (b : ℝ) : (p.1 : ℝ) < (N : ℝ) ^ b ↔
        Real.log (p.1 : ℝ) / Real.log (N : ℝ) < b := by
      simpa only [hpw] using (Real.rpow_lt_rpow_left_iff hN :
        (N : ℝ) ^ (Real.log (p.1 : ℝ) / Real.log (N : ℝ)) < (N : ℝ) ^ b ↔ _)
    have hlo' (b : ℝ) : (N : ℝ) ^ b ≤ (p.2 : ℝ) ↔
        b ≤ Real.log (p.2 : ℝ) / Real.log (N : ℝ) := by
      simpa only [hqw] using (Real.rpow_le_rpow_left_iff hN :
        (N : ℝ) ^ b ≤ (N : ℝ) ^ (Real.log (p.2 : ℝ) / Real.log (N : ℝ)) ↔ _)
    have hhi' (b : ℝ) : (p.2 : ℝ) < (N : ℝ) ^ b ↔
        Real.log (p.2 : ℝ) / Real.log (N : ℝ) < b := by
      simpa only [hqw] using (Real.rpow_lt_rpow_left_iff hN :
        (N : ℝ) ^ (Real.log (p.2 : ℝ) / Real.log (N : ℝ)) < (N : ℝ) ^ b ↔ _)
    have hprod : (N : ℝ) ^
        (Real.log (p.1 : ℝ) / Real.log (N : ℝ) +
          Real.log (p.2 : ℝ) / Real.log (N : ℝ)) = ((p.1 * p.2 : ℕ) : ℝ) := by
      rw [Real.rpow_add (zero_lt_one.trans hN), hpw, hqw, Nat.cast_mul]
    have hgate : ((p.1 * p.2 : ℕ) : ℝ) ≤
          (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta) ↔
        Real.log (p.1 : ℝ) / Real.log (N : ℝ) +
          Real.log (p.2 : ℝ) / Real.log (N : ℝ) ≤ (833 / 2500 : ℝ) - eta := by
      have hc : (1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) = 833 / 2500 := by norm_num
      simpa only [hprod, hc] using (Real.rpow_le_rpow_left_iff hN :
        (N : ℝ) ^ (Real.log (p.1 : ℝ) / Real.log (N : ℝ) +
          Real.log (p.2 : ℝ) / Real.log (N : ℝ)) ≤
            (N : ℝ) ^ ((1 / 2 : ℝ) - 2 * (417 / 5000 : ℝ) - eta) ↔ _)
    simp only [currentChenUpsilon6LogDomain, mem_inter_iff,
      mem_currentChenUpsilon6LogRectangle, mem_ofPred_eq,
      currentChenUpsilon6LogCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one,
      hlo, hhi, hlo', hhi', hgate]
  constructor
  · intro hp
    obtain ⟨hpMask, hprod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpSelector, hE⟩ := Finset.mem_filter.mp hpMask
    obtain ⟨hpCarrier, hpBands⟩ := Finset.mem_filter.mp hpSelector
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hpCarrier
    exact ⟨hp₁, hp₂, hE,
      (hbands (mem_chenAdditivePrimeCarrier.mp hp₁).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp hp₂).2.1.pos).mp ⟨hpBands, hprod⟩⟩
  · rintro ⟨hp₁, hp₂, hE, hpLog⟩
    obtain ⟨hpBands, hprod⟩ :=
      (hbands (mem_chenAdditivePrimeCarrier.mp hp₁).2.1.pos
        (mem_chenAdditivePrimeCarrier.mp hp₂).2.1.pos).mpr hpLog
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₁, hp₂⟩, hpBands⟩, hE⟩, hprod⟩

/-- Expanded arithmetic content of the same equivalence. -/
theorem mem_currentChenUpsilon6RetainedSelector_log_explicit {N : ℕ}
    (hN : (1 : ℝ) < N) (E : ℕ × ℕ → Prop) (eta : ℝ) (p : ℕ × ℕ) :
    p ∈ currentChenUpsilon6RetainedSelector N E eta ↔
      (p.1 < N ∧ Nat.Prime p.1 ∧ Nat.Coprime p.1 N) ∧
      (p.2 < N ∧ Nat.Prime p.2 ∧ Nat.Coprime p.2 N) ∧ ¬ E p ∧
      (417 / 5000 : ℝ) ≤ Real.log (p.1 : ℝ) / Real.log (N : ℝ) ∧
      Real.log (p.1 : ℝ) / Real.log (N : ℝ) < 19 / 125 ∧
      (19 / 125 : ℝ) ≤ Real.log (p.2 : ℝ) / Real.log (N : ℝ) ∧
      Real.log (p.2 : ℝ) / Real.log (N : ℝ) < 59 / 250 ∧
      Real.log (p.1 : ℝ) / Real.log (N : ℝ) +
        Real.log (p.2 : ℝ) / Real.log (N : ℝ) ≤ (833 / 2500 : ℝ) - eta := by
  rw [mem_currentChenUpsilon6RetainedSelector_log_iff hN]
  simp [mem_chenAdditivePrimeCarrier, currentChenUpsilon6LogDomain,
    currentChenUpsilon6LogCoordinates, and_assoc]

theorem measurableSet_currentChenUpsilon6LogRectangle :
    MeasurableSet currentChenUpsilon6LogRectangle :=
  measurableSet_logPrimeBox _ _

private theorem currentChenUpsilon6_density_eq_prod (x : Fin 2 → ℝ) :
    1 / (x 0 * x 1) = ∏ i : Fin 2, 1 / x i := by
  simp [Fin.prod_univ_succ]

/-- Concrete integrability; no integrability assumption is left to callers. -/
theorem integrableOn_currentChenUpsilon6LogRectangle :
    IntegrableOn (fun x : Fin 2 → ℝ => 1 / (x 0 * x 1))
      currentChenUpsilon6LogRectangle := by
  unfold currentChenUpsilon6LogRectangle
  simpa only [← currentChenUpsilon6_density_eq_prod] using
    (integrableOn_logPrimeBox_one_div
      ![(417 / 5000 : ℝ), 19 / 125] ![(19 / 125 : ℝ), 59 / 250]
      (by norm_num [Fin.forall_fin_succ]))

theorem integrableOn_currentChenUpsilon6LogDomain (eta : ℝ) :
    IntegrableOn (fun x : Fin 2 → ℝ => 1 / (x 0 * x 1))
      (currentChenUpsilon6LogDomain eta) :=
  integrableOn_currentChenUpsilon6LogRectangle.mono_set inter_subset_left

/-- Both actual coordinates are strictly positive throughout the rectangle. -/
theorem currentChenUpsilon6LogRectangle_coordinates_pos {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogRectangle) : 0 < x 0 ∧ 0 < x 1 := by
  obtain ⟨ha, _, hh, _⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
  constructor <;> linarith

private def currentChenUpsilon6ProductForm : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ) +
    (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ)

private theorem currentChenUpsilon6ProductForm_ne_zero :
    currentChenUpsilon6ProductForm ≠ 0 := by
  intro h
  have hh := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (fun _ => 1)) h
  norm_num [currentChenUpsilon6ProductForm] at hh

/-- A concrete product wall is null, at every buffer value as well as zero. -/
theorem currentChenUpsilon6_productWall_volume_zero (c : ℝ) :
    volume {x : Fin 2 → ℝ | x 0 + x 1 = c} = 0 := by
  simpa [currentChenUpsilon6ProductForm] using
    affinePrimeWall_volume_zero currentChenUpsilon6ProductForm
      currentChenUpsilon6ProductForm_ne_zero c

theorem currentChenUpsilon6_coordinateWall_volume_zero (i : Fin 2) (c : ℝ) :
    volume {x : Fin 2 → ℝ | x i = c} = 0 := by
  apply affinePrimeWall_volume_zero (ContinuousLinearMap.proj i) _ c
  intro h
  have hh := congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L (fun _ => 1)) h
  norm_num at hh

private theorem ae_currentChenUpsilon6_product_ne (c : ℝ) :
    ∀ᵐ x : Fin 2 → ℝ ∂volume, x 0 + x 1 ≠ c := by
  rw [ae_iff]
  simpa only [not_not] using currentChenUpsilon6_productWall_volume_zero c

private theorem ae_currentChenUpsilon6_coordinate_ne (i : Fin 2) (c : ℝ) :
    ∀ᵐ x : Fin 2 → ℝ ∂volume, x i ≠ c := by
  rw [ae_iff]
  simpa only [not_not] using currentChenUpsilon6_coordinateWall_volume_zero i c

/-- The product wall has zero reciprocal-coordinate mass in the actual box. -/
theorem integral_currentChenUpsilon6_productWall_eq_zero (c : ℝ) :
    (∫ x in currentChenUpsilon6LogRectangle ∩ {x | x 0 + x 1 = c},
      1 / (x 0 * x 1)) = 0 := by
  have hz : volume (currentChenUpsilon6LogRectangle ∩ {x | x 0 + x 1 = c}) = 0 :=
    measure_mono_null inter_subset_right (currentChenUpsilon6_productWall_volume_zero c)
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

/-- Each original endpoint wall also has zero reciprocal-coordinate mass. -/
theorem integral_currentChenUpsilon6_coordinateWall_eq_zero (i : Fin 2) (c : ℝ) :
    (∫ x in currentChenUpsilon6LogRectangle ∩ {x | x i = c},
      1 / (x 0 * x 1)) = 0 := by
  have hz : volume (currentChenUpsilon6LogRectangle ∩ {x | x i = c}) = 0 :=
    measure_mono_null inter_subset_right (currentChenUpsilon6_coordinateWall_volume_zero i c)
  rw [Measure.restrict_eq_zero.mpr hz, integral_zero_measure]

/-- Closing the two upper coordinate walls does not alter the integral. -/
theorem integral_currentChenUpsilon6_closedRectangle_eq :
    (∫ x : Fin 2 → ℝ in
      {x | (417 / 5000 : ℝ) ≤ x 0 ∧ x 0 ≤ 19 / 125 ∧
        (19 / 125 : ℝ) ≤ x 1 ∧ x 1 ≤ 59 / 250}, 1 / (x 0 * x 1)) =
    ∫ x in currentChenUpsilon6LogRectangle, 1 / (x 0 * x 1) := by
  apply setIntegral_congr_set
  filter_upwards [ae_currentChenUpsilon6_coordinate_ne 0 (19 / 125),
    ae_currentChenUpsilon6_coordinate_ne 1 (59 / 250)] with x hx hy
  apply propext
  change ((417 / 5000 : ℝ) ≤ x 0 ∧ x 0 ≤ 19 / 125 ∧
    (19 / 125 : ℝ) ≤ x 1 ∧ x 1 ≤ 59 / 250) ↔ x ∈ currentChenUpsilon6LogRectangle
  rw [mem_currentChenUpsilon6LogRectangle]
  constructor
  · rintro ⟨ha, hh, hh', hd⟩
    exact ⟨ha, (lt_or_eq_of_le hh).resolve_right hx,
      hh', (lt_or_eq_of_le hd).resolve_right hy⟩
  · rintro ⟨ha, hh, hh', hd⟩
    exact ⟨ha, hh.le, hh', hd.le⟩

/-- The exact buffered weak product gate and its strict version have the
same integral; the finite prime selector itself is not changed. -/
theorem integral_currentChenUpsilon6LogDomain_eq_strict (eta : ℝ) :
    (∫ x in currentChenUpsilon6LogDomain eta, 1 / (x 0 * x 1)) =
    ∫ x in currentChenUpsilon6LogRectangle ∩
      {x | x 0 + x 1 < (833 / 2500 : ℝ) - eta}, 1 / (x 0 * x 1) := by
  apply setIntegral_congr_set
  filter_upwards [ae_currentChenUpsilon6_product_ne ((833 / 2500 : ℝ) - eta)] with x hx
  apply propext
  change (x ∈ currentChenUpsilon6LogRectangle ∧ x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta) ↔
    (x ∈ currentChenUpsilon6LogRectangle ∧ x 0 + x 1 < (833 / 2500 : ℝ) - eta)
  exact and_congr_right (fun _ => ⟨fun h => (lt_or_eq_of_le h).resolve_right hx, le_of_lt⟩)

/-- A closed strip contains the entire loss from imposing the buffer. -/
def currentChenUpsilon6ProductBoundaryStrip (eta : ℝ) : Set (Fin 2 → ℝ) :=
  currentChenUpsilon6LogRectangle ∩
    {x | (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧ x 0 + x 1 ≤ 833 / 2500}

private theorem measurableSet_currentChenUpsilon6_stripGate (eta : ℝ) :
    MeasurableSet {x : Fin 2 → ℝ |
      (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧ x 0 + x 1 ≤ 833 / 2500} := by
  have hc : Continuous (fun x : Fin 2 → ℝ => x 0 + x 1) :=
    (continuous_apply 0).add (continuous_apply 1)
  exact (isClosed_le continuous_const hc).measurableSet.inter
    (isClosed_le hc continuous_const).measurableSet

theorem integrableOn_currentChenUpsilon6ProductBoundaryStrip (eta : ℝ) :
    IntegrableOn (fun x : Fin 2 → ℝ => 1 / (x 0 * x 1))
      (currentChenUpsilon6ProductBoundaryStrip eta) :=
  integrableOn_currentChenUpsilon6LogRectangle.mono_set inter_subset_left

theorem currentChenUpsilon6LogDomain_loss_subset_strip (eta : ℝ) :
    currentChenUpsilon6LogDomain 0 \ currentChenUpsilon6LogDomain eta ⊆
      currentChenUpsilon6ProductBoundaryStrip eta := by
  rintro x ⟨⟨hx, hx0⟩, hnot⟩
  have hgt : (833 / 2500 : ℝ) - eta < x 0 + x 1 := by
    by_contra h
    exact hnot ⟨hx, le_of_not_gt h⟩
  change x 0 + x 1 ≤ (833 / 2500 : ℝ) - 0 at hx0
  exact ⟨hx, hgt.le, by simpa only [sub_zero] using hx0⟩

/-- Dominated convergence on the concrete positive rectangle. The
integrable dominator is its actual reciprocal-coordinate density. This
two-sided eta limit in particular includes eta tending to zero positively. -/
theorem tendsto_integral_currentChenUpsilon6ProductBoundaryStrip :
    Tendsto (fun eta : ℝ =>
      ∫ x in currentChenUpsilon6ProductBoundaryStrip eta, 1 / (x 0 * x 1))
      (𝓝 0) (𝓝 0) := by
  unfold currentChenUpsilon6ProductBoundaryStrip
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict currentChenUpsilon6LogRectangle)
    (f := fun _ : Fin 2 → ℝ => (0 : ℝ))
    (F := fun eta : ℝ =>
      {x : Fin 2 → ℝ | (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧
        x 0 + x 1 ≤ 833 / 2500}.indicator (fun x => 1 / (x 0 * x 1)))
    (fun x : Fin 2 → ℝ => ‖1 / (x 0 * x 1)‖)
    (Eventually.of_forall (fun eta =>
      (integrableOn_currentChenUpsilon6LogRectangle.indicator
        (measurableSet_currentChenUpsilon6_stripGate eta)).aestronglyMeasurable))
    (Eventually.of_forall (fun eta => Eventually.of_forall (fun x =>
      norm_indicator_le_norm_self
        (s := {y : Fin 2 → ℝ | (833 / 2500 : ℝ) - eta ≤ y 0 + y 1 ∧
          y 0 + y 1 ≤ 833 / 2500})
        (fun y : Fin 2 → ℝ => 1 / (y 0 * y 1)) x)))
    integrableOn_currentChenUpsilon6LogRectangle.norm
    (show ∀ᵐ x : Fin 2 → ℝ ∂volume.restrict currentChenUpsilon6LogRectangle,
      Tendsto (fun eta : ℝ =>
        {x : Fin 2 → ℝ | (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧
          x 0 + x 1 ≤ 833 / 2500}.indicator (fun x => 1 / (x 0 * x 1)) x)
        (𝓝 0) (𝓝 0) from by
      filter_upwards [ae_restrict_of_ae (ae_currentChenUpsilon6_product_ne (833 / 2500))]
        with x hx
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · apply tendsto_const_nhds.congr'
        filter_upwards [Iio_mem_nhds (sub_pos.mpr hlt)] with eta heta
        change eta < (833 / 2500 : ℝ) - (x 0 + x 1) at heta
        have hn : x ∉ {x : Fin 2 → ℝ | (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧
            x 0 + x 1 ≤ 833 / 2500} := by
          intro hg
          change (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧ x 0 + x 1 ≤ 833 / 2500 at hg
          linarith [hg.1]
        simp only [indicator_of_notMem hn]
      · apply tendsto_const_nhds.congr'
        exact Eventually.of_forall (fun eta => by
          have hn : x ∉ {x : Fin 2 → ℝ | (833 / 2500 : ℝ) - eta ≤ x 0 + x 1 ∧
              x 0 + x 1 ≤ 833 / 2500} := fun hg => (not_le.mpr hgt) hg.2
          simp only [indicator_of_notMem hn]))
  simpa only [setIntegral_indicator (measurableSet_currentChenUpsilon6_stripGate _),
    integral_zero] using hlim

end

end ImbalancedChen
