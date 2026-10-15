import ImbalancedChen.CurrentChenUpsilon6LogDomain
import Mathlib.Tactic.FinCases

/-!
# Removing a product buffer from the actual ordinary sixth-row kernel

The finite product-buffer license and the unweighted boundary mass are already
proved. Here the integrand is the ordinary lower-sieve first-interval kernel
on the literal current sixth rectangle. Its profile stays strictly above one
on the whole closed rectangle; on the corrected product domain it is at least
two. Compact integrability and dominated convergence therefore pay the actual
kernel loss as eta tends to zero. This does not supply the stronger h248 kernel,
the arithmetic mean, or the manuscript's adopted sixth-row numerical constant.
-/

namespace ImbalancedChen

noncomputable section

open scoped Classical BigOperators Topology
open MeasureTheory Filter Set

def currentChenUpsilon6OrdinaryProfile (x : Fin 2 → ℝ) : ℝ :=
  ((1 / 2 : ℝ) - x 0 - x 1) / (417 / 5000)

/-- The profile factor times the original reciprocal-coordinate density. -/
def currentChenUpsilon6OrdinaryKernel (x : Fin 2 → ℝ) : ℝ :=
  (4 * Real.log (currentChenUpsilon6OrdinaryProfile x - 1) /
    (currentChenUpsilon6OrdinaryProfile x * (417 / 5000))) * (1 / (x 0 * x 1))

private def sixthClosedRectangle : Set (Fin 2 → ℝ) :=
  Set.univ.pi (fun i => Set.Icc
    (![(417 / 5000 : ℝ), 19 / 125] i) (![(19 / 125 : ℝ), 59 / 250] i))

private theorem sixthClosedRectangle_profile_bounds {x : Fin 2 → ℝ}
    (hx : x ∈ sixthClosedRectangle) :
    (560 / 417 : ℝ) ≤ currentChenUpsilon6OrdinaryProfile x ∧
      currentChenUpsilon6OrdinaryProfile x ≤ 1323 / 417 := by
  have hx0 := hx 0 (Set.mem_univ _)
  have hx1 := hx 1 (Set.mem_univ _)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx0 hx1
  unfold currentChenUpsilon6OrdinaryProfile
  constructor <;> norm_num <;> linarith [hx0.1, hx0.2, hx1.1, hx1.2]

private theorem sixthClosedRectangle_coordinates_pos {x : Fin 2 → ℝ}
    (hx : x ∈ sixthClosedRectangle) : 0 < x 0 ∧ 0 < x 1 := by
  have hx0 := (hx 0 (Set.mem_univ _)).1
  have hx1 := (hx 1 (Set.mem_univ _)).1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx0 hx1
  constructor <;> linarith

private theorem sixthRectangle_subset_closed :
    currentChenUpsilon6LogRectangle ⊆ sixthClosedRectangle := by
  intro x hx i _
  obtain ⟨ha, hh, hh', hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
  fin_cases i
  · exact ⟨ha, hh.le⟩
  · exact ⟨hh', hd.le⟩

/-- The corrected sixth-row product gate is exactly the lower-factor
first-interval threshold, with the same fixed buffer. -/
theorem currentChenUpsilon6OrdinaryProfile_buffer_lower {eta : ℝ}
    {x : Fin 2 → ℝ} (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    2 + eta / (417 / 5000 : ℝ) ≤ currentChenUpsilon6OrdinaryProfile x := by
  have hg : x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta := hx.2
  unfold currentChenUpsilon6OrdinaryProfile
  norm_num
  linarith

theorem currentChenUpsilon6OrdinaryProfile_mem_firstInterval {eta : ℝ}
    (heta : 0 ≤ eta) {x : Fin 2 → ℝ}
    (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    currentChenUpsilon6OrdinaryProfile x ∈ Set.Icc (2 : ℝ) 4 := by
  have hlo := currentChenUpsilon6OrdinaryProfile_buffer_lower hx
  have hhi := (sixthClosedRectangle_profile_bounds (sixthRectangle_subset_closed hx.1)).2
  have heta' : 0 ≤ eta / (417 / 5000 : ℝ) := div_nonneg heta (by norm_num)
  constructor
  · linarith
  · exact hhi.trans (by norm_num)

private theorem continuousOn_sixthOrdinaryKernel :
    ContinuousOn currentChenUpsilon6OrdinaryKernel sixthClosedRectangle := by
  have hp : Continuous currentChenUpsilon6OrdinaryProfile := by
    unfold currentChenUpsilon6OrdinaryProfile
    fun_prop
  have hprof : ∀ x ∈ sixthClosedRectangle, 1 < currentChenUpsilon6OrdinaryProfile x := by
    intro x hx
    have h := (sixthClosedRectangle_profile_bounds hx).1
    linarith
  have hd : ContinuousOn (fun x : Fin 2 → ℝ => 1 / (x 0 * x 1)) sixthClosedRectangle := by
    apply continuousOn_const.div
      ((continuous_apply 0).continuousOn.mul (continuous_apply 1).continuousOn)
    intro x hx
    obtain ⟨h0, h1⟩ := sixthClosedRectangle_coordinates_pos hx
    exact mul_ne_zero h0.ne' h1.ne'
  unfold currentChenUpsilon6OrdinaryKernel
  apply ContinuousOn.mul _ hd
  apply (continuousOn_const.mul
    ((hp.continuousOn.sub continuousOn_const).log ?_)).div
    (hp.continuousOn.mul continuousOn_const) ?_
  · intro x hx
    exact (sub_pos.mpr (hprof x hx)).ne'
  · intro x hx
    exact mul_ne_zero (zero_lt_one.trans (hprof x hx)).ne' (by norm_num)

/-- Integrability is paid on the actual positive rectangle, including
points outside the corrected positive-gain subdomain. -/
theorem integrableOn_currentChenUpsilon6OrdinaryKernel :
    IntegrableOn currentChenUpsilon6OrdinaryKernel currentChenUpsilon6LogRectangle := by
  have hcompact : IsCompact sixthClosedRectangle :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  exact (continuousOn_sixthOrdinaryKernel.integrableOn_compact hcompact).mono_set
    sixthRectangle_subset_closed

theorem integrableOn_currentChenUpsilon6OrdinaryKernel_domain (eta : ℝ) :
    IntegrableOn currentChenUpsilon6OrdinaryKernel (currentChenUpsilon6LogDomain eta) :=
  integrableOn_currentChenUpsilon6OrdinaryKernel.mono_set inter_subset_left

theorem currentChenUpsilon6OrdinaryKernel_nonneg {eta : ℝ} (heta : 0 ≤ eta)
    {x : Fin 2 → ℝ} (hx : x ∈ currentChenUpsilon6LogDomain eta) :
    0 ≤ currentChenUpsilon6OrdinaryKernel x := by
  have hp := (currentChenUpsilon6OrdinaryProfile_mem_firstInterval heta hx).1
  have hl : 0 ≤ Real.log (currentChenUpsilon6OrdinaryProfile x - 1) :=
    Real.log_nonneg (by linarith)
  obtain ⟨h0, h1⟩ := currentChenUpsilon6LogRectangle_coordinates_pos hx.1
  unfold currentChenUpsilon6OrdinaryKernel
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hl)
      (mul_nonneg (by linarith) (by norm_num)))
    (div_nonneg zero_le_one (mul_nonneg h0.le h1.le))

private theorem measurableSet_sixthProductGate (eta : ℝ) :
    MeasurableSet {x : Fin 2 → ℝ | x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta} := by
  exact (isClosed_le ((continuous_apply 0).add (continuous_apply 1))
    continuous_const).measurableSet

/-- Actual kernel convergence, with no numeric mass substituted for the
kernel and no exchange with the arithmetic N-limit. -/
theorem tendsto_integral_currentChenUpsilon6OrdinaryKernel_buffer :
    Tendsto (fun eta : ℝ => ∫ x in currentChenUpsilon6LogDomain eta,
      currentChenUpsilon6OrdinaryKernel x) (𝓝 0)
      (𝓝 (∫ x in currentChenUpsilon6LogDomain 0,
        currentChenUpsilon6OrdinaryKernel x)) := by
  let gate (eta : ℝ) := {x : Fin 2 → ℝ | x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta}
  have hw : ∀ᵐ x : Fin 2 → ℝ ∂volume, x 0 + x 1 ≠ (833 / 2500 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using currentChenUpsilon6_productWall_volume_zero (833 / 2500)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict currentChenUpsilon6LogRectangle)
    (f := (gate 0).indicator currentChenUpsilon6OrdinaryKernel)
    (F := fun eta : ℝ => (gate eta).indicator currentChenUpsilon6OrdinaryKernel)
    (fun x : Fin 2 → ℝ => ‖currentChenUpsilon6OrdinaryKernel x‖)
    (Eventually.of_forall (fun eta =>
      (integrableOn_currentChenUpsilon6OrdinaryKernel.indicator
        (measurableSet_sixthProductGate eta)).aestronglyMeasurable))
    (Eventually.of_forall (fun eta => Eventually.of_forall (fun x =>
      norm_indicator_le_norm_self (s := gate eta) currentChenUpsilon6OrdinaryKernel x)))
    integrableOn_currentChenUpsilon6OrdinaryKernel.norm
    (show ∀ᵐ x : Fin 2 → ℝ ∂volume.restrict currentChenUpsilon6LogRectangle,
      Tendsto (fun eta : ℝ => (gate eta).indicator currentChenUpsilon6OrdinaryKernel x)
        (𝓝 0) (𝓝 ((gate 0).indicator currentChenUpsilon6OrdinaryKernel x)) from by
      filter_upwards [ae_restrict_of_ae hw] with x hx
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · have hx0 : x ∈ gate 0 := by dsimp [gate]; simpa only [sub_zero] using hlt.le
        rw [Set.indicator_of_mem hx0]
        apply tendsto_const_nhds.congr'
        filter_upwards [Iio_mem_nhds (sub_pos.mpr hlt)] with eta heta
        change eta < (833 / 2500 : ℝ) - (x 0 + x 1) at heta
        have hxeta : x ∈ gate eta := by dsimp [gate]; linarith
        simp only [Set.indicator_of_mem hxeta]
      · have hx0 : x ∉ gate 0 := by
          dsimp [gate]
          simpa only [sub_zero] using not_le.mpr hgt
        rw [Set.indicator_of_notMem hx0]
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_nhds (sub_neg.mpr hgt)] with eta heta
        change (833 / 2500 : ℝ) - (x 0 + x 1) < eta at heta
        have hxeta : x ∉ gate eta := by
          dsimp [gate]
          intro hh
          linarith
        simp only [Set.indicator_of_notMem hxeta])
  simpa only [gate, currentChenUpsilon6LogDomain, setIntegral_indicator
    (measurableSet_sixthProductGate _)] using hlim

end

end ImbalancedChen
