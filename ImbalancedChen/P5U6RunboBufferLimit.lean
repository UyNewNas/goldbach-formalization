import ImbalancedChen.CurrentChenUpsilon6LogDomain
import Mathlib.Tactic.FinCases

/-!
SOURCE_ONLY / UNCOMPILED. Buffer removal for every fixed integrable kernel
on the literal corrected Runbo U6 domain. This generalizes the actual ordinary
kernel DCT, without asserting that an h248 kernel has already been supplied.
The dominator is the norm of the actual integrable kernel, not a postulated
boundary-tail estimate. The affine product wall has proved zero volume.
Arithmetic prime selectors are not modified by this analytic null-wall step.
-/

namespace ImbalancedChen.P5U6RunboBufferLimitSourceOnly

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

abbrev Point := Fin 2 → ℝ

private theorem measurableSet_productGate (eta : ℝ) :
    MeasurableSet {x : Point | x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta} := by
  exact (isClosed_le ((continuous_apply 0).add (continuous_apply 1))
    continuous_const).measurableSet

/-- General fixed-kernel buffer removal on the original corrected product
domain. Integrability is the only kernel premise; no nonnegativity, continuity,
uniform boundary estimate or arithmetic limiting assertion is assumed. -/
theorem tendsto_integral_productDomain (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) :
    Tendsto (fun eta : ℝ => ∫ x in currentChenUpsilon6LogDomain eta, f x)
      (𝓝 0) (𝓝 (∫ x in currentChenUpsilon6LogDomain 0, f x)) := by
  let gate (eta : ℝ) := {x : Point | x 0 + x 1 ≤ (833 / 2500 : ℝ) - eta}
  have hw : ∀ᵐ x : Point ∂volume, x 0 + x 1 ≠ (833 / 2500 : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using currentChenUpsilon6_productWall_volume_zero (833 / 2500)
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict currentChenUpsilon6LogRectangle)
    (f := (gate 0).indicator f)
    (F := fun eta : ℝ => (gate eta).indicator f)
    (fun x : Point => ‖f x‖)
    (Eventually.of_forall (fun eta =>
      (hf.indicator (measurableSet_productGate eta)).aestronglyMeasurable))
    (Eventually.of_forall (fun eta => Eventually.of_forall (fun x =>
      norm_indicator_le_norm_self (s := gate eta) f x)))
    hf.norm
    (show ∀ᵐ x : Point ∂volume.restrict currentChenUpsilon6LogRectangle,
      Tendsto (fun eta : ℝ => (gate eta).indicator f x)
        (𝓝 0) (𝓝 ((gate 0).indicator f x)) from by
      filter_upwards [ae_restrict_of_ae hw] with x hx
      rcases lt_or_gt_of_ne hx with hlt | hgt
      · have hx0 : x ∈ gate 0 := by
          dsimp [gate]
          simpa only [sub_zero] using hlt.le
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
  simpa only [gate, currentChenUpsilon6LogDomain,
    setIntegral_indicator (measurableSet_productGate _)] using hlim

/-- The exact signed loss tends to zero; this is proved from actual DCT. -/
theorem tendsto_buffer_loss (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) :
    Tendsto (fun eta : ℝ =>
      (∫ x in currentChenUpsilon6LogDomain 0, f x) -
        (∫ x in currentChenUpsilon6LogDomain eta, f x))
      (𝓝 0) (𝓝 0) := by
  have hc : Tendsto (fun _eta : ℝ => ∫ x in currentChenUpsilon6LogDomain 0, f x)
      (𝓝 0) (𝓝 (∫ x in currentChenUpsilon6LogDomain 0, f x)) :=
    tendsto_const_nhds
  simpa only [sub_self] using
    (hc.sub (tendsto_integral_productDomain f hf))

/-- The required eta-down-to-zero filter is a restriction of the stronger
two-sided analytic limit; the arithmetic N-limit has not been exchanged. -/
theorem tendsto_buffer_loss_right (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) :
    Tendsto (fun eta : ℝ =>
      (∫ x in currentChenUpsilon6LogDomain 0, f x) -
        (∫ x in currentChenUpsilon6LogDomain eta, f x))
      (𝓝[>] 0) (𝓝 0) :=
  (tendsto_buffer_loss f hf).mono_left nhdsWithin_le_nhds

/-- Absolute integral loss also tends to zero, without requiring f >= 0. -/
theorem tendsto_abs_buffer_loss_right (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle) :
    Tendsto (fun eta : ℝ => |(∫ x in currentChenUpsilon6LogDomain 0, f x) -
        (∫ x in currentChenUpsilon6LogDomain eta, f x)|)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [abs_zero] using (tendsto_buffer_loss_right f hf).abs

/-- Pick one strictly positive buffer after epsilon and before any future
arithmetic threshold. This is the exact quantifier order used by the mean. -/
theorem exists_positive_buffer (f : Point → ℝ)
    (hf : IntegrableOn f currentChenUpsilon6LogRectangle)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ eta : ℝ, 0 < eta ∧
      (∫ x in currentChenUpsilon6LogDomain 0, f x) - epsilon <
        (∫ x in currentChenUpsilon6LogDomain eta, f x) := by
  have hlimit : Tendsto (fun eta : ℝ =>
      ∫ x in currentChenUpsilon6LogDomain eta, f x) (𝓝[>] 0)
        (𝓝 (∫ x in currentChenUpsilon6LogDomain 0, f x)) :=
    (tendsto_integral_productDomain f hf).mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ eta : ℝ in 𝓝[>] (0 : ℝ), 0 < eta ∧
      (∫ x in currentChenUpsilon6LogDomain 0, f x) - epsilon <
        (∫ x in currentChenUpsilon6LogDomain eta, f x) := by
    filter_upwards [self_mem_nhdsWithin,
      hlimit.eventually (Ioi_mem_nhds
        (by linarith : (∫ x in currentChenUpsilon6LogDomain 0, f x) - epsilon <
          (∫ x in currentChenUpsilon6LogDomain 0, f x)))] with eta heta hI
    exact ⟨heta, hI⟩
  exact hnear.exists

/-- Concrete reciprocal mass has no remaining integrability premise. -/
theorem tendsto_reciprocal_mass_loss_right :
    Tendsto (fun eta : ℝ =>
      (∫ x in currentChenUpsilon6LogDomain 0, 1 / (x 0 * x 1)) -
        (∫ x in currentChenUpsilon6LogDomain eta, 1 / (x 0 * x 1)))
      (𝓝[>] 0) (𝓝 0) :=
  tendsto_buffer_loss_right (fun x : Point => 1 / (x 0 * x 1))
    integrableOn_currentChenUpsilon6LogRectangle

/-- Continuous kernels need no independent integrability supplier: compactness
of the literal closed rectangle pays it before applying the general result. -/
theorem tendsto_continuous_buffer_loss_right (f : Point → ℝ)
    (hf : Continuous f) :
    Tendsto (fun eta : ℝ =>
      (∫ x in currentChenUpsilon6LogDomain 0, f x) -
        (∫ x in currentChenUpsilon6LogDomain eta, f x))
      (𝓝[>] 0) (𝓝 0) := by
  let C : Set Point := Set.univ.pi (fun i => Set.Icc
    (![(417 / 5000 : ℝ), 19 / 125] i) (![(19 / 125 : ℝ), 59 / 250] i))
  have hC : IsCompact C := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : currentChenUpsilon6LogRectangle ⊆ C := by
    intro x hx i _
    obtain ⟨ha, hh, hh', hd⟩ := mem_currentChenUpsilon6LogRectangle.mp hx
    fin_cases i
    · exact ⟨ha, hh.le⟩
    · exact ⟨hh', hd.le⟩
  exact tendsto_buffer_loss_right f
    ((hf.continuousOn.integrableOn_compact hC).mono_set hsub)

end

end ImbalancedChen.P5U6RunboBufferLimitSourceOnly
