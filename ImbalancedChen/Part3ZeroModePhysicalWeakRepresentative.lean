import ImbalancedChen.Part3ZeroModeWeakHalfLineTrace

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Physical zero-mode weak data use literal dy/y^2 value mass and ordinary dy
gradient energy. On every finite prefix with Y>0, the weighted value norm
controls the ordinary local L2 norm. Thus the genuine weak-domain theorem
constructs an actual locally absolutely continuous physical representative
and lower trace. Its literal weighted mass and ordinary derivative energy
are proved equal to the original weak data. No Hardy inequality or smooth
graph closure is used or asserted.
-/

namespace ImbalancedChen.Part3.ZeroModePhysicalWeakRepresentative20261026b
noncomputable section
open MeasureTheory Set Filter
open ZeroModeWeakHalfLineTrace20261026b

/-- On (Y,b), positive physical height bounds the inverse-square weight
from below. This is a proved local L2 bridge from actual physical mass. -/
theorem local_memLp_of_physical_mass {Y b : ℝ} (hY : 0 < Y) (hb : Y < b)
    {f : ℝ → ℂ} (hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi Y)))
    (hfmass : IntegrableOn (fun y => ‖f y‖ ^ 2 / y ^ 2) (Ioi Y)) :
    MemLp f 2 (volume.restrict (Ioo Y b)) := by
  have hmu : volume.restrict (Ioo Y b) ≤ volume.restrict (Ioi Y) :=
    Measure.restrict_mono_set volume Ioo_subset_Ioi_self
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioo Y b)) :=
    hfmeas.mono_measure hmu
  have hbound : IntegrableOn (fun y => b ^ 2 * (‖f y‖ ^ 2 / y ^ 2)) (Ioo Y b) :=
    (hfmass.mono_set Ioo_subset_Ioi_self).const_mul _
  have hi : IntegrableOn (fun y => ‖f y‖ ^ 2) (Ioo Y b) := by
    apply hbound.mono' (hmeas.norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    have hypos : 0 < y := hY.trans hy.1
    have hbpos : 0 < b := hY.trans hb
    have hs : y ^ 2 ≤ b ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy.2.le)
        (add_nonneg hbpos.le hypos.le)]
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f y‖)]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos hypos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg ‖f y‖)]
  exact (memLp_two_iff_integrable_sq_norm hmeas).mpr hi

/-- Genuine physical weak data, with inverse-square value mass and ordinary
gradient L2, have a regular physical representative reaching the lower height. -/
theorem nonempty_physicalWeakTailRepresentative {Y : ℝ} (hY : 0 < Y)
    {f g : ℝ → ℂ} (hfmeas : AEStronglyMeasurable f (volume.restrict (Ioi Y)))
    (hfmass : IntegrableOn (fun y => ‖f y‖ ^ 2 / y ^ 2) (Ioi Y))
    (hg : MemLp g 2 (volume.restrict (Ioi Y)))
    (hweak : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Ioi Y →
      (∫ y, deriv ψ y • f y) = -(∫ y, ψ y • g y)) :
    Nonempty (HalfLineSobolevRepresentative Y f g) := by
  apply nonempty_halfLineSobolevRepresentative
    (fun b hb => ⟨local_memLp_of_physical_mass hY hb hfmeas hfmass,
      MemLp.mono_measure (Measure.restrict_mono_set volume Ioo_subset_Ioi_self) hg⟩)
    hweak

/-- The representative has the literal original physical mass, with no
formal-norm identification assumed as an input. -/
theorem physical_representative_mass {Y : ℝ} {f g : ℝ → ℂ}
    (u : HalfLineSobolevRepresentative Y f g) :
    (∫ y in Ioi Y, ‖u.function y‖ ^ 2 / y ^ 2) =
      ∫ y in Ioi Y, ‖f y‖ ^ 2 / y ^ 2 := by
  apply integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [u.value_ae] with y hy hym
  rw [hy hym]

/-- The ordinary derivative of the actual representative is the given weak
gradient a.e., so its dy-energy is the original ordinary gradient energy. -/
theorem physical_representative_energy {Y : ℝ} {f g : ℝ → ℂ}
    (u : HalfLineSobolevRepresentative Y f g) :
    (∫ y in Ioi Y, ‖deriv u.function y‖ ^ 2) =
      ∫ y in Ioi Y, ‖g y‖ ^ 2 := by
  apply integral_congr_ae
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [u.derivative_ae] with y hy hym
  rw [(hy hym).deriv]

theorem physical_representative_mass_integrable {Y : ℝ} {f g : ℝ → ℂ}
    (u : HalfLineSobolevRepresentative Y f g)
    (hfmass : IntegrableOn (fun y => ‖f y‖ ^ 2 / y ^ 2) (Ioi Y)) :
    IntegrableOn (fun y => ‖u.function y‖ ^ 2 / y ^ 2) (Ioi Y) := by
  apply hfmass.congr
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [u.value_ae] with y hy hym
  rw [hy hym]

theorem physical_representative_energy_integrable {Y : ℝ} {f g : ℝ → ℂ}
    (u : HalfLineSobolevRepresentative Y f g)
    (hg : MemLp g 2 (volume.restrict (Ioi Y))) :
    IntegrableOn (fun y => ‖deriv u.function y‖ ^ 2) (Ioi Y) := by
  have hi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  apply hi.congr
  rw [ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [u.derivative_ae] with y hy hym
  rw [(hy hym).deriv]

end
end ImbalancedChen.Part3.ZeroModePhysicalWeakRepresentative20261026b
