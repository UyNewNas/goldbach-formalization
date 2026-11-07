import ImbalancedChen.Certificates.PairedV2FullMaskGeometry
import ImbalancedChen.CurrentChenBuchstabRefinement

/-!
The proved global lower barrier for the pinned, actual Buchstab function
applies to every adopted fibre.  The pointwise extra-gain comparison uses
`K / 80 = (K / 4) * (1 / 20)` exactly once.  Arithmetic parent licensing
and the mean-value passage to this analytic kernel are separate obligations.
-/

namespace ImbalancedChen.Certificates.PairedV2.FullMask

set_option Elab.async false

theorem row_fibre_buchstab_eleven_twentieths (r : Row) {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w) :
    (11 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) := by
  exact ImbalancedChen.currentChen_buchstab_eleven_twentieths
    (row_fibre_argument r hs).2.2.2.2.2.2

theorem row_fibre_buchstab_gain (r : Row) {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w) :
    (1 : ℝ) / 20 ≤
      LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2 := by
  have hb := row_fibre_buchstab_eleven_twentieths r hs
  linarith

/-- Literal comparison with the full extra Buchstab gain on each actual
fibre.  The certified integral therefore retains its original normalization. -/
theorem row_fibre_buchstab_extra_kernel (r : Row) {t u z w : ℝ}
    (hs : openFibreSupport (indices r).1 (indices r).2 (cutoff r) t u z w) :
    ((K : ℝ) / 80) * pairedFibreKernel t u z w ≤
      ((K : ℝ) / 4) *
        (LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2) *
        pairedFibreKernel t u z w := by
  obtain ⟨haw, hwz, hzu, _, hht, _, _⟩ := row_fibre_argument r hs
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  have hh : (0 : ℝ) < (h : ℝ) := by norm_num [h]
  have hw : 0 < w := ha.trans haw
  have hz : 0 < z := hw.trans hwz
  have hu : 0 < u := hz.trans hzu
  have ht : 0 < t := hh.trans hht
  have hkernel : 0 ≤ pairedFibreKernel t u z w := by
    unfold pairedFibreKernel
    positivity
  have hK : (0 : ℝ) ≤ (K : ℝ) / 4 := by norm_num [K]
  have hb := mul_le_mul_of_nonneg_left (row_fibre_buchstab_gain r hs) hK
  have hb' : (K : ℝ) / 80 ≤ (K : ℝ) / 4 *
      (LiLiuPrereqBuchstab.buchstab ((1 - t - u - z - w) / z) - (1 : ℝ) / 2) := by
    calc
      (K : ℝ) / 80 = ((K : ℝ) / 4) * (1 / 20) := by ring
      _ ≤ _ := hb
  exact mul_le_mul_of_nonneg_right hb' hkernel

end ImbalancedChen.Certificates.PairedV2.FullMask
