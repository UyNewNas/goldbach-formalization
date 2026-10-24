import ImbalancedChen.P2PairedFibreBuchstabVariableLower
import ImbalancedChen.Certificates.PairedV2FullCertificate

/-!
# P2: actual integrated Buchstab gain and the frozen numerical lower bound

SOURCE ONLY, uncompiled.  Future source installation maps the two companion
candidates to `ImbalancedChen/P2HistoricalFibreBinding.lean` and
`ImbalancedChen/P2PairedFibreBuchstabVariableLower.lean`.  Neither draft is
treated as an installed or compiled supplier by this source-only delivery.

The final lower bound below actually composes the existing full certificate
theorem with the unconditional integrated actual-Buchstab comparison.  It
has no gain premise.  The upper endpoint for the constant-gain certificate
is not asserted to bound the larger semantic Buchstab gain.

The old and new fourfold integrals use exactly the same `K/4` weight, mask,
row coordinates, triangular inner fibre and interval endpoints.  Genuine
integral subtraction gives their difference as the actual semantic gain.
Continuity of a cutoff-clamped extension supplies integrability at every
nested integration level; the extension equals the literal kernels on the
entire closed integration support.

Still missing: P5 injection of these fibres into the retained arithmetic
parent, and the historical-domain/five-to-four-coordinate identification.
The analytic result here supplies neither of those arithmetic statements.
-/

namespace ImbalancedChen.Certificates.P2PairedSemanticGainEnclosure

noncomputable section

open MeasureTheory Set
open scoped Interval BigOperators
open PairedV2 PairedV2.FullMask
open P2HistoricalFibreBinding
open P2PairedFibreBuchstabVariableLower


private theorem continuous_w (F : Quad → ℝ) (hF : Continuous F) (a : ℝ) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => ∫ w in a..p.2, F (p, w)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p w => F (p, w)) hF continuous_snd

private theorem continuous_zw (F : Quad → ℝ) (hF : Continuous F) (a Z : ℝ) :
    Continuous (fun p : ℝ × ℝ => ∫ z in a..Z, ∫ w in a..z, F ((p, z), w)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun p z => ∫ w in a..z, F ((p, z), w)) (continuous_w F hF a) a Z

private theorem continuous_uzw (F : Quad → ℝ) (hF : Continuous F)
    (a ul ur Z : ℝ) :
    Continuous (fun t : ℝ => ∫ u in ul..ur, ∫ z in a..Z,
      ∫ w in a..z, F (((t, u), z), w)) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun t u => ∫ z in a..Z, ∫ w in a..z, F (((t, u), z), w))
    (continuous_zw F hF a Z) ul ur

/-- Genuine fourfold subtraction, with successive integrability proved
from global continuity and the true variable inner integration endpoint. -/
theorem fourfold_sub {F G : Quad → ℝ} (hF : Continuous F) (hG : Continuous G)
    (a tl tr ul ur Z : ℝ) :
    fourfold (fun p => F p - G p) a tl tr ul ur Z =
      fourfold F a tl tr ul ur Z - fourfold G a tl tr ul ur Z := by
  have hw (t u z : ℝ) :
      (∫ w in a..z, F (((t, u), z), w) - G (((t, u), z), w)) =
        (∫ w in a..z, F (((t, u), z), w)) -
          (∫ w in a..z, G (((t, u), z), w)) :=
    intervalIntegral.integral_sub
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a z)
      ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a z)
  have hz (t u : ℝ) :
      (∫ z in a..Z, (∫ w in a..z, F (((t, u), z), w)) -
        (∫ w in a..z, G (((t, u), z), w))) =
        (∫ z in a..Z, ∫ w in a..z, F (((t, u), z), w)) -
          (∫ z in a..Z, ∫ w in a..z, G (((t, u), z), w)) :=
    intervalIntegral.integral_sub
      (((continuous_w F hF a).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable a Z)
      (((continuous_w G hG a).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable a Z)
  have hu (t : ℝ) :
      (∫ u in ul..ur, (∫ z in a..Z, ∫ w in a..z, F (((t, u), z), w)) -
        (∫ z in a..Z, ∫ w in a..z, G (((t, u), z), w))) =
        (∫ u in ul..ur, ∫ z in a..Z, ∫ w in a..z, F (((t, u), z), w)) -
          (∫ u in ul..ur, ∫ z in a..Z, ∫ w in a..z, G (((t, u), z), w)) :=
    intervalIntegral.integral_sub
      (((continuous_zw F hF a Z).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable ul ur)
      (((continuous_zw G hG a Z).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable ul ur)
  unfold fourfold
  simp_rw [hw, hz, hu]
  exact intervalIntegral.integral_sub
    ((continuous_uzw F hF a ul ur Z).intervalIntegrable tl tr)
    ((continuous_uzw G hG a ul ur Z).intervalIntegrable tl tr)

/-- Literal adopted row functional, retaining all original endpoints. -/
def rowIntegral (r : Row) (F : Quad → ℝ) : ℝ :=
  fourfold F (a : ℝ) (tLower (indices r).1) (tUpper (indices r).1)
    (uLower (indices r).2) (uUpper (indices r).2) (cutoff r)

/-- Pointwise equality on the complete closed support gives equality of
the literal fourfold integrals, without any extension-domain assertion. -/
theorem rowIntegral_congr_on_closed (r : Row) {F G : Quad → ℝ}
    (hFG : ∀ t u z w : ℝ, P2PairedFibreBuchstabVariableLower.FullMask.closedSupport r t u z w →
      F (((t, u), z), w) = G (((t, u), z), w)) :
    rowIntegral r F = rowIntegral r G := by
  have he := row_endpoint_bounds r
  have htt : (tLower (indices r).1 : ℝ) ≤ (tUpper (indices r).1 : ℝ) := by
    exact_mod_cast he.2.2.2.2.2.1.le
  have huu : (uLower (indices r).2 : ℝ) ≤ (uUpper (indices r).2 : ℝ) := by
    exact_mod_cast he.2.2.1.le
  have hZZ : (a : ℝ) ≤ (cutoff r : ℝ) := by exact_mod_cast he.1.le
  unfold rowIntegral fourfold
  apply intervalIntegral.integral_congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro z hz
  apply intervalIntegral.integral_congr
  intro w hw
  rw [uIcc_of_le htt] at ht
  rw [uIcc_of_le huu] at hu
  rw [uIcc_of_le hZZ] at hz
  rw [uIcc_of_le hz.1] at hw
  exact hFG t u z w ⟨ht, hu, hz, hw⟩

/-- The shared original Chen-quarter weight, without a Buchstab factor. -/
def quarterWeight (p : Quad) : ℝ :=
  pairedChenQuarterWeight (K : ℝ) p.1.1.1 p.1.1.2 p.1.2 p.2

/-- The actual pinned Buchstab value at the paired residual argument. -/
def buchstabValue (p : Quad) : ℝ :=
  LiLiuPrereqBuchstab.buchstab ((1 - p.1.1.1 - p.1.1.2 - p.1.2 - p.2) / p.1.2)

def rowBuchstabIntegral (r : Row) : ℝ :=
  rowIntegral r (fun p => quarterWeight p * buchstabValue p)

def rowHalfBaselineIntegral (r : Row) : ℝ :=
  rowIntegral r (fun p => quarterWeight p * (1 / 2))

private def clamp (x : ℝ) : ℝ := max (a : ℝ) x

private def clampQuad (p : Quad) : Quad :=
  (((clamp p.1.1.1, clamp p.1.1.2), clamp p.1.2), clamp p.2)

private theorem clampQuad_eq (r : Row) {t u z w : ℝ}
    (hs : P2PairedFibreBuchstabVariableLower.FullMask.closedSupport r t u z w) :
    clampQuad (((t, u), z), w) = (((t, u), z), w) := by
  obtain ⟨ht, hu, hz, hw⟩ := P2PairedFibreBuchstabVariableLower.FullMask.closedSupport_lower_bounds r hs
  simp only [clampQuad, clamp, max_eq_right ht, max_eq_right hu,
    max_eq_right hz, max_eq_right hw]

private theorem rowIntegral_clamp_eq (r : Row) (F : Quad → ℝ) :
    rowIntegral r (fun p => F (clampQuad p)) = rowIntegral r F := by
  apply rowIntegral_congr_on_closed r
  intro t u z w hs
  rw [clampQuad_eq r hs]

private theorem clamp_ne_zero (x : ℝ) : clamp x ≠ 0 := by
  have ha : (0 : ℝ) < (a : ℝ) := by norm_num [a]
  exact (ha.trans_le (le_max_left (a : ℝ) x)).ne'

private theorem continuous_clamp : Continuous clamp := continuous_const.max continuous_id

private theorem continuous_clampedWeight : Continuous (fun p : Quad => quarterWeight (clampQuad p)) := by
  have ht : Continuous (fun p : Quad => clamp p.1.1.1) := continuous_clamp.comp (by fun_prop)
  have hu : Continuous (fun p : Quad => clamp p.1.1.2) := continuous_clamp.comp (by fun_prop)
  have hz : Continuous (fun p : Quad => clamp p.1.2) := continuous_clamp.comp (by fun_prop)
  have hw : Continuous (fun p : Quad => clamp p.2) := continuous_clamp.comp (by fun_prop)
  exact continuous_const.div (((ht.mul hu).mul (hz.pow 2)).mul hw)
    (fun p => mul_ne_zero (mul_ne_zero (mul_ne_zero (clamp_ne_zero _) (clamp_ne_zero _))
      (pow_ne_zero 2 (clamp_ne_zero _))) (clamp_ne_zero _))

private theorem continuous_clampedBuchstab : Continuous (fun p : Quad => buchstabValue (clampQuad p)) := by
  have ht : Continuous (fun p : Quad => clamp p.1.1.1) := continuous_clamp.comp (by fun_prop)
  have hu : Continuous (fun p : Quad => clamp p.1.1.2) := continuous_clamp.comp (by fun_prop)
  have hz : Continuous (fun p : Quad => clamp p.1.2) := continuous_clamp.comp (by fun_prop)
  have hw : Continuous (fun p : Quad => clamp p.2) := continuous_clamp.comp (by fun_prop)
  exact LiLiuPrereqBuchstab.continuous_buchstab.comp
    (((((continuous_const.sub ht).sub hu).sub hz).sub hw).div hz
      (fun p => clamp_ne_zero p.1.2))

/-- The original new and old fourfold integrals differ by exactly the
actual semantic G_B integral; `K/4` occurs once on every term. -/
theorem row_difference_eq_semantic_gain (r : Row) :
    rowBuchstabIntegral r - rowHalfBaselineIntegral r = P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r := by
  let F : Quad → ℝ := fun p => quarterWeight (clampQuad p) * buchstabValue (clampQuad p)
  let G : Quad → ℝ := fun p => quarterWeight (clampQuad p) * (1 / 2)
  have hF : Continuous F := continuous_clampedWeight.mul continuous_clampedBuchstab
  have hG : Continuous G := continuous_clampedWeight.mul continuous_const
  have hnew : rowIntegral r F = rowBuchstabIntegral r :=
    rowIntegral_clamp_eq r (fun p => quarterWeight p * buchstabValue p)
  have hold : rowIntegral r G = rowHalfBaselineIntegral r :=
    rowIntegral_clamp_eq r (fun p => quarterWeight p * (1 / 2))
  have hdiff : rowIntegral r (fun p => F p - G p) = P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r := by
    change rowIntegral r (fun p => F p - G p) =
      rowIntegral r (fun p => quarterWeight p * (buchstabValue p - (1 / 2)))
    apply rowIntegral_congr_on_closed r
    intro t u z w hs
    dsimp [F, G]
    rw [clampQuad_eq r hs]
    ring
  have hsub := fourfold_sub hF hG (a : ℝ)
    (tLower (indices r).1) (tUpper (indices r).1)
    (uLower (indices r).2) (uUpper (indices r).2) (cutoff r)
  change rowIntegral r (fun p => F p - G p) = rowIntegral r F - rowIntegral r G at hsub
  rw [hdiff, hnew, hold] at hsub
  exact hsub.symm

/-- The half-baseline integral is exactly ten times the existing `1/20`
gain certificate, using the same `K/4` normalization throughout. -/
theorem rowHalfBaselineIntegral_eq_ten_certificate (r : Row) :
    rowHalfBaselineIntegral r = 10 * pairedLocalIntegral (K : ℝ) a
      (tLower (indices r).1) (tUpper (indices r).1)
      (uLower (indices r).2) (uUpper (indices r).2) (cutoff r) := by
  have hpoint (t u z w : ℝ) : quarterWeight (((t, u), z), w) * (1 / 2) =
      (10 * ((K : ℝ) / 80)) * pairedFibreKernel t u z w := by
    rw [pairedFibreKernel_eq]
    unfold quarterWeight pairedChenQuarterWeight
    ring
  unfold rowHalfBaselineIntegral rowIntegral fourfold
  simp_rw [hpoint]
  simp only [intervalIntegral.integral_const_mul, pairedLocalIntegral]
  ring

def fullSemanticGain : ℝ := ∑ r : Row, P2PairedFibreBuchstabVariableLower.FullMask.rowGainIntegral r

def fullBuchstabIntegral : ℝ := ∑ r : Row, rowBuchstabIntegral r

def fullHalfBaselineIntegral : ℝ := ∑ r : Row, rowHalfBaselineIntegral r

/-- The full 17572-row difference is the sum of the actual G_B integrals. -/
theorem full_difference_eq_semantic_gain :
    fullBuchstabIntegral - fullHalfBaselineIntegral = fullSemanticGain := by
  unfold fullBuchstabIntegral fullHalfBaselineIntegral fullSemanticGain
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun r _hr => row_difference_eq_semantic_gain r)

theorem fullHalfBaselineIntegral_eq_ten_certificate :
    fullHalfBaselineIntegral = 10 * PairedV2.FullMask.integral := by
  unfold fullHalfBaselineIntegral PairedV2.FullMask.integral
  simp_rw [rowHalfBaselineIntegral_eq_ten_certificate]
  exact (Finset.mul_sum _ _ _).symm

/-- Actual semantic gain with the original fixed rational lower endpoint.
The bound is supplied by existing checker soundness, not as a premise. -/
theorem fullSemanticGain_lower :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤ fullSemanticGain := by
  exact le_trans PairedV2.FullMask.integral_bounds.1 P2PairedFibreBuchstabVariableLower.FullMask.fullMask_semantic_gain_ge_integral

/-- The frozen rounded-down extra-gross bound also applies to the actual
semantic gain; its original rational value is unchanged. -/
theorem fullSemanticGain_adopted_lower : (558583 / 1000000000 : ℝ) ≤ fullSemanticGain := by
  exact le_trans PairedV2.FullMask.adopted_extra_gross_lower P2PairedFibreBuchstabVariableLower.FullMask.fullMask_semantic_gain_ge_integral

theorem fullSemanticGain_pos : 0 < fullSemanticGain :=
  lt_of_lt_of_le (by norm_num) fullSemanticGain_lower

/-- The literal new Buchstab integral exceeds the literal old half
baseline by at least the original certified gain, unconditionally. -/
theorem full_difference_lower :
    (55858378943374979 / 100000000000000000000 : ℝ) ≤
      fullBuchstabIntegral - fullHalfBaselineIntegral := by
  rw [full_difference_eq_semantic_gain]
  exact fullSemanticGain_lower

theorem fullBuchstabIntegral_gt_halfBaseline :
    fullHalfBaselineIntegral < fullBuchstabIntegral := by
  have hp := fullSemanticGain_pos
  rw [← full_difference_eq_semantic_gain] at hp
  linarith

end

end ImbalancedChen.Certificates.P2PairedSemanticGainEnclosure
