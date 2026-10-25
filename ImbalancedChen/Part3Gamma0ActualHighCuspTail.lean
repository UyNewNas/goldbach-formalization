import ImbalancedChen.Part3Gamma0ActualParabolicUnfolding
import ImbalancedChen.Part3ActualCuspStripCutoff
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Genuine high-cusp disjointness for the ACTUAL GammaInfinity\Gamma0 cosets.
A nonzero integral lower-left entry implies Im(gz)*Im(z)<=1 by the actual
Mobius denominator formula. Distinct parabolic representatives therefore
cannot both have image height >Y when Y>=1. Closed heights >=Y are also
disjoint when Y>1. The latter exact indicator is used for the tail measure.

The actual nonnegative parabolic quotient series of that closed high-cusp
indicator takes only 0 and 1. It is the indicator of a measurable subset of
the original quotient. Genuine parabolic unfolding and the previously
proved canonical strip volume give this standard cusp tail mass exactly
1/Y, for every Gamma0 level. This is ONE actual width-one infinity cusp;
an all-cusps index/Y claim requires the separate full cusp decomposition.
No global smooth quotient cutoff, form-core approximation, or constant
kernel membership is assumed or asserted.
-/

namespace ImbalancedChen.Part3.Gamma0ActualHighCuspTail20261025a

noncomputable section
open Set MeasureTheory
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups UpperHalfPlane ENNReal
open Gamma0ParabolicBottomRow20261025a Gamma0ParabolicCosetRows20261025a
open Gamma0ParabolicEffectiveDecomposition20261025a GammaInfinityTranslationStrip20261025a
open Gamma0ActualParabolicUnfolding20261025a Gamma0QuotientCellPushforward20261025a
open Gamma0CarrierAESection20261025a Gamma0CarrierMeasurableInverse20261025a
open Gamma0QuotientConullTransport20261025a ActualCuspStripCutoff20261025a

/-- The genuine integer action shrinks height past the reciprocal bound
unless the matrix fixes infinity. No model-space action is substituted. -/
theorem im_smul_mul_im_le_one (g : SL(2,ℤ)) (hc : g 1 0≠0) (z : UpperHalfPlane) :
    (g • z).im*z.im≤1 := by
  let G := SpecialLinearGroup.mapGL ℝ g
  have hcpos : (0:ℤ)<(g 1 0)^2 := sq_pos_of_ne_zero hc
  have hcint : (1:ℤ)≤(g 1 0)^2 := by omega
  have hcr : (1:ℝ)≤(g 1 0:ℝ)^2 := by exact_mod_cast hcint
  have hden : ((g 1 0:ℝ)*z.im)^2≤Complex.normSq (UpperHalfPlane.denom G z) := by
    simpa [G] using UpperHalfPlane.c_mul_im_sq_le_normSq_denom G z
  have hysq : z.im^2≤Complex.normSq (UpperHalfPlane.denom G z) := by
    have hmul := mul_le_mul_of_nonneg_right hcr (sq_nonneg z.im)
    nlinarith [hden]
  have hdenpos : 0<Complex.normSq (UpperHalfPlane.denom G z) :=
    UpperHalfPlane.normSq_denom_pos G z.im_ne_zero
  have him : (g • z).im=z.im/Complex.normSq (UpperHalfPlane.denom G z) := by
    change (G • z).im=_
    rw [UpperHalfPlane.im_smul_eq_div_normSq]
    simp only [G,SpecialLinearGroup.det_mapGL,Units.val_one,abs_one,one_mul]
  have heq : (g • z).im*Complex.normSq (UpperHalfPlane.denom G z)=z.im :=
    (eq_div_iff hdenpos.ne').mp him
  have hsq : (g • z).im*z.im^2≤z.im :=
    (mul_le_mul_of_nonneg_left hysq (g • z).im_pos.le).trans_eq heq
  apply (mul_le_mul_right z.im_pos).mp
  simpa only [pow_two,mul_assoc,one_mul] using hsq

/-- Two actual Gamma0 images both above height one lie in the same actual
GammaInfinity left coset. The relative c=0 conclusion is derived. -/
theorem two_high_images_same_coset (N : ℕ)
    (g h : CongruenceSubgroup.Gamma0 N) (z : UpperHalfPlane)
    (hg : 1<(g • z).im) (hh : 1<(h • z).im) :
    (Quotient.mk'' g : GammaInfinityCosets N)=Quotient.mk'' h := by
  have hc : (((g*h⁻¹ : CongruenceSubgroup.Gamma0 N):SL(2,ℤ)) 1 0)=0 := by
    by_contra hne
    have hbound := im_smul_mul_im_le_one
      ((g*h⁻¹ : CongruenceSubgroup.Gamma0 N):SL(2,ℤ)) hne (h • z)
    have haction : ((g*h⁻¹ : CongruenceSubgroup.Gamma0 N):SL(2,ℤ)) • (h • z)=g • z := by
      change ((g:SL(2,ℤ))*(h:SL(2,ℤ))⁻¹) • ((h:SL(2,ℤ)) • z)=_
      simp only [mul_smul,inv_smul_smul]
    rw [haction] at hbound
    have hprod : 1<(g • z).im*(h • z).im :=
      hh.trans (by simpa only [one_mul] using mul_lt_mul_of_pos_right hg (h • z).im_pos)
    exact (not_lt_of_ge hbound) hprod
  apply Quotient.sound
  apply (parabolic_orbit_iff_relative N g h).mpr
  exact hc

/-- Literal strict high cusps are disjoint already at the threshold Y=1. -/
theorem strict_high_coset_unique (N : ℕ) (Y : ℝ) (hY : 1≤Y)
    (q r : GammaInfinityCosets N) (z : UpperHalfPlane)
    (hq : Y<(parabolicRepresentative N q • z).im)
    (hr : Y<(parabolicRepresentative N r • z).im) : q=r := by
  have heq := two_high_images_same_coset N (parabolicRepresentative N q)
    (parabolicRepresentative N r) z (hY.trans_lt hq) (hY.trans_lt hr)
  simpa only [parabolicRepresentative_class] using heq

theorem closed_high_coset_unique (N : ℕ) (Y : ℝ) (hY : 1<Y)
    (q r : GammaInfinityCosets N) (z : UpperHalfPlane)
    (hq : Y≤(parabolicRepresentative N q • z).im)
    (hr : Y≤(parabolicRepresentative N r • z).im) : q=r := by
  have heq := two_high_images_same_coset N (parabolicRepresentative N q)
    (parabolicRepresentative N r) z (hY.trans_le hq) (hY.trans_le hr)
  simpa only [parabolicRepresentative_class] using heq

def strictHighSeed (Y : ℝ) : UpperHalfPlane → ℝ≥0∞ :=
  {z | Y<z.im}.indicator (fun _ => 1)

/-- The literal strict high-cusp indicator trace is 0/1 for Y>=1,
including the exact geometric threshold. -/
theorem strictHighTrace_zero_or_one (N : ℕ) (Y : ℝ) (hY : 1≤Y) (z : UpperHalfPlane) :
    parabolicTraceNN N (strictHighSeed Y) z=0 ∨ parabolicTraceNN N (strictHighSeed Y) z=1 := by
  classical
  by_cases hex : ∃ q : GammaInfinityCosets N,Y<(parabolicRepresentative N q • z).im
  · obtain ⟨q,hq⟩ := hex
    right
    rw [parabolicTraceNN,tsum_eq_single q]
    · simp only [strictHighSeed,indicator_of_mem hq]
    · intro r hr
      exact indicator_of_notMem (fun hh => hr (strict_high_coset_unique N Y hY r q z hh hq)) _
  · left
    apply tsum_eq_zero.mpr
    intro q
    exact indicator_of_notMem (fun h => hex ⟨q,h⟩) _

def highRegion (Y : ℝ) : Set UpperHalfPlane := {z | Y≤z.im}

theorem highRegion_measurable (Y : ℝ) : MeasurableSet (highRegion Y) :=
  UpperHalfPlane.continuous_im.measurable measurableSet_Ici

def highSeed (Y : ℝ) : UpperHalfPlane → ℝ≥0∞ :=
  (highRegion Y).indicator (fun _ => 1)

theorem highSeed_measurable (Y : ℝ) : Measurable (highSeed Y) :=
  measurable_const.indicator (highRegion_measurable Y)

theorem highSeed_periodic (Y : ℝ) (k : ℤ) (z : UpperHalfPlane) :
    highSeed Y (translate k z)=highSeed Y z := by
  have him : (translate k z).im=z.im := by rw [translate_eq_vadd,UpperHalfPlane.vadd_im]
  simp only [highSeed,Set.indicator,highRegion,mem_setOf_eq,him]

/-- The actual parabolic indicator trace is a true 0/1 value; no overlap
count or a.e. multiplicity conclusion is a premise. -/
theorem highTrace_zero_or_one (N : ℕ) (Y : ℝ) (hY : 1<Y) (z : UpperHalfPlane) :
    parabolicTraceNN N (highSeed Y) z=0 ∨ parabolicTraceNN N (highSeed Y) z=1 := by
  classical
  by_cases hex : ∃ q : GammaInfinityCosets N,Y≤(parabolicRepresentative N q • z).im
  · obtain ⟨q,hq⟩ := hex
    right
    rw [parabolicTraceNN,tsum_eq_single q]
    · simp only [highSeed,indicator_of_mem hq]
    · intro r hr
      have hnot : ¬Y≤(parabolicRepresentative N r • z).im := by
        intro hh
        exact hr (closed_high_coset_unique N Y hY r q z hh hq)
      exact indicator_of_notMem hnot _
  · left
    apply tsum_eq_zero.mpr
    intro q
    exact indicator_of_notMem (fun h => hex ⟨q,h⟩) _

def quotientHighIndicator (N : ℕ) [NeZero N] (Y : ℝ) : Gamma0OrbitSpace N → ℝ≥0∞ :=
  parabolicNonnegativePoincare N (highSeed Y)

theorem quotientHighIndicator_measurable (N : ℕ) [NeZero N] (Y : ℝ) :
    Measurable (quotientHighIndicator N Y) := by
  exact (reducedProjection_measurableEmbedding N).measurable_extend
    ((parabolicTraceNN_measurable N _ (highSeed_measurable Y)).comp measurable_subtype_coe)
    measurable_const

theorem quotientHighIndicator_zero_or_one (N : ℕ) [NeZero N]
    (Y : ℝ) (hY : 1<Y) (u : Gamma0OrbitSpace N) :
    quotientHighIndicator N Y u=0 ∨ quotientHighIndicator N Y u=1 := by
  by_cases hu : u∈range (reducedProjection N)
  · obtain ⟨z,rfl⟩ := hu
    rw [quotientHighIndicator,parabolicNonnegativePoincare_projection]
    exact highTrace_zero_or_one N Y hY z
  · left
    exact Function.extend_apply' _ _ u hu

/-- The actual standard-infinity cusp tail in the genuine quotient. -/
def quotientHighTail (N : ℕ) [NeZero N] (Y : ℝ) : Set (Gamma0OrbitSpace N) :=
  {u | quotientHighIndicator N Y u=1}

theorem quotientHighTail_measurable (N : ℕ) [NeZero N] (Y : ℝ) :
    MeasurableSet (quotientHighTail N Y) :=
  (quotientHighIndicator_measurable N Y) measurableSet_singleton

theorem quotientHighIndicator_eq_indicator (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1<Y) :
    quotientHighIndicator N Y=(quotientHighTail N Y).indicator (fun _ => 1) := by
  funext u
  rcases quotientHighIndicator_zero_or_one N Y hY u with hu|hu
  · simp only [quotientHighTail,mem_setOf_eq,hu,zero_ne_one,not_false_eq_true,
      indicator_of_notMem,Pi.zero_apply]
  · simp only [quotientHighTail,mem_setOf_eq,hu,indicator_of_mem]

/-- Exact mass of ONE genuine width-one Gamma0 cusp tail. This is not
the sum over a supplied family of cusp charts or a guessed index factor. -/
theorem quotientHighTail_volume (N : ℕ) [NeZero N] (Y : ℝ) (hY : 1<Y) :
    carrierPushforward N (quotientHighTail N Y)=ENNReal.ofReal (1/Y) := by
  have hYpos : 0<Y := (by norm_num : (0:ℝ)<1).trans hY
  have hleft : (∫⁻ u,quotientHighIndicator N Y u ∂carrierPushforward N)=
      carrierPushforward N (quotientHighTail N Y) := by
    rw [quotientHighIndicator_eq_indicator N Y hY,
      lintegral_indicator (quotientHighTail_measurable N Y)]
    simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  have hright : (∫⁻ z in strip,highSeed Y z)=ENNReal.ofReal (1/Y) := by
    rw [highSeed,lintegral_indicator (highRegion_measurable Y)]
    simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
    rw [Measure.restrict_apply (highRegion_measurable Y)]
    have hset : highRegion Y∩strip=highWidthStrip 1 Y := by
      ext z
      simp only [highRegion,strip,highWidthStrip,widthStrip,mem_inter_iff,mem_setOf_eq]
      tauto
    rw [hset]
    exact highWidthStrip_volume (by norm_num : (0:ℝ)≤1) hYpos
  rw [← hleft]
  exact (nonnegative_parabolic_quotient_unfolding N (highSeed Y)
    (highSeed_periodic Y) (highSeed_measurable Y)).trans hright

end
end ImbalancedChen.Part3.Gamma0ActualHighCuspTail20261025a
