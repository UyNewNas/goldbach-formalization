import ImbalancedChen.ActualThirdPrefixTailIntegralCore

/-!
# The literal extended ideal cap and its noncompact tail

At manuscript pin ba6ec11d800eccc54406490631895e174de85766,
`proof-library/source/extended-prefix-upper.tex`, lines 12--20, the ideal
envelope is the full gated `Phi` for `x <= 25/128` and the single-variable
`v(x)` otherwise. Equality belongs to the full-envelope branch. The cap is
`min(299/500, A)`. Every original gate remains in the definition below.

Measurability is proved from those actual finite affine comparisons; no
measurable-selector-fibre hypothesis is imposed. The buffered cap inherits a
uniform residual margin and the already proved genuine nonnegative tail
mass bound. This is the ideal analytic functional, not the finite robust
coarse policy of lines 84--103. It does not identify the numerical enclosure
partition with that physical policy or prove a density asymptotic.
-/

namespace ImbalancedChen

noncomputable section

open Filter Topology Set MeasureTheory
open VariableEnvelope
open scoped ENNReal

/-- The actual manuscript dispatch: retain the full gated envelope at equality. -/
def actualExtendedThirdEnvelope (x y z : ℝ) : ℝ :=
  if x ≤ mu then original x y z else v x

/-- The already verified six-branch reduction is used only on its true
ordered domain, without replacing the gated definition off that domain. -/
theorem actualExtendedThirdEnvelope_eq_six {x y z : ℝ} (ht : Ordered x y z) :
    actualExtendedThirdEnvelope x y z = six x y z := by
  rw [actualExtendedThirdEnvelope, if_pos ht.2.2.2, original_eq_six ht]

/-- The same positive buffer is subtracted from both levels before the minimum. -/
def actualExtendedThirdBufferedCap (e x y z : ℝ) : ℝ :=
  thirdPrefixBufferedCap e (actualExtendedThirdEnvelope x y z)

/-- The literal ideal `L = min(Theta,A)` of the extended functional. -/
def actualExtendedThirdIdealCap (x y z : ℝ) : ℝ :=
  actualExtendedThirdBufferedCap 0 x y z

theorem actualExtendedThirdIdealCap_eq (x y z : ℝ) :
    actualExtendedThirdIdealCap x y z =
      min thirdPrefixTheta (if x ≤ mu then original x y z else v x) := by
  simp only [actualExtendedThirdIdealCap, actualExtendedThirdBufferedCap,
    thirdPrefixBufferedCap, actualExtendedThirdEnvelope, mul_zero, sub_zero]

private theorem measurable_psi_comp {α : Type*} [MeasurableSpace α]
    {a b : α → ℝ} (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun t => psi (a t) (b t)) := by
  unfold psi
  exact ha.piecewise (measurableSet_le hb ha) measurable_const

/-- All eight original branches and both original pair gates are measurable.
Their actual affine comparison sets supply this fact, rather than a hypothesis
on the fibres of an unspecified selector. -/
theorem measurable_actualThirdOriginalEnvelope :
    Measurable (fun t : Fin 3 → ℝ => original (t 0) (t 1) (t 2)) := by
  have hx : Continuous (fun t : Fin 3 → ℝ => t 0) := continuous_apply 0
  have hy : Continuous (fun t : Fin 3 → ℝ => t 1) := continuous_apply 1
  have hz : Continuous (fun t : Fin 3 → ℝ => t 2) := continuous_apply 2
  have hvx := (continuous_v.comp hx).measurable
  have hvy := (continuous_v.comp hy).measurable
  have hvxy := (continuous_v.comp (hx.add hy)).measurable
  have hvxyz := (continuous_v.comp ((hx.add hy).add hz)).measurable
  have hwxyz : Continuous (fun t : Fin 3 → ℝ => wInner (t 0) (t 1) (t 2)) := by
    unfold wInner
    exact ((continuous_const.sub (continuous_const.mul hz)).div_const 107).min
      ((continuous_B.comp hz).min (continuous_const.sub (continuous_const.mul hy)))
  have hwxzy : Continuous (fun t : Fin 3 → ℝ => wInner (t 0) (t 2) (t 1)) := by
    unfold wInner
    exact ((continuous_const.sub (continuous_const.mul hy)).div_const 107).min
      ((continuous_B.comp hy).min (continuous_const.sub (continuous_const.mul hz)))
  have hw1 : Measurable (fun t : Fin 3 → ℝ => w (t 0) (t 1) (t 2)) := by
    unfold w
    exact measurable_psi_comp hwxyz.measurable (continuous_A.comp hx).measurable
  have hw2 : Measurable (fun t : Fin 3 → ℝ => w (t 0) (t 2) (t 1)) := by
    unfold w
    exact measurable_psi_comp hwxzy.measurable (continuous_A.comp hx).measurable
  have hp1 : Measurable (fun t : Fin 3 → ℝ =>
      psi (v (t 0 + t 2)) (t 0 + 2 * t 1 + t 2)) :=
    measurable_psi_comp (continuous_v.comp (hx.add hz)).measurable
      ((hx.add (hy.const_mul 2)).add hz).measurable
  have hp2 : Measurable (fun t : Fin 3 → ℝ =>
      psi (v (t 1 + t 2)) (2 * t 0 + t 1 + t 2)) :=
    measurable_psi_comp (continuous_v.comp (hy.add hz)).measurable
      (((hx.const_mul 2).add hy).add hz).measurable
  unfold original
  exact hvx.max (hvy.max (hvxy.max (hvxyz.max (hw1.max (hw2.max (hp1.max hp2))))))

theorem measurable_actualExtendedThirdEnvelope :
    Measurable (fun t : Fin 3 → ℝ => actualExtendedThirdEnvelope (t 0) (t 1) (t 2)) := by
  unfold actualExtendedThirdEnvelope
  exact measurable_actualThirdOriginalEnvelope.piecewise
    (isClosed_le (continuous_apply 0) continuous_const).measurableSet
    (continuous_v.comp (continuous_apply 0)).measurable

theorem measurable_actualExtendedThirdBufferedCap (e : ℝ) :
    Measurable (fun t : Fin 3 → ℝ => actualExtendedThirdBufferedCap e (t 0) (t 1) (t 2)) := by
  unfold actualExtendedThirdBufferedCap thirdPrefixBufferedCap
  exact measurable_const.min (measurable_actualExtendedThirdEnvelope.sub measurable_const)

theorem measurable_actualExtendedThirdIdealCap :
    Measurable (fun t : Fin 3 → ℝ => actualExtendedThirdIdealCap (t 0) (t 1) (t 2)) :=
  measurable_actualExtendedThirdBufferedCap 0

/-- The baseline survives both actual dispatch branches, including their wall. -/
theorem v_le_actualExtendedThirdEnvelope (x y z : ℝ) :
    v x ≤ actualExtendedThirdEnvelope x y z := by
  unfold actualExtendedThirdEnvelope
  split_ifs
  · unfold original
    exact le_max_left _ _
  · exact le_rfl

theorem half_le_actualExtendedThirdEnvelope {x y z : ℝ}
    (hx0 : 0 ≤ x) (hxrho : x ≤ thirdPrefixRho) :
    (1 / 2 : ℝ) ≤ actualExtendedThirdEnvelope x y z := by
  have hv := half_le_v_of_extended_range hx0
    (show x ≤ extendedFirstStop by simpa only [thirdPrefixRho, extendedFirstStop] using hxrho)
  exact hv.trans (v_le_actualExtendedThirdEnvelope x y z)

/-- Concrete geometry of the literal extended cap. There is no selector or
generic Gamma premise here. -/
theorem actualExtendedThirdBufferedCap_tail_geometry {e x y z : ℝ}
    (he : e ≤ 1 / 384) (hx0 : 0 ≤ x)
    (hx : x ≤ thirdPrefixRho) (hy : y ≤ thirdPrefixRho) :
    thirdPrefixTailMargin ≤ actualExtendedThirdBufferedCap e x y z - x - y ∧
      actualExtendedThirdBufferedCap e x y z ≤ thirdPrefixTheta - 2 * e := by
  constructor
  · exact thirdPrefixBufferedCap_residual_margin he
      (half_le_actualExtendedThirdEnvelope hx0 hx) hx hy
  · exact thirdPrefixBufferedCap_le_root _ _

def actualExtendedThirdIdealTailMass (e h : ℝ) : ℝ≥0∞ :=
  thirdPrefixTailMass (thirdPrefixTheta - 2 * e)
    (actualExtendedThirdBufferedCap e) thirdPrefixRho h

theorem actualExtendedThirdIdealTailMass_le_eighteen {e h : ℝ}
    (he : e ≤ 1 / 384) (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdIdealTailMass e h ≤
      ENNReal.ofReal (18 * h / (thirdPrefixTailMargin - h) ^ 2 *
        (Real.log (thirdPrefixRho / h) ^ 2 + 2 * Real.log (thirdPrefixRho / h) + 2)) := by
  apply thirdPrefixTailMass_le_eighteen hh hsmall
  intro x y z hz _hzh hzy hyx hx
  exact actualExtendedThirdBufferedCap_tail_geometry he
    (hz.le.trans (hzy.trans hyx)) hx (hyx.trans hx)

theorem actualExtendedThirdIdealTailMass_ne_top {e h : ℝ}
    (he : e ≤ 1 / 384) (hh : 0 < h) (hsmall : h ≤ thirdPrefixTailMargin / 4) :
    actualExtendedThirdIdealTailMass e h ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (actualExtendedThirdIdealTailMass_le_eighteen he hh hsmall)

/-- The genuine ideal-envelope tail mass tends to zero; cap geometry and
measurability were paid above from the manuscript's actual formulas. -/
theorem actualExtendedThirdIdealTailMass_tendsto_zero {e : ℝ} (he : e ≤ 1 / 384) :
    Tendsto (actualExtendedThirdIdealTailMass e) (𝓝[>] 0) (𝓝 (0 : ℝ≥0∞)) := by
  apply thirdPrefixTailMass_tendsto_zero_of_cutoffDependentCap
  intro h _hh _hsmall x y z hz _hzh hzy hyx hx
  exact actualExtendedThirdBufferedCap_tail_geometry he
    (hz.le.trans (hzy.trans hyx)) hx (hyx.trans hx)

end

end ImbalancedChen
