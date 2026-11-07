import ImbalancedChen.Part3Gamma0CuspMeasure
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-!
SOURCE ONLY, 2026-10-24. UNCOMPILED; no acceptance credit.

The recovery source supplies a genuine Gamma0(N) parabolic which acts as
translation by one in the scaled cusp-one chart. This module makes its
half-open high strip measurable and proves that strip and its immediate
parabolic translate are disjoint. The chart has finite hyperbolic measure.
This is a local overlap statement for one actual Gamma0 element, not a
fundamental domain or quotient measure for the full Gamma0 group.
-/

namespace ImbalancedChen.Part3.Gamma0CuspChartOverlap20261024zz

noncomputable section

open Set MeasureTheory
open scoped MatrixGroups UpperHalfPlane Pointwise
open P3ActualCuspScalingSourceOnly
open ImbalancedChen.Part3.Gamma0CuspMeasure20261024zz

/-- The half-open strip is Borel in the upper half-plane. -/
theorem highStripIco_measurable : MeasurableSet highStripIco := by
  have hre : Continuous (fun w : UpperHalfPlane => w.re) := by fun_prop
  have him : Continuous (fun w : UpperHalfPlane => w.im) :=
    UpperHalfPlane.continuous_im
  change MeasurableSet
    (((fun w : UpperHalfPlane => w.re) ⁻¹'
        Ico (-(1 : ℝ) / 2) ((1 : ℝ) / 2)) ∩
      ((fun w : UpperHalfPlane => w.im) ⁻¹' Ici (1 : ℝ)))
  exact (measurableSet_Ico.preimage hre.measurable).inter
    (measurableSet_Ici.preimage him.measurable)

/-- The actual scaled chart is measurable; the scaling is an SL(2,R)
action, so its hyperbolic mass is the finite unscaled strip mass. -/
theorem scaledHighStrip_measurable (N : ℕ) (hN : 0 < (N : ℝ)) :
    MeasurableSet (scaledHighStrip N hN) := by
  unfold scaledHighStrip
  exact highStripIco_measurable.const_smul _

private theorem re_one_vadd (w : UpperHalfPlane) :
    ((1 : ℝ) +ᵥ w).re = 1 + w.re := by
  have h : (((1 : ℝ) +ᵥ w : UpperHalfPlane) : ℂ) =
      (1 : ℂ) + (w : ℂ) := by
    simp [UpperHalfPlane.coe_vadd]
  have hr := congrArg Complex.re h
  simpa using hr

/-- A point of the half-open strip cannot return to that strip after
the actual Gamma0 deck transformation. Closed-edge duplication is removed
by the `Ico` choice. -/
theorem scaledHighStrip_disjoint_deck (N : ℕ) (hN : 0 < (N : ℝ)) :
    Disjoint (scaledHighStrip N hN)
      ((cuspDeck N : SL(2, ℤ)) • scaledHighStrip N hN) := by
  apply Set.disjoint_left.mpr
  intro u hu hdeck
  obtain ⟨w, hw, rfl⟩ := hu
  change newSL (N : ℝ) hN • w ∈
    (fun v : UpperHalfPlane => (cuspDeck N : SL(2, ℤ)) • v) ''
      scaledHighStrip N hN at hdeck
  obtain ⟨v, hv, hv_eq⟩ := hdeck
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  have hscaled : newSL (N : ℝ) hN • w =
      newSL (N : ℝ) hN • ((1 : ℝ) +ᵥ v₀) := by
    calc
      newSL (N : ℝ) hN • w =
          (cuspDeck N : SL(2, ℤ)) • (newSL (N : ℝ) hN • v₀) := hv_eq.symm
      _ = newSL (N : ℝ) hN • ((1 : ℝ) +ᵥ v₀) :=
        cuspDeck_smul_newSL_vadd N hN v₀
  have hcoord : w = (1 : ℝ) +ᵥ v₀ := by
    have h := congrArg
      (fun t : UpperHalfPlane => (newSL (N : ℝ) hN)⁻¹ • t) hscaled
    simpa only [← smul_smul, inv_mul_cancel, one_smul] using h
  have hre : w.re = 1 + v₀.re := by
    rw [hcoord, re_one_vadd]
  have hw_upper : w.re < (1 : ℝ) / 2 := hw.1.2
  have hv_lower : -(1 : ℝ) / 2 ≤ v₀.re := hv₀.1.1
  linarith

/-- A finite measurable chart with zero overlap against its immediate
translate by the displayed element of the actual Gamma0 subgroup. -/
theorem scaledHighStrip_chart (N : ℕ) (hN : 0 < (N : ℝ)) :
    MeasurableSet (scaledHighStrip N hN) ∧
      (volume : Measure UpperHalfPlane) (scaledHighStrip N hN) < ∞ ∧
      Disjoint (scaledHighStrip N hN)
        ((cuspDeck N : SL(2, ℤ)) • scaledHighStrip N hN) := by
  exact ⟨scaledHighStrip_measurable N hN,
    scaledHighStrip_finite N hN,
    scaledHighStrip_disjoint_deck N hN⟩

end

end ImbalancedChen.Part3.Gamma0CuspChartOverlap20261024zz
