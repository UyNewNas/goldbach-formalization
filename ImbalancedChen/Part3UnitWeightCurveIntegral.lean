import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! Unit-modulus Fourier tests on a compact parameterized curve can be recovered
from three unweighted compact-curve tests. The curves depend only on the
original curve and its weight, uniformly over every function being tested. -/
namespace ImbalancedChen.Part3.UnitWeightCurveIntegral20261123

noncomputable section
open Complex Set MeasureTheory

/-- Change of variables by the primitive of a continuous density bounded
below by one. Both the time change and the total mass precede the test. -/
theorem positive_curve_weight {X : Type*} [TopologicalSpace X]
    (Z : ℝ → X) (hZ : Continuous Z) (w : ℝ → ℝ) (hw : Continuous w)
    (hpos : ∀ x, 1 ≤ w x) :
    ∃ (P : ℝ → X) (mass : ℝ), Continuous P ∧ 0 < mass ∧
      ∀ F : X → ℂ,
        (∫ x in (0 : ℝ)..1, (w x : ℂ) * F (Z x)) =
          (mass : ℂ) * ∫ x in (0 : ℝ)..1, F (P x) := by
  let A (x : ℝ) := ∫ u in (0 : ℝ)..x, w u
  have hA (x : ℝ) : HasDerivAt A (w x) x := (hw.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hcont : Continuous A := continuous_iff_continuousAt.mpr (fun x => (hA x).continuousAt)
  have hmono : StrictMono A := strictMono_of_deriv_pos fun x => by
    rw [(hA x).deriv]
    exact zero_lt_one.trans_le (hpos x)
  have hdiff : Monotone (fun x : ℝ => A x - x) :=
    monotone_of_hasDerivAt_nonneg (fun x => (hA x).sub (hasDerivAt_id x))
      (fun x => sub_nonneg.mpr (hpos x))
  have hz : A 0 = 0 := by simp [A]
  have hsurj : Function.Surjective A := by
    intro y
    have hlo := hdiff (min_le_right y 0)
    have hhi := hdiff (le_max_right y 0)
    change A (min y 0) - min y 0 ≤ A 0 - 0 at hlo
    change A 0 - 0 ≤ A (max y 0) - max y 0 at hhi
    rw [hz] at hlo hhi
    have hm : min y 0 ≤ max y 0 := (min_le_left _ _).trans (le_max_left _ _)
    have hy : y ∈ Icc (A (min y 0)) (A (max y 0)) :=
      ⟨by linarith [min_le_left y 0], by linarith [le_max_left y 0]⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc hm hcont.continuousOn hy
    exact ⟨x, hx⟩
  let e := StrictMono.orderIsoOfSurjective A hmono hsurj
  let P (x : ℝ) := Z (e.symm (A 1 * x))
  refine ⟨P, A 1, hZ.comp (e.symm.continuous.comp (continuous_const.mul continuous_id)), ?_, ?_⟩
  · simpa only [hz] using hmono (show (0 : ℝ) < 1 by norm_num)
  · intro F
    let G (u : ℝ) := F (Z (e.symm u))
    have hind (x : ℝ) : G (A x) = F (Z x) := by
      change F (Z (e.symm (e x))) = _
      rw [e.symm_apply_apply]
    have H := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1) (g := G) hcont.continuousOn
      (fun x _ => hA x) (fun x _ => zero_le_one.trans (hpos x))
    simp only [Function.comp_apply, hind, hz, Complex.real_smul] at H
    rw [H]
    simpa only [zero_mul, mul_zero, mul_one, Complex.real_smul] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := 1) G (A 1)).symm

/-- A bounded complex test is a fixed linear combination of means of three
continuous paths, valid simultaneously for all continuous spatial profiles. -/
theorem unit_weight_curve_formula {X : Type*} [TopologicalSpace X]
    (Z : ℝ → X) (hZ : Continuous Z) (w : ℝ → ℂ) (hw : Continuous w)
    (hbound : ∀ x, ‖w x‖ ≤ 1) :
    ∃ (P Q : ℝ → X) (c d : ℝ), Continuous P ∧ Continuous Q ∧
      0 < c ∧ 0 < d ∧ ∀ (F : X → ℂ), Continuous F →
        (∫ x in (0 : ℝ)..1, w x * F (Z x)) =
          (c : ℂ) * (∫ x in (0 : ℝ)..1, F (P x)) +
          Complex.I * ((d : ℂ) * (∫ x in (0 : ℝ)..1, F (Q x))) -
          (2 + 2 * Complex.I) * (∫ x in (0 : ℝ)..1, F (Z x)) := by
  let u := fun x : ℝ => 2 + (w x).re
  let v := fun x : ℝ => 2 + (w x).im
  have hu : Continuous u := continuous_const.add (Complex.continuous_re.comp hw)
  have hv : Continuous v := continuous_const.add (Complex.continuous_im.comp hw)
  have hul (x : ℝ) : 1 ≤ u x := by
    have H := (abs_le.mp ((Complex.abs_re_le_norm (w x)).trans (hbound x))).1
    dsimp [u]
    linarith
  have hvl (x : ℝ) : 1 ≤ v x := by
    have H := (abs_le.mp ((Complex.abs_im_le_norm (w x)).trans (hbound x))).1
    dsimp [v]
    linarith
  obtain ⟨P, c, hP, hc, HP⟩ := positive_curve_weight Z hZ u hu hul
  obtain ⟨Q, d, hQ, hd, HQ⟩ := positive_curve_weight Z hZ v hv hvl
  refine ⟨P, Q, c, d, hP, hQ, hc, hd, ?_⟩
  intro F hF
  let A := fun x : ℝ => (u x : ℂ) * F (Z x)
  let B := fun x : ℝ => (v x : ℂ) * F (Z x)
  let D := fun x : ℝ => (2 + 2 * Complex.I) * F (Z x)
  have hA : Continuous A := (Complex.continuous_ofReal.comp hu).mul (hF.comp hZ)
  have hB : Continuous B := (Complex.continuous_ofReal.comp hv).mul (hF.comp hZ)
  have hD : Continuous D := continuous_const.mul (hF.comp hZ)
  have hIB : Continuous (fun x : ℝ => Complex.I * B x) := continuous_const.mul hB
  have he (x : ℝ) : w x * F (Z x) = A x + Complex.I * B x - D x := by
    dsimp [A, B, D, u, v]
    push_cast
    calc
      _ = ((w x).re + (w x).im * Complex.I) * F (Z x) := by rw [Complex.re_add_im]
      _ = _ := by ring
  simp_rw [he]
  rw [intervalIntegral.integral_sub (μ := volume) (f := fun x : ℝ => A x + Complex.I * B x)
      (g := D) ((hA.add hIB).intervalIntegrable 0 1)
      (hD.intervalIntegrable 0 1),
    intervalIntegral.integral_add (μ := volume) (f := A) (g := fun x : ℝ => Complex.I * B x)
      (hA.intervalIntegrable 0 1)
      (hIB.intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul (μ := volume) Complex.I B]
  change (∫ x in (0 : ℝ)..1, (u x : ℂ) * F (Z x)) +
    Complex.I * (∫ x in (0 : ℝ)..1, (v x : ℂ) * F (Z x)) -
    (∫ x in (0 : ℝ)..1, (2 + 2 * Complex.I) * F (Z x)) = _
  rw [HP F, HQ F, intervalIntegral.integral_const_mul]

end
end ImbalancedChen.Part3.UnitWeightCurveIntegral20261123
