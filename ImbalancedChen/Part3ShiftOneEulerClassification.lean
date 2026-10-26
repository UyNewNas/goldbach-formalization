import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT, 2026-10-26.

Clean exact shift-one Euler classification on y>0. Genuine C2 regularity
and f''=f/y^2 give native derivative jets. The two actual Wronskian
coefficient functions are differentiated and proved constant by the
primary derivative-uniqueness theorem on the connected open positive
line. Their explicit reconstruction proves the true basis
y^((1+sqrt 5)/2), y^((1-sqrt 5)/2), with no assumed basis or IVP supplier.

No old CuspConstantMode source or HOLD supplier is imported. No tail L2,
small-y admissibility, quotient geometry or spectral completeness is
claimed here. This theorem is exact shift 1, not a general small-y claim.
-/

namespace ImbalancedChen.Part3.ShiftOneEulerClassification20261026b
noncomputable section
open Set

def alphaPlus : ℝ := (1 + Real.sqrt 5) / 2
def alphaMinus : ℝ := (1 - Real.sqrt 5) / 2

theorem alpha_sum : alphaPlus + alphaMinus = 1 := by unfold alphaPlus alphaMinus; ring

theorem alpha_product : alphaPlus * alphaMinus = -1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  unfold alphaPlus alphaMinus
  nlinarith

theorem alpha_difference : alphaPlus - alphaMinus = Real.sqrt 5 := by
  unfold alphaPlus alphaMinus
  ring

theorem alphaPlus_gt_threeHalves : (3 / 2 : ℝ) < alphaPlus := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  unfold alphaPlus
  nlinarith

theorem alphaMinus_lt_negHalf : alphaMinus < -(1 / 2 : ℝ) := by
  have h := alphaPlus_gt_threeHalves
  have hs := alpha_sum
  linarith

def eulerPower (a y : ℝ) : ℂ := (Real.exp (a * Real.log y) : ℂ)

theorem eulerPower_one (a : ℝ) : eulerPower a 1 = 1 := by simp [eulerPower]

theorem eulerPower_mul_inverse (a y : ℝ) : eulerPower a y * eulerPower (-a) y = 1 := by
  unfold eulerPower
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  rw [show a * Real.log y + -a * Real.log y = 0 by ring, Real.exp_zero, Complex.ofReal_one]

theorem eulerPower_eq_rpow (a : ℝ) {y : ℝ} (hy : 0 < y) :
    eulerPower a y = (y ^ a : ℝ) := by
  rw [Real.rpow_def_of_pos hy]
  unfold eulerPower
  congr 2
  ring

theorem eulerPower_hasDerivAt (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (eulerPower a) (((a : ℂ) / (y : ℂ)) * eulerPower a y) y := by
  have hr := (((Real.hasDerivAt_log hy.ne').const_mul a).exp).ofReal_comp
  convert hr using 1 <;>
    simp only [eulerPower, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv] <;> ring

def ShiftOneJets (f : ℝ → ℂ) : Prop :=
  ∀ y : ℝ, 0 < y → HasDerivAt f (deriv f y) y ∧
    HasDerivAt (deriv f) (f y / (y : ℂ) ^ 2) y

theorem shiftOneJets_of_C2 (f : ℝ → ℂ) (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → deriv (deriv f) y = f y / (y : ℂ) ^ 2) : ShiftOneJets f := by
  intro y hy
  have hc : ContDiffAt ℝ 2 f y := (hC2 y hy).contDiffAt (isOpen_Ioi.mem_nhds hy)
  have hd : DifferentiableAt ℝ (deriv f) y :=
    (hc.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact ⟨(hc.differentiableAt (by norm_num)).hasDerivAt,
    by simpa only [hODE y hy] using hd.hasDerivAt⟩

def eulerWronskian (r s : ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  eulerPower (-r) y * ((y : ℂ) * deriv f y - (s : ℂ) * f y)

/-- Direct native derivative calculation pays the Wronskian first
integral. The hypotheses are the elementary root equations, not a basis. -/
theorem eulerWronskian_hasDerivAt_zero {r s : ℝ} (hsum : r + s = 1) (hprod : r * s = -1)
    {f : ℝ → ℂ} (hf : ShiftOneJets f) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (eulerWronskian r s f) 0 y := by
  have hyC : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hsC : (r : ℂ) + (s : ℂ) = 1 := by exact_mod_cast hsum
  have hpC : (r : ℂ) * (s : ℂ) = -1 := by exact_mod_cast hprod
  have hz1 : 1 - (r : ℂ) - (s : ℂ) = 0 := by linear_combination -hsC
  have hz2 : (r : ℂ) * (s : ℂ) + 1 = 0 := by linear_combination hpC
  have hB : HasDerivAt (fun x : ℝ => (x : ℂ) * deriv f x - (s : ℂ) * f x)
      (deriv f y + (y : ℂ) * (f y / (y : ℂ) ^ 2) - (s : ℂ) * deriv f y) y := by
    simpa only [one_mul] using
      (Complex.ofRealCLM.hasDerivAt.mul (hf y hy).2).sub ((hf y hy).1.const_mul (s : ℂ))
  have hD : ((((-r : ℝ) : ℂ) / (y : ℂ)) * eulerPower (-r) y) *
        ((y : ℂ) * deriv f y - (s : ℂ) * f y) +
      eulerPower (-r) y *
        (deriv f y + (y : ℂ) * (f y / (y : ℂ) ^ 2) - (s : ℂ) * deriv f y) = 0 := by
    calc
      _ = eulerPower (-r) y *
          ((1 - (r : ℂ) - (s : ℂ)) * deriv f y +
            ((r : ℂ) * (s : ℂ) + 1) * f y / (y : ℂ)) := by
        push_cast
        field_simp [hyC]
        <;> ring
      _ = 0 := by rw [hz1, hz2]; simp
  simpa only [eulerWronskian, hD] using (eulerPower_hasDerivAt (-r) hy).mul hB

theorem eulerWronskian_constant {r s : ℝ} (hsum : r + s = 1) (hprod : r * s = -1)
    {f : ℝ → ℂ} (hf : ShiftOneJets f) :
    EqOn (eulerWronskian r s f) (fun _ => eulerWronskian r s f 1) (Ioi (0 : ℝ)) := by
  apply isOpen_Ioi.eqOn_of_deriv_eq (x := (1 : ℝ)) isPreconnected_Ioi
    (fun y hy => (eulerWronskian_hasDerivAt_zero hsum hprod hf hy).differentiableAt.differentiableWithinAt)
    differentiableOn_const
  · intro y hy
    rw [(eulerWronskian_hasDerivAt_zero hsum hprod hf hy).deriv, deriv_const]
  · norm_num
  · rfl

/-- Classification of the actual C2 Euler solution, with both genuine
Wronskians and their global constancy proved above. -/
theorem shiftOneEuler_classification (f : ℝ → ℂ)
    (hC2 : ContDiffOn ℝ 2 f (Ioi (0 : ℝ)))
    (hODE : ∀ y : ℝ, 0 < y → deriv (deriv f) y = f y / (y : ℂ) ^ 2) :
    ∃ A B : ℂ, ∀ y : ℝ, 0 < y →
      f y = A * eulerPower alphaPlus y + B * eulerPower alphaMinus y := by
  have hf := shiftOneJets_of_C2 f hC2 hODE
  have hplus := eulerWronskian_constant alpha_sum alpha_product hf
  have hminus := eulerWronskian_constant (by simpa only [add_comm] using alpha_sum)
    (by simpa only [mul_comm] using alpha_product) hf
  have hd : (alphaPlus : ℂ) - (alphaMinus : ℂ) ≠ 0 := by
    have hr : alphaPlus - alphaMinus ≠ 0 := by
      rw [alpha_difference]
      exact (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 5)).ne'
    exact_mod_cast hr
  refine ⟨eulerWronskian alphaPlus alphaMinus f 1 / ((alphaPlus : ℂ) - (alphaMinus : ℂ)),
    -eulerWronskian alphaMinus alphaPlus f 1 / ((alphaPlus : ℂ) - (alphaMinus : ℂ)), ?_⟩
  intro y hy
  have hp : eulerPower alphaPlus y * eulerWronskian alphaPlus alphaMinus f 1 =
      (y : ℂ) * deriv f y - (alphaMinus : ℂ) * f y := by
    rw [← hplus hy, eulerWronskian, ← mul_assoc, eulerPower_mul_inverse, one_mul]
  have hm : eulerPower alphaMinus y * eulerWronskian alphaMinus alphaPlus f 1 =
      (y : ℂ) * deriv f y - (alphaPlus : ℂ) * f y := by
    rw [← hminus hy, eulerWronskian, ← mul_assoc, eulerPower_mul_inverse, one_mul]
  field_simp [hd]
  linear_combination -hp + hm

end
end ImbalancedChen.Part3.ShiftOneEulerClassification20261026b
