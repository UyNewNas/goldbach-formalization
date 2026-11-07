import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
SOURCE ONLY / UNCOMPILED / NOT ROOT ACCEPTED.

Explicit square-root paths for the actual Stone parameters z=x +/- i eps.
For x>0, b=sqrt((sqrt(x²+eps²)+x)/2), a=eps/(2b), and nu+=a-i b,
nu-=a+i b. Their square identities are proved algebraically. No principal
square-root continuity across the negative-real branch cut is used.

The uniform bounds retain the actual Stone vertical epsilon: a<=eps/(2sqrt A)
and 0<=b-sqrt x<=eps²/(8 A sqrt A) for x>=A>0. No path or uniform-bound
conclusion is supplied as a premise. Kernel/integrated Stone limits are
separate consumers of these primitives.
-/
namespace ImbalancedChen.Part3.ActualStoneSqrtPath20261025a

noncomputable section
open Set Filter

def rootModulus (x eps : ℝ) : ℝ := Real.sqrt (x ^ 2 + eps ^ 2)
def imagMagnitude (x eps : ℝ) : ℝ := Real.sqrt ((rootModulus x eps + x) / 2)
def realMagnitude (x eps : ℝ) : ℝ := eps / (2 * imagMagnitude x eps)

def nuPlus (x eps : ℝ) : ℂ :=
  (realMagnitude x eps : ℂ) - (imagMagnitude x eps : ℂ) * Complex.I

def nuMinus (x eps : ℝ) : ℂ :=
  (realMagnitude x eps : ℂ) + (imagMagnitude x eps : ℂ) * Complex.I

def zPlus (x eps : ℝ) : ℂ := (x : ℂ) + (eps : ℂ) * Complex.I
def zMinus (x eps : ℝ) : ℂ := (x : ℂ) - (eps : ℂ) * Complex.I

def boundaryPlus (x : ℝ) : ℂ := -(Real.sqrt x : ℂ) * Complex.I
def boundaryMinus (x : ℝ) : ℂ := (Real.sqrt x : ℂ) * Complex.I

theorem rootModulus_nonneg (x eps : ℝ) : 0 ≤ rootModulus x eps := Real.sqrt_nonneg _
theorem rootModulus_sq (x eps : ℝ) : rootModulus x eps ^ 2 = x ^ 2 + eps ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem rootModulus_ge_x {x : ℝ} (hx : 0 ≤ x) (eps : ℝ) : x ≤ rootModulus x eps := by
  have hs := rootModulus_sq x eps
  have hp := rootModulus_nonneg x eps
  nlinarith [sq_nonneg eps]

theorem imagMagnitude_nonneg (x eps : ℝ) : 0 ≤ imagMagnitude x eps := Real.sqrt_nonneg _

theorem imagMagnitude_sq {x : ℝ} (hx : 0 ≤ x) (eps : ℝ) :
    imagMagnitude x eps ^ 2 = (rootModulus x eps + x) / 2 :=
  Real.sq_sqrt (div_nonneg (add_nonneg (rootModulus_nonneg x eps) hx) (by norm_num))

theorem imagMagnitude_ge_sqrt {x : ℝ} (hx : 0 ≤ x) (eps : ℝ) :
    Real.sqrt x ≤ imagMagnitude x eps := by
  have hb := imagMagnitude_sq hx eps
  have hs := rootModulus_ge_x hx eps
  have hxq := Real.sq_sqrt hx
  have hp := imagMagnitude_nonneg x eps
  have hxp := Real.sqrt_nonneg x
  nlinarith

theorem imagMagnitude_pos {x : ℝ} (hx : 0 < x) (eps : ℝ) : 0 < imagMagnitude x eps :=
  (Real.sqrt_pos.mpr hx).trans_le (imagMagnitude_ge_sqrt hx.le eps)

theorem realMagnitude_nonneg {x eps : ℝ} (hx : 0 < x) (heps : 0 ≤ eps) :
    0 ≤ realMagnitude x eps :=
  div_nonneg heps (mul_pos (by norm_num) (imagMagnitude_pos hx eps)).le

theorem realMagnitude_pos {x eps : ℝ} (hx : 0 < x) (heps : 0 < eps) :
    0 < realMagnitude x eps :=
  div_pos heps (mul_pos (by norm_num) (imagMagnitude_pos hx eps))

/-- The imaginary cross term is exactly the Stone epsilon. -/
theorem twice_real_mul_imag {x : ℝ} (hx : 0 < x) (eps : ℝ) :
    2 * realMagnitude x eps * imagMagnitude x eps = eps := by
  unfold realMagnitude
  field_simp [(imagMagnitude_pos hx eps).ne']
  <;> ring

/-- The real square difference is exactly the positive Stone x. -/
theorem realMagnitude_sq {x : ℝ} (hx : 0 < x) (eps : ℝ) :
    realMagnitude x eps ^ 2 = imagMagnitude x eps ^ 2 - x := by
  have hb := imagMagnitude_sq hx.le eps
  have hs := rootModulus_sq x eps
  have hr : rootModulus x eps = 2 * imagMagnitude x eps ^ 2 - x := by linarith only [hb]
  rw [hr] at hs
  have hid : 4 * imagMagnitude x eps ^ 2 * (imagMagnitude x eps ^ 2 - x) = eps ^ 2 := by
    nlinarith only [hs]
  have hcross := congrArg (fun y : ℝ => y ^ 2) (twice_real_mul_imag hx eps)
  have hmul : (4 * imagMagnitude x eps ^ 2) *
      (realMagnitude x eps ^ 2 - (imagMagnitude x eps ^ 2 - x)) = 0 := by
    nlinarith only [hid, hcross]
  have hne : 4 * imagMagnitude x eps ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (imagMagnitude_pos hx eps).ne')
  have hz := (mul_eq_zero.mp hmul).resolve_left hne
  linarith only [hz]

@[simp] theorem nuPlus_re (x eps : ℝ) : (nuPlus x eps).re = realMagnitude x eps := by
  simp [nuPlus]
@[simp] theorem nuMinus_re (x eps : ℝ) : (nuMinus x eps).re = realMagnitude x eps := by
  simp [nuMinus]
@[simp] theorem nuPlus_im (x eps : ℝ) : (nuPlus x eps).im = -imagMagnitude x eps := by
  simp [nuPlus]
@[simp] theorem nuMinus_im (x eps : ℝ) : (nuMinus x eps).im = imagMagnitude x eps := by
  simp [nuMinus]

theorem neg_nuPlus_sq {x : ℝ} (hx : 0 < x) (eps : ℝ) : -(nuPlus x eps) ^ 2 = zPlus x eps := by
  have hs := realMagnitude_sq hx eps
  have hc := twice_real_mul_imag hx eps
  apply Complex.ext <;> simp [nuPlus, zPlus, pow_two] <;> nlinarith only [hs, hc]

theorem neg_nuMinus_sq {x : ℝ} (hx : 0 < x) (eps : ℝ) : -(nuMinus x eps) ^ 2 = zMinus x eps := by
  have hs := realMagnitude_sq hx eps
  have hc := twice_real_mul_imag hx eps
  apply Complex.ext <;> simp [nuMinus, zMinus, pow_two] <;> nlinarith only [hs, hc]

theorem nuPlus_re_pos {x eps : ℝ} (hx : 0 < x) (heps : 0 < eps) : 0 < (nuPlus x eps).re := by
  simpa only [nuPlus_re] using realMagnitude_pos hx heps

theorem nuMinus_re_pos {x eps : ℝ} (hx : 0 < x) (heps : 0 < eps) : 0 < (nuMinus x eps).re := by
  simpa only [nuMinus_re] using realMagnitude_pos hx heps

/-- Uniform first-order control of the positive real part on x>=A>0. -/
theorem realMagnitude_le {A x eps : ℝ} (hA : 0 < A) (hx : A ≤ x) (heps : 0 ≤ eps) :
    realMagnitude x eps ≤ eps / (2 * Real.sqrt A) := by
  have hx0 : 0 < x := hA.trans_le hx
  have hb : Real.sqrt A ≤ imagMagnitude x eps :=
    (Real.sqrt_le_sqrt hx).trans (imagMagnitude_ge_sqrt hx0.le eps)
  apply div_le_div_of_nonneg_left heps (by positivity : 0 < 2 * Real.sqrt A)
  exact mul_le_mul_of_nonneg_left hb (by norm_num)

/-- The true O(eps²) imaginary-part error, uniform away from x=0. -/
theorem imagMagnitude_sub_sqrt_le {A x : ℝ} (hA : 0 < A) (hx : A ≤ x) (eps : ℝ) :
    0 ≤ imagMagnitude x eps - Real.sqrt x ∧
      imagMagnitude x eps - Real.sqrt x ≤ eps ^ 2 / (8 * A * Real.sqrt A) := by
  have hx0 : 0 < x := hA.trans_le hx
  have hdelta : 0 ≤ imagMagnitude x eps - Real.sqrt x :=
    sub_nonneg.mpr (imagMagnitude_ge_sqrt hx0.le eps)
  have hb := imagMagnitude_sq hx0.le eps
  have hs := rootModulus_sq x eps
  have hxq := Real.sq_sqrt hx0.le
  have hroot : 2 * x * (rootModulus x eps - x) ≤ eps ^ 2 := by
    nlinarith only [hs, sq_nonneg (rootModulus x eps - x)]
  have hbdelta : (2 * Real.sqrt x) * (imagMagnitude x eps - Real.sqrt x) ≤
      (rootModulus x eps - x) / 2 := by
    nlinarith only [hb, hxq, sq_nonneg (imagMagnitude x eps - Real.sqrt x)]
  have hm := mul_le_mul_of_nonneg_left hbdelta (show 0 ≤ 4 * x by positivity)
  have hlocal : (imagMagnitude x eps - Real.sqrt x) * (8 * x * Real.sqrt x) ≤ eps ^ 2 := by
    nlinarith only [hm, hroot]
  have hprod : A * Real.sqrt A ≤ x * Real.sqrt x :=
    mul_le_mul hx (Real.sqrt_le_sqrt hx) (Real.sqrt_nonneg A) hx0.le
  have hden := mul_le_mul_of_nonneg_left hprod (by norm_num : (0 : ℝ) ≤ 8)
  have hmul := mul_le_mul_of_nonneg_left hden hdelta
  refine ⟨hdelta, (le_div_iff₀ (by positivity : 0 < 8 * A * Real.sqrt A)).2 ?_⟩
  nlinarith only [hlocal, hmul]

/-- A compact imaginary-order bound for eps in[0,1]. -/
theorem imagMagnitude_le {B x eps : ℝ} (hx0 : 0 ≤ x) (hxB : x ≤ B)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1) :
    imagMagnitude x eps ≤ Real.sqrt (B + 1) := by
  have hs := rootModulus_sq x eps
  have hs0 := rootModulus_nonneg x eps
  have hsup : rootModulus x eps ≤ x + eps := by
    nlinarith [mul_nonneg hx0 heps0]
  apply Real.sqrt_le_sqrt
  linarith only [hsup, hxB, heps1]

/-- Quantitative common bound for both signed Stone root paths. -/
def pathErrorBound (A eps : ℝ) : ℝ :=
  eps / (2 * Real.sqrt A) + eps ^ 2 / (8 * A * Real.sqrt A)

theorem nuPlus_sub_boundary_norm_le {A x eps : ℝ}
    (hA : 0 < A) (hx : A ≤ x) (heps : 0 ≤ eps) :
    ‖nuPlus x eps - boundaryPlus x‖ ≤ pathErrorBound A eps := by
  have hx0 : 0 < x := hA.trans_le hx
  have ha := realMagnitude_nonneg hx0 heps
  have hd := (imagMagnitude_sub_sqrt_le hA hx eps).1
  have heq : nuPlus x eps - boundaryPlus x =
      (realMagnitude x eps : ℂ) - ((imagMagnitude x eps - Real.sqrt x : ℝ) : ℂ) * Complex.I := by
    simp only [nuPlus, boundaryPlus, Complex.ofReal_sub]
    ring
  rw [heq]
  calc
    _ ≤ ‖(realMagnitude x eps : ℂ)‖ +
        ‖((imagMagnitude x eps - Real.sqrt x : ℝ) : ℂ) * Complex.I‖ := norm_sub_le _ _
    _ = realMagnitude x eps + (imagMagnitude x eps - Real.sqrt x) := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hd]
    _ ≤ pathErrorBound A eps := add_le_add (realMagnitude_le hA hx heps)
      (imagMagnitude_sub_sqrt_le hA hx eps).2

theorem nuMinus_sub_boundary_norm_le {A x eps : ℝ}
    (hA : 0 < A) (hx : A ≤ x) (heps : 0 ≤ eps) :
    ‖nuMinus x eps - boundaryMinus x‖ ≤ pathErrorBound A eps := by
  have hx0 : 0 < x := hA.trans_le hx
  have ha := realMagnitude_nonneg hx0 heps
  have hd := (imagMagnitude_sub_sqrt_le hA hx eps).1
  have heq : nuMinus x eps - boundaryMinus x =
      (realMagnitude x eps : ℂ) + ((imagMagnitude x eps - Real.sqrt x : ℝ) : ℂ) * Complex.I := by
    simp only [nuMinus, boundaryMinus, Complex.ofReal_sub]
    ring
  rw [heq]
  calc
    _ ≤ ‖(realMagnitude x eps : ℂ)‖ +
        ‖((imagMagnitude x eps - Real.sqrt x : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = realMagnitude x eps + (imagMagnitude x eps - Real.sqrt x) := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hd]
    _ ≤ pathErrorBound A eps := add_le_add (realMagnitude_le hA hx heps)
      (imagMagnitude_sub_sqrt_le hA hx eps).2

end
end ImbalancedChen.Part3.ActualStoneSqrtPath20261025a


